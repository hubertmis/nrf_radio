//! Implementation of PPI based on legacy PPI peripheral from nRF52 series

use super::traits::{Allocator, Channel};
use crate::error::Error;
use core::ops::Deref;
use core::sync::atomic::{AtomicBool, Ordering};

// Copied from src/radio.rs and modified a little.
// This copy includes PpiPeriphWrapper
use nrf52840_hal::pac::ppi;
type PpiRegisterBlock = ppi::RegisterBlock;

struct PpiPeriphWrapper {
    ptr: *const PpiRegisterBlock,
}
impl PpiPeriphWrapper {
    pub fn new(ppi: &PpiRegisterBlock) -> Self {
        PpiPeriphWrapper { ptr: ppi }
    }
}
impl Deref for PpiPeriphWrapper {
    type Target = PpiRegisterBlock;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}
//unsafe impl Send for PpiPeriphWrapper {} // Is this really safe considering it's just pointer
// dereference?
unsafe impl Sync for PpiPeriphWrapper {} // Is this really safe considering it's just pointer
                                         // dereference?

const NUM_CHANNELS: usize = 20;

/// Allocator of PPI channels using the PPI peripheral available in the nRF52 family
pub struct PpiAllocator {
    periph: PpiPeriphWrapper,
    channels_availability: [AtomicBool; NUM_CHANNELS], // TODO: atomic bitmask
}

impl PpiAllocator {
    /// Create a new allocator
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::hw::ppi::legacy_ppi::PpiAllocator;
    /// use nrf52840_hal::pac::Peripherals;
    ///
    /// let peripherals = Peripherals::take().unwrap();
    ///
    /// let allocator = PpiAllocator::new(&peripherals.PPI);
    /// # }
    /// ```
    pub fn new(ppi: &PpiRegisterBlock) -> Self {
        Self {
            periph: PpiPeriphWrapper::new(ppi),
            channels_availability: array_init::array_init(|_| AtomicBool::new(true)),
        }
    }

    fn mark_channel_free(&self, id: usize) -> Result<(), Error> {
        // TODO: which Ordering?
        self.channels_availability[id]
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .map_or(Err(Error::InvalidArgument), |_| Ok(()))
    }
}

impl Allocator for PpiAllocator {
    fn allocate_channel(&'static self) -> Result<PpiChannel<'static>, Error> {
        for (id, channel_free) in self.channels_availability.iter().enumerate() {
            // TODO: which Ordering?
            if channel_free
                .compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                return Ok(PpiChannel::new(id.try_into().unwrap(), self));
            }
        }

        Err(Error::NoResources)
    }
}

/// Uses PPI peripheral channel to trigger tasks on hardware evetns
///
/// Uses PPI peripheral available in nRF52 series
pub struct PpiChannel<'ch> {
    id: u8,
    allocator: &'ch PpiAllocator,
}

impl<'ch> PpiChannel<'ch> {
    fn new(id: u8, allocator: &'ch PpiAllocator) -> Self {
        Self { id, allocator }
    }
}

impl Channel for PpiChannel<'_> {
    fn publish_by<T>(&self, event_reg: *const T) -> Result<(), Error> {
        // TODO: reading peripheral register takes a lot of time, how about a shadow variable in
        // RAM?
        if self.allocator.periph.ch[self.id as usize].eep.read().bits() == 0u32 {
            self.allocator.periph.ch[self.id as usize]
                .eep
                .write(|w| w.eep().variant(event_reg as u32));
            Ok(())
        } else {
            Err(Error::WouldBlock)
        }
    }

    fn stop_publishing_by<T>(&self, event_reg: *const T) -> Result<(), Error> {
        // TODO: reading peripheral register takes a lot of time, how about a shadow variable in
        // RAM?
        if self.allocator.periph.ch[self.id as usize].eep.read().bits() == event_reg as u32 {
            self.allocator.periph.ch[self.id as usize]
                .eep
                .write(|w| w.eep().variant(0u32));
            Ok(())
        } else {
            Err(Error::WouldBlock)
        }
    }

    fn subscribe_by<T>(&self, task_reg: *const T) -> Result<(), Error> {
        // TODO: reading peripheral register takes a lot of time, how about a shadow variable in
        // RAM?
        if self.allocator.periph.ch[self.id as usize].tep.read().bits() == 0u32 {
            self.allocator.periph.ch[self.id as usize]
                .tep
                .write(|w| w.tep().variant(task_reg as u32));
            Ok(())
        } else if self.allocator.periph.fork[self.id as usize]
            .tep
            .read()
            .bits()
            == 0u32
        {
            self.allocator.periph.fork[self.id as usize]
                .tep
                .write(|w| w.tep().variant(task_reg as u32));
            Ok(())
        } else {
            Err(Error::WouldBlock)
        }
    }

    fn stop_subscribing_by<T>(&self, task_reg: *const T) -> Result<(), Error> {
        // TODO: reading peripheral register takes a lot of time, how about a shadow variable in
        // RAM?
        if self.allocator.periph.ch[self.id as usize].tep.read().bits() == task_reg as u32 {
            self.allocator.periph.ch[self.id as usize]
                .tep
                .write(|w| w.tep().variant(0u32));
            Ok(())
        } else if self.allocator.periph.fork[self.id as usize]
            .tep
            .read()
            .bits()
            == task_reg as u32
        {
            self.allocator.periph.fork[self.id as usize]
                .tep
                .write(|w| w.tep().variant(0u32));
            Ok(())
        } else {
            Err(Error::WouldBlock)
        }
    }

    fn enable(&self) {
        self.allocator
            .periph
            .chenset
            .write(|w| unsafe { w.bits(1u32 << self.id) });
    }

    fn disable(&self) {
        self.allocator
            .periph
            .chenclr
            .write(|w| unsafe { w.bits(1u32 << self.id) });
    }
}

impl Drop for PpiChannel<'_> {
    fn drop(&mut self) {
        self.disable();

        self.allocator
            .mark_channel_free(self.id.into())
            .expect("PPI channel being freed is already free");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // PPI peripheral mock
    #[repr(align(4))]
    struct PpiMock {
        memory: [u8; 4096],
    }

    impl PpiMock {
        pub fn new() -> Self {
            Self { memory: [0; 4096] }
        }
    }

    impl Deref for PpiMock {
        type Target = PpiRegisterBlock;
        fn deref(&self) -> &Self::Target {
            let ptr: *const PpiRegisterBlock = self.memory.as_ptr() as *const _;
            unsafe { ptr.as_ref().unwrap() }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_allocate_all_channels() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;

        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let result = allocator.allocate_channel();
        assert!(result.is_err());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_reallocate_dropped_channels() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        for _ in 0..NUM_CHANNELS {
            let _channel = allocator.allocate_channel().unwrap();
            // Channel is dropped immediately
        }

        let result = allocator.allocate_channel();
        assert!(result.is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_enable_and_disable_channels() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.chenset.read().bits() & 1u32 << i, 0);
            channel.enable();
            assert_eq!(ppi_mock.chenset.read().bits() & 1u32 << i, 1u32 << i);
        }

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.chenclr.read().bits() & 1u32 << i, 0);
            channel.disable();
            assert_eq!(ppi_mock.chenclr.read().bits() & 1u32 << i, 1u32 << i);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_publish_to_channel_and_stop() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let publisher = 0u32;

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].eep.read().bits(), 0);
            let result = channel.publish_by(&publisher);
            assert_eq!(result, Ok(()));
            assert_eq!(
                ppi_mock.ch[i].eep.read().bits(),
                &publisher as *const _ as u32
            );
        }

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(
                ppi_mock.ch[i].eep.read().bits(),
                &publisher as *const _ as u32
            );
            let result = channel.stop_publishing_by(&publisher);
            assert_eq!(result, Ok(()));
            assert_eq!(ppi_mock.ch[i].eep.read().bits(), 0);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_subscribe_to_channel_and_stop() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let subscriber = 0u32;

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            let result = channel.subscribe_by(&subscriber);
            assert_eq!(result, Ok(()));
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
        }

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            let result = channel.stop_subscribing_by(&subscriber);
            assert_eq!(result, Ok(()));
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_publishing_to_single_channel_twice_fails() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let publisher = 0u32;
        let publisher2 = 1u32;

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].eep.read().bits(), 0);
            let result = channel.publish_by(&publisher);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].eep.read().bits(),
                &publisher as *const _ as u32
            );

            let result = channel.publish_by(&publisher2);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(
                ppi_mock.ch[i].eep.read().bits(),
                &publisher as *const _ as u32
            );

            let result = channel.publish_by(&publisher);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(
                ppi_mock.ch[i].eep.read().bits(),
                &publisher as *const _ as u32
            );
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stopping_publishing_to_channel_to_which_is_not_publishing_fails() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let publisher = 0u32;
        let publisher2 = 1u32;

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].eep.read().bits(), 0);
            let result = channel.stop_publishing_by(&publisher);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(ppi_mock.ch[i].eep.read().bits(), 0);

            let result = channel.publish_by(&publisher);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].eep.read().bits(),
                &publisher as *const _ as u32
            );

            let result = channel.stop_publishing_by(&publisher2);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(
                ppi_mock.ch[i].eep.read().bits(),
                &publisher as *const _ as u32
            );

            let result = channel.stop_publishing_by(&publisher);
            assert!(result.is_ok());
            assert_eq!(ppi_mock.ch[i].eep.read().bits(), 0);

            let result = channel.stop_publishing_by(&publisher);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(ppi_mock.ch[i].eep.read().bits(), 0);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_subscribing_from_single_channel_twice_is_ok() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let subscriber = 0u32;
        let subscriber2 = 1u32;

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber2);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(
                ppi_mock.fork[i].tep.read().bits(),
                &subscriber2 as *const _ as u32
            );
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_subscribing_from_single_channel_more_than_twice_fails() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let subscriber = 0u32;
        let subscriber2 = 1u32;
        let subscriber3 = 2u32;

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber2);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(
                ppi_mock.fork[i].tep.read().bits(),
                &subscriber2 as *const _ as u32
            );
        }

        for (i, channel) in channels.iter().enumerate() {
            let result = channel.subscribe_by(&subscriber3);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(
                ppi_mock.fork[i].tep.read().bits(),
                &subscriber2 as *const _ as u32
            );
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_subscribing_the_only_subscriber_is_ok() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let subscriber = 0u32;

        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);
        }

        for (i, channel) in channels.iter().enumerate() {
            let result = channel.stop_subscribing_by(&subscriber);
            assert_eq!(result, Ok(()));
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_subscribing_both_subscribers_in_any_order_is_ok() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let subscriber = 0u32;
        let subscriber2 = 1u32;

        // Subscribe both
        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber2);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(
                ppi_mock.fork[i].tep.read().bits(),
                &subscriber2 as *const _ as u32
            );
        }

        // Unsubscribe starting with first
        for (i, channel) in channels.iter().enumerate() {
            let result = channel.stop_subscribing_by(&subscriber);
            assert_eq!(result, Ok(()));
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(
                ppi_mock.fork[i].tep.read().bits(),
                &subscriber2 as *const _ as u32
            );

            let result = channel.stop_subscribing_by(&subscriber2);
            assert_eq!(result, Ok(()));
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);
        }

        // Subscribe both again
        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber2);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(
                ppi_mock.fork[i].tep.read().bits(),
                &subscriber2 as *const _ as u32
            );
        }

        // Unsubscribe starting with last
        for (i, channel) in channels.iter().enumerate() {
            let result = channel.stop_subscribing_by(&subscriber2);
            assert_eq!(result, Ok(()));
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.stop_subscribing_by(&subscriber);
            assert_eq!(result, Ok(()));
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_subscribing_by_unsubscribed_fails() {
        let ppi_mock = PpiMock::new();

        static mut ALLOCATOR: Option<PpiAllocator> = None;
        let allocator: &'static PpiAllocator;
        unsafe {
            ALLOCATOR = Some(PpiAllocator::new(&ppi_mock));
            allocator = ALLOCATOR.as_ref().unwrap();
        }

        let mut channels = Vec::new();

        for _ in 0..NUM_CHANNELS {
            channels.push(allocator.allocate_channel().unwrap());
        }

        let subscriber = 0u32;
        let subscriber2 = 1u32;
        let subscriber3 = 0u32;

        // Subscribe two
        for (i, channel) in channels.iter().enumerate() {
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.subscribe_by(&subscriber2);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(
                ppi_mock.fork[i].tep.read().bits(),
                &subscriber2 as *const _ as u32
            );
        }

        // Unsubscribe 3rd
        for (i, channel) in channels.iter().enumerate() {
            let result = channel.stop_subscribing_by(&subscriber3);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(
                ppi_mock.fork[i].tep.read().bits(),
                &subscriber2 as *const _ as u32
            );
        }

        // Unsubscribe 2nd
        for (i, channel) in channels.iter().enumerate() {
            let result = channel.stop_subscribing_by(&subscriber2);
            assert!(result.is_ok());
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);
        }

        // Try unsubscribing 3rd and 2nd
        for (i, channel) in channels.iter().enumerate() {
            let result = channel.stop_subscribing_by(&subscriber3);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.stop_subscribing_by(&subscriber2);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(
                ppi_mock.ch[i].tep.read().bits(),
                &subscriber as *const _ as u32
            );
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);
        }

        // Unsubscribe 1st
        for (i, channel) in channels.iter().enumerate() {
            let result = channel.stop_subscribing_by(&subscriber);
            assert!(result.is_ok());
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);
        }

        // Try unsubscribing 1st, 2nd, and 3rd
        for (i, channel) in channels.iter().enumerate() {
            let result = channel.stop_subscribing_by(&subscriber);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.stop_subscribing_by(&subscriber2);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);

            let result = channel.stop_subscribing_by(&subscriber3);
            assert_eq!(result, Err(Error::WouldBlock));
            assert_eq!(ppi_mock.ch[i].tep.read().bits(), 0);
            assert_eq!(ppi_mock.fork[i].tep.read().bits(), 0);
        }
    }
}
