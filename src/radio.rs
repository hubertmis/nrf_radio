use crate::error::Error;
use crate::hw::ppi::{self, traits::Channel};
use crate::mutex::Mutex;
use core::any::Any;
use core::ops::Deref;

use crate::frm_mem_mng::frame_buffer::FrameBuffer;

// Port to nRF52840
use nrf52840_hal::pac::radio;
type RadioRegisterBlock = radio::RegisterBlock;

//// Radio Periph Wrapper
//// It is a structure allowing testability of the Phy structure. It allows overriding
//// RADIO peripheral memory space with arbitrary selected memory space (like an array)
//// in unit tests running on a host PC.
unsafe impl Send for RadioPeriphWrapper {} // Is this really safe considering it's just pointer
                                           // dereference?
struct RadioPeriphWrapper {
    ptr: *const RadioRegisterBlock,
}
impl RadioPeriphWrapper {
    pub fn new(radio: &RadioRegisterBlock) -> Self {
        RadioPeriphWrapper { ptr: radio }
    }
}
impl Deref for RadioPeriphWrapper {
    type Target = RadioRegisterBlock;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}

// TODO: shorter lifetime than static. Is it possible?
//       Maybe it requires FSM refactoring to change FSM type on the fly?
/// Reference to any data selected by a requester
///
/// The same reference is passed in a callback function when the requested operation is completed.
pub type Context = &'static (dyn Any + Send + Sync);

/// Type of the callback function called when the requested TX operation is completed
pub type TxCallback = fn(Result<(), Error>, Context);

/// Internal data required in the TX state
struct TxData {
    callback: TxCallback,
    context: Context,
}

/// Data and metadata of the correctly received frame
#[derive(Debug, PartialEq)]
pub struct RxOk {
    /// Reference to the content of the received frame
    ///
    /// For IEEE 802.15.4 this buffer contains PHR and PSDU of the received frame, where MFR might
    /// be malformed
    pub frame: FrameBuffer<'static>,
}

/// Type of the callback function called when the requested RX operation is completed
pub type RxCallback = fn(Result<RxOk, Error>, Context, &mut RxResources);

/// Resrouces being returned to the caller in RxCallback function
pub struct RxResources {
    start_ppi_channel: Option<ppi::Channel>,
    phyend_ppi_channel: Option<ppi::Channel>,
}

impl RxResources {
    /// Get PPI channel borrowed to trigger RXEN task
    pub fn start_channel(&mut self) -> Option<ppi::Channel> {
        self.start_ppi_channel.take()
    }

    /// Get PPI channel borrowed to be triggered at the PHYEND event
    pub fn phyend_ppi_channel(&mut self) -> Option<ppi::Channel> {
        self.phyend_ppi_channel.take()
    }
}

enum OperationStartType {
    Now,
    AtEvent(ppi::Channel),
}

struct RxFsmModifiers {
    start_type: Option<OperationStartType>,
    phyend_ppi_channel: Option<ppi::Channel>,
}

/// Defines RX operation to be requested
///
/// User-friendly interface to flexibly select optional features of RX operation. In the simplest
/// usage only the arguments mandatory for each RX operation are passed. In more complex scenarios
/// optional methods can be chained to enable more sophisticated RX features
///
/// # Example
///
/// ```no_run
/// # #[macro_use] extern crate nrf_radio;
/// # missing_test_fns!();
/// # fn main() {
/// use nrf_radio::error::Error;
/// use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator;
/// use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
/// use nrf_radio::radio::{Context, RxOk, RxRequest, RxResources};
///
/// fn rx_callback(result: Result<RxOk, Error>, context: Context, resources: &mut RxResources) {
///   // Do something with the RX operation result
/// }
///
/// let buffer_allocator = SingleFrameAllocator::new();
/// let request = RxRequest::new(buffer_allocator.get_frame().unwrap(),
///                              rx_callback,
///                              &None::<usize>)
///                          .now();
/// # }
/// ```
pub struct RxRequest {
    buffer: FrameBuffer<'static>,
    callback: RxCallback,
    context: Context,
    fsm_mod: RxFsmModifiers,
}

impl RxRequest {
    /// Creates RX operation request with mandatory data
    ///
    /// After a frame is received the `callback` function is called from an ISR context. The
    /// `result` parameter of the `callback` function is [`Ok(RxOk)`](RxOk) if the received frame
    /// is valid. Alternatively it is [`Err(Error)`](Error) if the received frame is invalid.
    /// The `context` argument is blindly copied to the `callback` function as its `context`
    /// parameter. The caller can use `context` to match callbacks with reception requests.
    /// The `resources` argument returns resources that were borrowed to the `Phy` module to
    /// proceed with the requested RX operation.
    ///
    /// When the callback is called the receiver is not enabled anymore.
    ///
    /// The `buffer` is returned to the caller through `callback` when received a valid frame.
    /// The `buffer` is dropped on any error.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::error::Error;
    /// use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator;
    /// use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
    /// use nrf_radio::radio::{Context, RxOk, RxRequest, RxResources};
    ///
    /// fn rx_callback(result: Result<RxOk, Error>, context: Context, resources: &mut RxResources) {
    ///   // Do something with the RX operation result
    /// }
    ///
    /// let buffer_allocator = SingleFrameAllocator::new();
    /// let initial_request = RxRequest::new(buffer_allocator.get_frame().unwrap(),
    ///                                      rx_callback,
    ///                                      &None::<usize>);
    /// # }
    /// ```
    pub fn new(buffer: FrameBuffer<'static>, callback: RxCallback, context: Context) -> Self {
        Self {
            buffer,
            callback,
            context,
            fsm_mod: RxFsmModifiers {
                start_type: None,
                phyend_ppi_channel: None,
            },
        }
    }

    /// Publishes to given PPI channel on the PHYEND event
    ///
    /// When received frame generates a PHYEND event in the RADIO peripheral, the peripheral
    /// publishes to passed PPI channel. This feature can be used to capture timestamp of the
    /// received frame.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::error::Error;
    /// use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator;
    /// use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
    /// use nrf_radio::hw::ppi::{self, traits::Allocator};
    /// use nrf_radio::radio::{Context, RxOk, RxRequest, RxResources};
    ///
    /// use nrf52840_hal::pac::Peripherals;
    ///
    /// fn rx_callback(result: Result<RxOk, Error>, context: Context, resources: &mut RxResources) {
    ///   // Do something with the RX operation result
    /// }
    ///
    /// // Allocate frame buffer
    /// let buffer_allocator = SingleFrameAllocator::new();
    /// let frame_buffer = buffer_allocator.get_frame().unwrap();
    ///
    /// // Allocate PPI channel
    /// let peripherals = Peripherals::take().unwrap();
    /// let ppi_allocator;
    ///
    /// static mut PPI_ALLOCATOR: Option<ppi::Allocator> = None;
    /// unsafe {
    ///   PPI_ALLOCATOR = Some(ppi::Allocator::new(&peripherals.PPI));
    ///   ppi_allocator = PPI_ALLOCATOR.as_ref().unwrap();
    /// }
    ///
    /// let ppi_channel = ppi_allocator.allocate_channel().unwrap();
    ///
    /// let complete_request = RxRequest::new(frame_buffer, rx_callback, &None::<usize>)
    ///                                   .with_ppi_channel_on_phyend(ppi_channel);
    /// # }
    /// ```
    pub fn with_ppi_channel_on_phyend(mut self, ppi_channel: ppi::Channel) -> Self {
        self.fsm_mod.phyend_ppi_channel = Some(ppi_channel);
        self
    }

    /// Marks passed request to be started when passed ppi channel is triggered
    ///
    /// RX request may be started as soon as possible (now), or it might be deferred to be started
    /// by a hardware event (potentially using a hardware task). This function selects that passed
    /// request is to be started at a hardware event.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::error::Error;
    /// use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator;
    /// use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
    /// use nrf_radio::hw::ppi::{self, traits::Allocator};
    /// use nrf_radio::radio::{Context, RxOk, RxRequest, RxResources};
    /// use nrf52840_hal::pac::Peripherals;
    ///
    /// fn rx_callback(result: Result<RxOk, Error>, context: Context, resources: &mut RxResources) {
    ///   // Do something with the RX operation result
    /// }
    ///
    /// // Allocate frame buffer
    /// let buffer_allocator = SingleFrameAllocator::new();
    /// let frame_buffer = buffer_allocator.get_frame().unwrap();
    ///
    /// // Allocate PPI channel
    /// let peripherals = Peripherals::take().unwrap();
    /// let ppi_allocator;
    ///
    /// static mut PPI_ALLOCATOR: Option<ppi::Allocator> = None;
    /// unsafe {
    ///   PPI_ALLOCATOR = Some(ppi::Allocator::new(&peripherals.PPI));
    ///   ppi_allocator = PPI_ALLOCATOR.as_ref().unwrap();
    /// }
    ///
    /// let ppi_channel = ppi_allocator.allocate_channel().unwrap();
    ///
    /// let complete_request = RxRequest::new(buffer_allocator.get_frame().unwrap(),
    ///                                       rx_callback,
    ///                                       &None::<usize>)
    ///                                   .at_event(ppi_channel);
    /// # }
    /// ```
    pub fn at_event(mut self, ppi_channel: ppi::Channel) -> Self {
        debug_assert!(self.fsm_mod.start_type.is_none());
        self.fsm_mod.start_type = Some(OperationStartType::AtEvent(ppi_channel));
        self
    }

    /// Marks passed request to be started now
    ///
    /// RX request may be started as soon as possible (now), or it might be deferred to be started
    /// by a hardware event (potentially using a hardware task). This function select that passed
    /// request is to be started now.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::error::Error;
    /// use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator;
    /// use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
    /// use nrf_radio::radio::{Context, RxOk, RxRequest, RxResources};
    ///
    /// fn rx_callback(result: Result<RxOk, Error>, context: Context, resources: &mut RxResources) {
    ///   // Do something with the RX operation result
    /// }
    ///
    /// let buffer_allocator = SingleFrameAllocator::new();
    /// let complete_request = RxRequest::new(buffer_allocator.get_frame().unwrap(),
    ///                                       rx_callback,
    ///                                       &None::<usize>)
    ///                                   .now();
    /// # }
    /// ```
    pub fn now(mut self) -> Self {
        debug_assert!(self.fsm_mod.start_type.is_none());
        self.fsm_mod.start_type = Some(OperationStartType::Now);
        self
    }
}

/// Internal data required in the RX state
struct RxData {
    request: RxRequest,
}

/// The state of the software PHY FSM
enum State {
    // In Idle state RADIO is being disabled (RXDISABLE, TXDISABLE) or already disabled (DISABLED).
    // The INTEN register is cleared. The SHORTS, PACKETPTR, EVENTS_ are undefined (expected to be
    // overriden when entering the next state).
    Idle,
    Tx(TxData),
    Rx(RxData),
}

/// Data accessible by an ISR
struct IsrData {
    radio: RadioPeriphWrapper,
    state: State,
}

// There is only one ISR_DATA instance, because there is only one ISR handler. This instance should
// be multiplied (an array) if there were more peripheral instances (implying more ISRs) to handle.
static ISR_DATA: Mutex<Option<IsrData>> = Mutex::new(None);

/// Macro used to build tests on a host
///
/// It is used for unit tests and doctest targets
#[doc(hidden)]
#[macro_export]
macro_rules! missing_test_fns {
    () => {
        #[no_mangle]
        pub extern "C" fn __primask_r() -> u32 {
            0
        }

        #[no_mangle]
        pub extern "C" fn __cpsie() {}

        #[no_mangle]
        pub extern "C" fn __cpsid() {}
    };
}

/// Radio physical layer representation
///
/// # Examples
///
/// ```no_run
/// # #[macro_use] extern crate nrf_radio;
/// # missing_test_fns!();
/// # fn main() {
///   use nrf52840_hal::pac::Peripherals;
///   use nrf_radio::radio::Phy;
///
///   let peripherals = Peripherals::take().unwrap();
///   let phy = Phy::new(&peripherals.RADIO);
///   phy.configure_802154();
/// # }
/// ```
pub struct Phy {
    isr_data: &'static Mutex<Option<IsrData>>,
}

impl Phy {
    /// Reset module
    ///
    /// This function is intended to be used between unit tests
    #[doc(hidden)]
    pub fn reset() {
        crate::crit_sect::locked(|cs| {
            *ISR_DATA.borrow_mut(cs) = None;
        });
    }

    /// Create new instance of the physical layer
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    ///   use nrf52840_hal::pac::Peripherals;
    ///   use nrf_radio::radio::Phy;
    ///
    ///   let peripherals = Peripherals::take().unwrap();
    ///
    ///   let phy = Phy::new(&peripherals.RADIO);
    /// # }
    /// ```
    // TODO: Should I take mutable reference to the register block, to own it exclusively? With
    // a lifetime bound to the created instance?
    pub fn new(radio: &RadioRegisterBlock) -> Self {
        let isr_data = IsrData {
            radio: RadioPeriphWrapper::new(radio),
            state: State::Idle,
        };

        crate::crit_sect::locked(|cs| {
            let prev_isr_data = ISR_DATA.borrow_mut(cs).replace(isr_data);
            assert!(prev_isr_data.is_none());
        });

        Self {
            isr_data: &ISR_DATA,
        }
    }

    /// Helper function to get access to data accessible from ISR
    fn use_isr_data<F, R>(&self, func: F) -> R
    where
        F: FnOnce(&mut IsrData) -> R,
    {
        crate::crit_sect::locked(|cs| {
            let isr_data_option = &mut self.isr_data.borrow_mut(cs);
            let isr_data = &mut isr_data_option.as_mut().unwrap();
            func(isr_data)
        })
    }

    /// Configure physical layer for IEEE 802.15.4 protocol
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    ///   use nrf52840_hal::pac::Peripherals;
    ///   use nrf_radio::radio::Phy;
    ///
    ///   let peripherals = Peripherals::take().unwrap();
    ///   let phy = Phy::new(&peripherals.RADIO);
    ///   phy.configure_802154();
    /// # }
    /// ```
    pub fn configure_802154(&self) {
        self.use_isr_data(|i| {
            i.radio
                .mode
                .write(|w| w.mode().variant(radio::mode::MODE_A::IEEE802154_250KBIT));
            i.radio.pcnf0.write(|w| {
                w.lflen()
                    .variant(8)
                    .plen()
                    .variant(radio::pcnf0::PLEN_A::_32BIT_ZERO)
                    .crcinc()
                    .variant(radio::pcnf0::CRCINC_A::INCLUDE)
            });
            i.radio.pcnf1.write(|w| w.maxlen().variant(127)); // TODO: remove magic numbers
            i.radio
                .modecnf0
                .write(|w| w.ru().variant(radio::modecnf0::RU_A::FAST));
            i.radio.crccnf.write(|w| {
                w.len()
                    .variant(radio::crccnf::LEN_A::TWO)
                    .skipaddr()
                    .variant(radio::crccnf::SKIPADDR_A::IEEE802154)
            });
            i.radio.crcpoly.write(|w| w.crcpoly().variant(0x011021)); // TODO: remove magic numbers

            // TODO: move CCA configuration out
            i.radio.ccactrl.write(|w| {
                w.ccamode()
                    .variant(radio::ccactrl::CCAMODE_A::ED_MODE)
                    .ccaedthres()
                    .variant(20)
            });
        });

        // TODO: enable IRQs?
        //       or perhaps separated function to enable irqs?
    }

    fn get_802154_frequency_from_channel(channel: u8) -> Result<u16, Error> {
        if (11..=26).contains(&channel) {
            Ok(2405u16 + (channel - 11) as u16 * 5)
        } else {
            Err(Error::InvalidChannel)
        }
    }

    /// Sets channel (radio frequency)
    ///
    /// The channel number depends on configured Phy mode. Currently only IEEE 802.15.4 is
    /// supported with channels from range 11-26.
    ///
    /// Returns:
    /// * [`Ok(())`](core::result::Result::Ok) if channel is configured successfully
    /// * [`Err(Error::WouldBlock)`](Error::WouldBlock) if the transceiver is enabled
    /// * [`Err(Error::InvalidChannel)`](Error::InvalidChannel) if the requested channel is out of
    /// range for enabled radio protocol
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// use core::any::Any;
    /// use nrf52840_hal::pac::Peripherals;
    /// use nrf_radio::radio::Phy;
    ///
    /// fn main() {
    ///   let peripherals = Peripherals::take().unwrap();
    ///   let phy = Phy::new(&peripherals.RADIO);
    ///   phy.configure_802154();
    ///
    ///   let result = phy.set_channel(11);
    ///   assert_eq!(result, Ok(()));
    /// }
    /// ```
    pub fn set_channel(&self, channel: u8) -> Result<(), Error> {
        self.use_isr_data(|i| match &i.state {
            State::Idle => {
                let frequency = (Phy::get_802154_frequency_from_channel(channel)? - 2400)
                    .try_into()
                    .unwrap();
                i.radio
                    .frequency
                    .write(|w| w.frequency().variant(frequency));
                Ok(())
            }
            _ => Err(Error::WouldBlock),
        })
    }

    /// Helper function to set PACKETPTR register to point to passed buffer
    fn set_packetptr(buffer: &[u8], i: &mut IsrData) {
        i.radio
            .packetptr
            .write(|w| w.packetptr().variant(buffer.as_ptr() as u32));
    }

    /// FSM procedure on entering TX state
    fn enter_tx(frame: &[u8], i: &mut IsrData) {
        Phy::set_packetptr(frame, i);
        i.radio
            .shorts
            .write(|w| w.txready_start().set_bit().phyend_disable().set_bit());
        i.radio
            .events_phyend
            .write(|w| w.events_phyend().clear_bit());
        i.radio.tasks_txen.write(|w| w.tasks_txen().set_bit());
        i.radio.intenset.write(|w| w.phyend().set_bit());
    }

    /// FSM procedure on exitting TX state
    fn exit_tx(i: &mut IsrData) {
        i.radio.intenclr.write(|w| w.phyend().set_bit());
    }

    /// Transmits a frame
    ///
    /// Transmits the content of `frame` using radio protocol configured for this [`Phy`] instance.
    /// For IEEE 802.15.4 `frame` must include PHR and PSDU. Other protocols are not supported yet.
    ///
    /// Returns [`Ok(())`](core::result::Result::Ok) if the transmission request was accepted. If
    /// the request was not accepted returns [`Err(Error)`](Error).
    ///
    /// After the accepted transmission request is completed the `callback` function is called from
    /// an ISR context. The parameters of the `callback` function are `result` indicating if the
    /// requested transmission was successful, and `context` being any reference provided by the
    /// caller. The caller might use `context` to match callbacks with transmission requests.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// use core::any::Any;
    /// use nrf52840_hal::pac::Peripherals;
    /// use nrf_radio::radio::Phy;
    /// use nrf_radio::error::Error;
    ///
    /// fn tx_callback(result: Result<(), Error>, context: &'static (dyn Any + Send + Sync)) {
    ///   println!("Packet tx procedure finished");
    /// }
    ///
    /// fn main() {
    ///   let peripherals = Peripherals::take().unwrap();
    ///   let phy = Phy::new(&peripherals.RADIO);
    ///   phy.configure_802154();
    ///
    ///   let frame: [u8; 17] = [16, 0x41, 0x98, 0xaa, 0xcd, 0xab, 0xff, 0xff, 0x34, 0x12,
    ///                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];
    ///   let result = phy.tx(&frame, tx_callback, &None::<u8>);
    ///   assert_eq!(result, Ok(()));
    /// }
    /// ```
    pub fn tx(&self, frame: &[u8], callback: TxCallback, context: Context) -> Result<(), Error> {
        // FSM:
        // | idle |  <----> | tx |
        self.use_isr_data(|i| match &i.state {
            State::Idle => {
                i.state = State::Tx(TxData { callback, context });
                Phy::enter_tx(frame, i);
                Ok(())
            }
            _ => Err(Error::WouldBlock),
        })
    }

    /// FSM procedure on entering RX state
    fn enter_rx(buffer: &[u8], fsm_mod: &RxFsmModifiers, i: &mut IsrData) -> Result<(), Error> {
        if fsm_mod.start_type.is_none() {
            return Err(Error::InvalidArgument);
        }

        Phy::set_packetptr(buffer, i);
        i.radio
            .shorts
            .write(|w| w.rxready_start().set_bit().end_disable().set_bit());
        i.radio.events_crcok.write(|w| w.events_crcok().clear_bit());
        i.radio
            .events_crcerror
            .write(|w| w.events_crcerror().clear_bit());

        if let Some(phyend_ch) = &fsm_mod.phyend_ppi_channel {
            let result = phyend_ch.publish_by(&i.radio.events_phyend as *const _);
            debug_assert!(result.is_ok());
        }

        match &fsm_mod.start_type {
            Some(OperationStartType::Now) => i.radio.tasks_rxen.write(|w| w.tasks_rxen().set_bit()),
            Some(OperationStartType::AtEvent(ppi_ch)) => ppi_ch
                .subscribe_by(&i.radio.tasks_rxen as *const _)
                .unwrap(),
            None => panic!("Checked that start_type is Some() while validating arguemtns"),
        }

        i.radio
            .intenset
            .write(|w| w.crcok().set_bit().crcerror().set_bit());

        Ok(())
    }

    /// FSM procedure on exitting RX state
    fn exit_rx(fsm_mod: &RxFsmModifiers, i: &mut IsrData) {
        if let Some(phyend_ch) = &fsm_mod.phyend_ppi_channel {
            let result = phyend_ch.stop_publishing_by(&i.radio.events_phyend as *const _);
            debug_assert!(result.is_ok());
        }

        if let Some(OperationStartType::AtEvent(start_ch)) = &fsm_mod.start_type {
            let result = start_ch.stop_subscribing_by(&i.radio.tasks_rxen as *const _);
            debug_assert!(result.is_ok());
        }

        i.radio
            .intenclr
            .write(|w| w.crcok().set_bit().crcerror().set_bit());
    }

    /// Enables receiver
    ///
    /// The receiver is enabled until a frame is received.
    ///
    /// Returns [`Ok(())`](core::result::Result::Ok) if the request was accepted. If the request
    /// was not accepted returns [`Err(Error)`](Error).
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// use nrf52840_hal::pac::Peripherals;
    /// use nrf_radio::radio::{Phy, RxOk, RxRequest, Context, RxResources};
    /// use nrf_radio::error::Error;
    /// use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator;
    /// use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
    /// use nrf_radio::hw::ppi;
    ///
    /// fn rx_callback(result: Result<RxOk, Error>,
    ///                context: Context,
    ///                returned_resources: &mut RxResources)
    /// {
    ///   match result {
    ///     Ok(rx_ok) => {
    ///       println!("Received frame: {:x?}", rx_ok.frame);
    ///     }
    ///     Err(error) => {
    ///       println!("Received invalid frame because of {:?}", error);
    ///     }
    ///   }
    /// }
    ///
    /// fn main() {
    ///   let buffer_allocator = SingleFrameAllocator::new();
    ///
    ///   let peripherals = Peripherals::take().unwrap();
    ///   let phy = Phy::new(&peripherals.RADIO);
    ///   phy.configure_802154();
    ///
    ///   let result = phy.rx(
    ///         RxRequest::new(
    ///                 buffer_allocator.get_frame().unwrap(),
    ///                 rx_callback,
    ///                 &None::<usize>)
    ///             .now());
    ///   assert_eq!(result, Ok(()));
    /// }
    /// ```
    pub fn rx(&self, request: RxRequest) -> Result<(), Error> {
        if request.buffer.len() <= 127 {
            // TODO: remove magic number
            return Err(Error::TooSmallBuffer);
        }

        self.use_isr_data(|i| match &i.state {
            State::Idle => {
                Phy::enter_rx(&request.buffer, &request.fsm_mod, i)?;
                i.state = State::Rx(RxData { request });
                Ok(())
            }
            _ => Err(Error::WouldBlock),
        })
    }
}

// TODO: remove when extenral IRQ managing library is used
use nrf52840_hal::pac::interrupt;
#[interrupt]
fn RADIO() {
    irq_handler();
}

fn irq_handler() {
    enum Callback {
        None,
        Tx(TxCallback, Context),
        Rx(RxCallback, Context, Result<RxOk, Error>, RxResources),
    }

    let mut callback = Callback::None;

    crate::crit_sect::locked(|cs| {
        let mut i = ISR_DATA.borrow_mut(cs).take().unwrap();

        match i.state {
            State::Rx(mut rx_data) => {
                let resources = RxResources {
                    phyend_ppi_channel: None,
                    start_ppi_channel: None,
                };

                if i.radio.events_crcok.read().events_crcok().bit_is_set() {
                    i.radio.events_crcok.write(|w| w.events_crcok().clear_bit());

                    callback = Callback::Rx(
                        rx_data.request.callback,
                        rx_data.request.context,
                        Ok(RxOk {
                            frame: rx_data.request.buffer,
                        }),
                        resources,
                    );
                } else if i
                    .radio
                    .events_crcerror
                    .read()
                    .events_crcerror()
                    .bit_is_set()
                {
                    i.radio
                        .events_crcerror
                        .write(|w| w.events_crcerror().clear_bit());

                    callback = Callback::Rx(
                        rx_data.request.callback,
                        rx_data.request.context,
                        Err(Error::IncorrectCrc),
                        resources,
                    );
                } else {
                    panic!("Unexpected event received in Rx state");
                }

                i.state = State::Idle;
                Phy::exit_rx(&rx_data.request.fsm_mod, &mut i);

                if let Callback::Rx(_, _, _, ref mut resources) = callback {
                    if let Some(OperationStartType::AtEvent(start_ch)) =
                        rx_data.request.fsm_mod.start_type
                    {
                        resources.start_ppi_channel = Some(start_ch);
                    }

                    resources.phyend_ppi_channel =
                        rx_data.request.fsm_mod.phyend_ppi_channel.take();
                }
            }

            State::Tx(tx_data) => {
                if i.radio.events_phyend.read().events_phyend().bit_is_set() {
                    i.radio
                        .events_phyend
                        .write(|w| w.events_phyend().clear_bit());

                    callback = Callback::Tx(tx_data.callback, tx_data.context);
                } else {
                    panic!("Unexpected event received in Tx state");
                }

                i.state = State::Idle;
                Phy::exit_tx(&mut i);
            }

            State::Idle => panic!("An event received in Idle state"),
        }

        let temp_i = ISR_DATA.borrow_mut(cs).replace(i);
        debug_assert!(temp_i.is_none());
    });

    match callback {
        Callback::None => (),
        Callback::Rx(callback, context, result, mut resources) => {
            callback(result, context, &mut resources)
        }
        Callback::Tx(callback, context) => callback(Ok(()), context),
    };
}

#[cfg(test)]
missing_test_fns!();

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hw::ppi::traits::MockChannel;
    use serial_test::serial;

    // RADIO peripheral mock
    #[repr(align(4))]
    struct RadioMock {
        memory: [u8; 4096],
    }

    impl RadioMock {
        pub fn new() -> Self {
            Self { memory: [0; 4096] }
        }
    }

    impl Deref for RadioMock {
        type Target = RadioRegisterBlock;
        fn deref(&self) -> &Self::Target {
            let ptr: *const RadioRegisterBlock = self.memory.as_ptr() as *const _;
            unsafe { ptr.as_ref().unwrap() }
        }
    }

    fn create_frame_buffer_from_static_buffer(static_buffer: &'static mut [u8]) -> FrameBuffer {
        FrameBuffer::new(static_buffer, None, &None::<usize>)
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_configuring_802154() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        assert_eq!(
            radio_mock.mode.read().mode().variant().unwrap(),
            radio::mode::MODE_A::IEEE802154_250KBIT
        );
        assert_eq!(radio_mock.pcnf0.read().lflen().bits(), 8);
        assert_eq!(radio_mock.pcnf0.read().s0len().bit(), false);
        assert_eq!(radio_mock.pcnf0.read().s1len().bits(), 0);
        assert_eq!(radio_mock.pcnf0.read().cilen().bits(), 0);
        assert_eq!(
            radio_mock.pcnf0.read().plen().variant(),
            radio::pcnf0::PLEN_A::_32BIT_ZERO
        );
        assert_eq!(
            radio_mock.pcnf0.read().crcinc().variant(),
            radio::pcnf0::CRCINC_A::INCLUDE
        );
        assert_eq!(radio_mock.pcnf0.read().termlen().bits(), 0);
        assert_eq!(radio_mock.pcnf1.read().maxlen().bits(), 127);
        assert_eq!(radio_mock.pcnf1.read().statlen().bits(), 0);
        assert_eq!(radio_mock.pcnf1.read().balen().bits(), 0);
        assert_eq!(
            radio_mock.pcnf1.read().endian().variant(),
            radio::pcnf1::ENDIAN_A::LITTLE
        );
        assert_eq!(
            radio_mock.pcnf1.read().whiteen().variant(),
            radio::pcnf1::WHITEEN_A::DISABLED
        );
        assert_eq!(
            radio_mock.modecnf0.read().ru().variant(),
            radio::modecnf0::RU_A::FAST
        );
        assert_eq!(
            radio_mock.modecnf0.read().dtx().variant().unwrap(),
            radio::modecnf0::DTX_A::CENTER
        );
        assert_eq!(
            radio_mock.crccnf.read().len().variant(),
            radio::crccnf::LEN_A::TWO
        );
        assert_eq!(
            radio_mock.crccnf.read().skipaddr().variant().unwrap(),
            radio::crccnf::SKIPADDR_A::IEEE802154
        );
        assert_eq!(radio_mock.crcpoly.read().crcpoly().bits(), 0x011021);
        assert_eq!(radio_mock.crcinit.read().crcinit().bits(), 0);
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_tx() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);

        let frame: [u8; 17] = [
            16, 0x41, 0x98, 0xaa, 0xcd, 0xab, 0xff, 0xff, 0x34, 0x12, 0x01, 0x02, 0x03, 0x04, 0x05,
            0x06, 0x07,
        ];

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Result<(), Error> = Err(Error::IncorrectCrc);
        static mut RECEIVED_CONTEXT: &Option<u8> = &Some(0);

        fn callback(result: Result<(), Error>, context: Context) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = result };
            unsafe { RECEIVED_CONTEXT = context.downcast_ref().unwrap() };
        }

        phy.configure_802154();
        let result = phy.tx(&frame, callback, &None::<u8>);

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Check peripheral configuration before IRQ
        assert_eq!(radio_mock.packetptr.read().bits(), frame.as_ptr() as u32);
        assert!(radio_mock.shorts.read().txready_start().bit_is_set());
        assert!(radio_mock.shorts.read().phyend_disable().bit_is_set());
        assert!(radio_mock
            .events_phyend
            .read()
            .events_phyend()
            .bit_is_clear());
        assert!(radio_mock.intenset.read().phyend().bit_is_set());

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_phyend
            .write(|w| w.events_phyend().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        assert_eq!(unsafe { &RECEIVED_RESULT }, &Ok(()));
        assert_eq!(unsafe { RECEIVED_CONTEXT }, &None::<u8>); // TODO check address instead of value
        assert!(radio_mock.intenclr.read().phyend().bit_is_set());
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_enter_rx() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut FRAME: [u8; 128] = [0; 128];

        fn callback(_result: Result<RxOk, Error>, _context: Context, _resources: &mut RxResources) {
            unsafe { CALLED = true };
        }

        let result = phy.rx(RxRequest::new(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        )
        .now());

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // TODO check bits that should be clear? Can I easily check "all other bits"?
        assert!(radio_mock.shorts.read().rxready_start().bit_is_set());
        assert!(radio_mock.shorts.read().end_disable().bit_is_set());
        assert!(radio_mock.events_crcok.read().events_crcok().bit_is_clear());
        assert!(radio_mock
            .events_crcerror
            .read()
            .events_crcerror()
            .bit_is_clear());
        assert!(radio_mock.intenset.read().crcok().bit_is_set());
        assert!(radio_mock.intenset.read().crcerror().bit_is_set());
        assert_eq!(
            radio_mock.packetptr.read().bits(),
            unsafe { FRAME.as_ptr() } as u32
        );

        assert!(!unsafe { CALLED });
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_rx_correct_frame() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Option<Result<RxOk, Error>> = None;
        static mut FRAME: [u8; 128] = [0; 128];

        fn callback(result: Result<RxOk, Error>, _context: Context, _resources: &mut RxResources) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = Some(result) };
        }

        let result = phy.rx(RxRequest::new(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        )
        .now());

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_crcok
            .write(|w| w.events_crcok().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        unsafe {
            assert!(RECEIVED_RESULT.is_some());
            let received_option = RECEIVED_RESULT.replace(Err(Error::WouldBlock)).unwrap();
            assert!(received_option.is_ok());
            assert_eq!(
                received_option.as_ref().unwrap().frame.as_ptr() as u32,
                FRAME.as_ptr() as u32
            );
        }
        assert!(radio_mock.intenclr.read().crcok().bit_is_set());
        assert!(radio_mock.intenclr.read().crcerror().bit_is_set());
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_rx_frame_with_incorrect_crc() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Option<Result<RxOk, Error>> = None;
        static mut FRAME: [u8; 128] = [0; 128];

        fn callback(result: Result<RxOk, Error>, _context: Context, _resources: &mut RxResources) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = Some(result) };
        }

        let result = phy.rx(RxRequest::new(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        )
        .now());

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_crcerror
            .write(|w| w.events_crcerror().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        assert_eq!(unsafe { &RECEIVED_RESULT }, &Some(Err(Error::IncorrectCrc)));
        assert!(radio_mock.intenclr.read().crcok().bit_is_set());
        assert!(radio_mock.intenclr.read().crcerror().bit_is_set());
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_tx_request_in_rx_state_returns_error() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut RX_CALLED: bool = false;
        static mut FRAME: [u8; 128] = [0; 128];

        fn rx_callback(
            _result: Result<RxOk, Error>,
            _context: Context,
            _resources: &mut RxResources,
        ) {
            unsafe { RX_CALLED = true };
        }

        let result = phy.rx(RxRequest::new(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            rx_callback,
            &None::<usize>,
        )
        .now());
        assert_eq!(result, Ok(()));

        let frame: [u8; 17] = [
            16, 0x41, 0x98, 0xaa, 0xcd, 0xab, 0xff, 0xff, 0x34, 0x12, 0x01, 0x02, 0x03, 0x04, 0x05,
            0x06, 0x07,
        ];

        static mut TX_CALLED: bool = false;
        static mut TX_RECEIVED_RESULT: Option<Result<(), Error>> = None;
        static mut TX_RECEIVED_CONTEXT: &Option<u8> = &Some(0);

        fn tx_callback(result: Result<(), Error>, context: Context) {
            unsafe { TX_CALLED = true };
            unsafe { TX_RECEIVED_RESULT = Some(result) };
            unsafe { TX_RECEIVED_CONTEXT = context.downcast_ref().unwrap() };
        }

        let result = phy.tx(&frame, tx_callback, &None::<u8>);
        assert_eq!(result, Err(Error::WouldBlock));

        assert!(!unsafe { RX_CALLED });
        assert!(!unsafe { TX_CALLED });
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_rx_request_during_tx_returns_error() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        let frame: [u8; 17] = [
            16, 0x41, 0x98, 0xaa, 0xcd, 0xab, 0xff, 0xff, 0x34, 0x12, 0x01, 0x02, 0x03, 0x04, 0x05,
            0x06, 0x07,
        ];

        static mut TX_CALLED: bool = false;
        static mut TX_RECEIVED_RESULT: Option<Result<(), Error>> = None;
        static mut TX_RECEIVED_CONTEXT: &Option<u8> = &Some(0);
        static mut RX_FRAME: [u8; 128] = [0; 128];

        fn tx_callback(result: Result<(), Error>, context: Context) {
            unsafe { TX_CALLED = true };
            unsafe { TX_RECEIVED_RESULT = Some(result) };
            unsafe { TX_RECEIVED_CONTEXT = context.downcast_ref().unwrap() };
        }

        let result = phy.tx(&frame, tx_callback, &None::<u8>);
        assert_eq!(result, Ok(()));

        static mut RX_CALLED: bool = false;

        fn rx_callback(
            _result: Result<RxOk, Error>,
            _context: Context,
            _resources: &mut RxResources,
        ) {
            unsafe { RX_CALLED = true };
        }

        let result = phy.rx(RxRequest::new(
            create_frame_buffer_from_static_buffer(unsafe { &mut RX_FRAME }),
            rx_callback,
            &None::<usize>,
        ));
        assert_eq!(result, Err(Error::WouldBlock));

        assert!(!unsafe { RX_CALLED });
        assert!(!unsafe { TX_CALLED });
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_rx_frame_with_ppi_on_phyend() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Option<Result<RxOk, Error>> = None;
        static mut RETURNED_PPI_CHANNEL: Option<ppi::Channel> = None;
        static mut FRAME: [u8; 128] = [0; 128];

        let mut ppi_ch_mock = MockChannel::new();
        let expected_event_ptr = &radio_mock.events_phyend as *const _ as u32;
        ppi_ch_mock
            .expect_publish_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    radio::events_phyend::EVENTS_PHYEND_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        ppi_ch_mock
            .expect_stop_publishing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    radio::events_phyend::EVENTS_PHYEND_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));

        fn callback(result: Result<RxOk, Error>, _context: Context, resources: &mut RxResources) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = Some(result) };
            unsafe { RETURNED_PPI_CHANNEL = resources.phyend_ppi_channel() };
        }

        let result = phy.rx(RxRequest::new(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        )
        .with_ppi_channel_on_phyend(ppi_ch_mock)
        .now());

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_crcok
            .write(|w| w.events_crcok().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        unsafe {
            assert!(RECEIVED_RESULT.is_some());
            let received_option = RECEIVED_RESULT.replace(Err(Error::WouldBlock)).unwrap();
            assert!(received_option.is_ok());
            assert_eq!(
                received_option.as_ref().unwrap().frame.as_ptr() as u32,
                FRAME.as_ptr() as u32
            );
            // TODO: Verify id?
            assert!(RETURNED_PPI_CHANNEL.is_some());
        }
        assert!(radio_mock.intenclr.read().crcok().bit_is_set());
        assert!(radio_mock.intenclr.read().crcerror().bit_is_set());
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_rx_frame_with_ppi_on_phyend_ends_with_crcerror() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Option<Result<RxOk, Error>> = None;
        static mut RETURNED_PPI_CHANNEL: Option<ppi::Channel> = None;
        static mut FRAME: [u8; 128] = [0; 128];

        let mut ppi_ch_mock = MockChannel::new();
        let expected_event_ptr = &radio_mock.events_phyend as *const _ as u32;
        ppi_ch_mock
            .expect_publish_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    radio::events_phyend::EVENTS_PHYEND_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        ppi_ch_mock
            .expect_stop_publishing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    radio::events_phyend::EVENTS_PHYEND_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));

        fn callback(result: Result<RxOk, Error>, _context: Context, resources: &mut RxResources) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = Some(result) };
            unsafe { RETURNED_PPI_CHANNEL = resources.phyend_ppi_channel() };
        }

        let result = phy.rx(RxRequest::new(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        )
        .with_ppi_channel_on_phyend(ppi_ch_mock)
        .now());

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_crcerror
            .write(|w| w.events_crcerror().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        assert_eq!(unsafe { &RECEIVED_RESULT }, &Some(Err(Error::IncorrectCrc)));
        // TODO: Verify id?
        assert!(unsafe { RETURNED_PPI_CHANNEL.is_some() });
        assert!(radio_mock.intenclr.read().crcok().bit_is_set());
        assert!(radio_mock.intenclr.read().crcerror().bit_is_set());
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_start_rx_at_hardware_event() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Option<Result<RxOk, Error>> = None;
        static mut RETURNED_PPI_CHANNEL: Option<ppi::Channel> = None;
        static mut FRAME: [u8; 128] = [0; 128];

        fn callback(result: Result<RxOk, Error>, _context: Context, resources: &mut RxResources) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = Some(result) };
            unsafe { RETURNED_PPI_CHANNEL = resources.start_channel() };
        }

        let mut ppi_ch_mock = MockChannel::new();
        let expected_task_ptr = &radio_mock.tasks_rxen as *const _ as u32;
        ppi_ch_mock
            .expect_subscribe_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    radio::tasks_rxen::TASKS_RXEN_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        ppi_ch_mock
            .expect_stop_subscribing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    radio::tasks_rxen::TASKS_RXEN_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));

        let result = phy.rx(RxRequest::new(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        )
        .at_event(ppi_ch_mock));

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_crcok
            .write(|w| w.events_crcok().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        unsafe {
            assert!(RECEIVED_RESULT.is_some());
            let received_option = RECEIVED_RESULT.replace(Err(Error::WouldBlock)).unwrap();
            assert!(received_option.is_ok());
            assert_eq!(
                received_option.as_ref().unwrap().frame.as_ptr() as u32,
                FRAME.as_ptr() as u32
            );
            // TODO: Verify id?
            assert!(RETURNED_PPI_CHANNEL.is_some());
        }
        assert!(radio_mock.intenclr.read().crcok().bit_is_set());
        assert!(radio_mock.intenclr.read().crcerror().bit_is_set());
    }
}
