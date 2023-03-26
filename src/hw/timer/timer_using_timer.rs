//! Timer implementation based on the TIMER peripheral available in nRF MCUs
//!
//! This is the simplest freerunning timer with microsecond precision and capability to capture
//! timstamps available in nRF52. However it's usage significantly increases power consumption.
//! This module is fine for tests, however it should replaced with something more power efficient
//! for battery operated devices.

use super::super::ppi::{traits::Channel as PpiChannelTrait, Channel};
use super::{
    traits::{TaskChannel, TaskTrigger, Timer, TimestampChannel, Timestamper},
    Timestamp,
};
use crate::error::Error;
use core::ops::Deref;
use core::sync::atomic::{AtomicBool, Ordering};

// Copied from src/radio.rs and modified a little.
// This copy includes TimerPeriphWrapper
use nrf52840_hal::pac::timer0;
type TimerRegisterBlock = timer0::RegisterBlock;

struct TimerPeriphWrapper {
    ptr: *const TimerRegisterBlock,
}
impl TimerPeriphWrapper {
    pub fn new(timer: &TimerRegisterBlock) -> Self {
        TimerPeriphWrapper { ptr: timer }
    }
}
impl Deref for TimerPeriphWrapper {
    type Target = TimerRegisterBlock;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}
unsafe impl Sync for TimerPeriphWrapper {} // Is this really safe considering it's just pointer
                                           // dereference?

const CAPTURE_NOW_CH: usize = 0;
const CAPTURE_TIMESTAMP_CH: u8 = 1;
const TRIGGER_TASK_CH: u8 = 2;

/// Timer based on `TIMER` peripheral
pub struct TimerUsingTimer {
    timer: TimerPeriphWrapper,
    is_timestamp_channel_allocated: AtomicBool,
    is_task_allocated: AtomicBool,
}

impl TimerUsingTimer {
    /// Create a new [`TimerUsingTimer`] instance using passed hardware TIMER instance
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    /// use nrf_radio::hw::timer::timer_using_timer::TimerUsingTimer;
    /// use nrf52840_hal::pac::Peripherals;
    ///
    /// let peripherals = Peripherals::take().unwrap();
    ///
    /// let timer = TimerUsingTimer::new(&peripherals.TIMER0);
    /// # }
    /// ```
    pub fn new(timer: &TimerRegisterBlock) -> Self {
        Self {
            timer: TimerPeriphWrapper::new(timer),
            is_timestamp_channel_allocated: AtomicBool::new(false),
            is_task_allocated: AtomicBool::new(false),
        }
    }
}

impl Timer for TimerUsingTimer {
    fn start(&mut self) -> Result<(), Error> {
        self.timer
            .bitmode
            .write(|w| w.bitmode().variant(timer0::bitmode::BITMODE_A::_32BIT));
        self.timer.prescaler.write(|w| w.prescaler().variant(4));
        self.timer.tasks_start.write(|w| w.tasks_start().set_bit());
        Ok(())
    }

    fn now(&self) -> Result<Timestamp, Error> {
        self.timer.tasks_capture[CAPTURE_NOW_CH].write(|w| w.tasks_capture().set_bit());
        Ok(self.timer.cc[CAPTURE_NOW_CH].read().bits())
    }
}

impl<'t> Timestamper<'t> for TimerUsingTimer {
    type Channel = TimerTimestampChannel<'t>;

    fn allocate_timestamp_channel(&'t self) -> Result<TimerTimestampChannel<'t>, Error> {
        self.is_timestamp_channel_allocated
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .map_or(Err(Error::NoResources), |_| {
                Ok(TimerTimestampChannel::new(self, CAPTURE_TIMESTAMP_CH))
            })
    }
}

/// Timer channel using a `TIMER` peripheral to capture timestamps of PPI events
///
/// This abstract channel uses single hardware channel of the `TIMER` peripheral in use
pub struct TimerTimestampChannel<'ch> {
    is_capturing: AtomicBool,
    idx: u8,
    timer: &'ch TimerUsingTimer,
}

impl<'ch> TimerTimestampChannel<'ch> {
    fn new(timer: &'ch TimerUsingTimer, idx: u8) -> Self {
        Self {
            is_capturing: AtomicBool::new(false),
            idx,
            timer,
        }
    }
}

impl TimestampChannel for TimerTimestampChannel<'_> {
    fn start_capturing(&mut self, ppi_ch: &Channel) -> Result<(), Error> {
        self.is_capturing
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .map_or(Err(Error::WouldBlock), |_| {
                let idx = self.idx as usize;
                ppi_ch.subscribe_by(&self.timer.timer.tasks_capture[idx] as *const _)
            })
    }

    fn stop_capturing(&mut self, ppi_ch: &Channel) -> Result<(), Error> {
        self.is_capturing
            .compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst)
            .map_or(Err(Error::WouldBlock), |_| {
                let idx = self.idx as usize;
                ppi_ch.stop_subscribing_by(&self.timer.timer.tasks_capture[idx] as *const _)
            })
    }

    fn timestamp(&self) -> Result<u32, Error> {
        let idx = self.idx as usize;
        Ok(self.timer.timer.cc[idx].read().bits())
    }
}

impl Drop for TimerTimestampChannel<'_> {
    fn drop(&mut self) {
        assert!(!self.is_capturing.load(Ordering::Relaxed));
        self.timer
            .is_timestamp_channel_allocated
            .compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed)
            .unwrap();
    }
}

impl<'t> TaskTrigger<'t> for TimerUsingTimer {
    type Channel = TimerTaskChannel<'t>;

    fn allocate_task_channel(&'t self) -> Result<TimerTaskChannel<'t>, Error> {
        self.is_task_allocated
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .map_or(Err(Error::NoResources), |_| {
                Ok(TimerTaskChannel::new(self, TRIGGER_TASK_CH))
            })
    }
}

/// Timer channel using a `TIMER` peripheral to trigger PPI tasks at requested time
///
/// This abstract channel uses single hardware channel of the `TIMER` peripheral
pub struct TimerTaskChannel<'ch> {
    is_triggering: AtomicBool,
    idx: u8,
    timer: &'ch TimerUsingTimer,
}

impl<'ch> TimerTaskChannel<'ch> {
    fn new(timer: &'ch TimerUsingTimer, idx: u8) -> Self {
        Self {
            is_triggering: AtomicBool::new(false),
            idx,
            timer,
        }
    }
}

impl TaskChannel for TimerTaskChannel<'_> {
    fn trigger_at(&mut self, ppi_ch: &Channel, time: Timestamp) -> Result<(), Error> {
        self.is_triggering
            .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
            .map_or(Err(Error::WouldBlock), |_| {
                let idx = self.idx as usize;
                self.timer.timer.cc[idx].write(|w| w.cc().variant(time));
                ppi_ch.publish_by(&self.timer.timer.events_compare[idx] as *const _)?;
                Ok(())
            })
    }

    fn disable(&mut self, ppi_ch: &Channel) -> Result<(), Error> {
        self.is_triggering
            .compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed)
            .map_or(Err(Error::WouldBlock), |_| {
                let idx = self.idx as usize;
                ppi_ch.stop_publishing_by(&self.timer.timer.events_compare[idx] as *const _)
            })
    }
}

impl Drop for TimerTaskChannel<'_> {
    fn drop(&mut self) {
        assert!(!self.is_triggering.load(Ordering::Relaxed));
        self.timer
            .is_task_allocated
            .compare_exchange(true, false, Ordering::Relaxed, Ordering::Relaxed)
            .unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::ppi::traits::MockChannel;
    use super::*;

    // TIMER peripheral mock
    #[repr(align(4))]
    struct TimerMock {
        memory: [u8; 4096],
    }

    impl TimerMock {
        pub fn new() -> Self {
            Self { memory: [0; 4096] }
        }
    }

    impl Deref for TimerMock {
        type Target = TimerRegisterBlock;
        fn deref(&self) -> &Self::Target {
            let ptr: *const TimerRegisterBlock = self.memory.as_ptr() as *const _;
            unsafe { ptr.as_ref().unwrap() }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_start() {
        let timer_mock = TimerMock::new();
        let mut timer: TimerUsingTimer = TimerUsingTimer::new(&timer_mock);

        let result = timer.start();
        assert!(result.is_ok());

        assert_eq!(
            timer_mock.mode.read().mode().variant().unwrap(),
            timer0::mode::MODE_A::TIMER
        );
        assert_eq!(
            timer_mock.bitmode.read().bitmode().variant(),
            timer0::bitmode::BITMODE_A::_32BIT
        );
        assert_eq!(timer_mock.prescaler.read().prescaler().bits(), 4);
        // TODO: How to check if TASKS_START was called?
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_now() {
        let timer_mock = TimerMock::new();
        let mut timer: TimerUsingTimer = TimerUsingTimer::new(&timer_mock);

        let result = timer.start();
        assert!(result.is_ok());

        let expected_timestamp = 0xfdb97531;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(expected_timestamp));

        let result = timer.now();
        // TODO: How to check if TASKS_CAPTURE[CAPTURE_NOW_CH] was called?
        assert_eq!(result, Ok(expected_timestamp));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_timestamp() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let channel = timer.allocate_timestamp_channel().unwrap();

        let timestamp = channel.timestamp();
        assert_eq!(timestamp.unwrap(), 0);

        let expected_timestamp = 0xdeadbeefu32;
        timer_mock.cc[CAPTURE_TIMESTAMP_CH as usize].write(|w| w.cc().variant(expected_timestamp));
        let timestamp = channel.timestamp();
        assert_eq!(timestamp.unwrap(), expected_timestamp);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_allocate_timestamp_channel() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let channel_result = timer.allocate_timestamp_channel();

        channel_result.unwrap();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_allocating_more_timestamp_channels_than_available_fails() {
        const NUM_CHANNELS: usize = 1;

        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let mut channel_results = [None::<TimerTimestampChannel>; NUM_CHANNELS];

        for i in 0..NUM_CHANNELS {
            let channel_result = timer.allocate_timestamp_channel();
            channel_results[i] = Some(channel_result.unwrap());
        }

        let channel_result = timer.allocate_timestamp_channel();
        assert!(channel_result.is_err());
        assert_eq!(channel_result.err(), Some(Error::NoResources));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_timestamp_channels_can_be_reallocated_after_dropped() {
        const NUM_CHANNELS: usize = 1;

        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        {
            let mut channel_results = [None::<TimerTimestampChannel>; NUM_CHANNELS];

            for i in 0..NUM_CHANNELS {
                let channel_result = timer.allocate_timestamp_channel();
                channel_results[i] = Some(channel_result.unwrap());
            }

            // Dropping all allocated channels
        }

        let channel_result = timer.allocate_timestamp_channel();
        channel_result.unwrap();
    }

    #[test]
    #[should_panic]
    #[cfg_attr(miri, ignore)]
    fn test_dropping_timestamp_channel_in_use_panics() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let channel_result = timer.allocate_timestamp_channel();

        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock.expect_subscribe_by().returning(
            |_: *const nrf52840_hal::pac::generic::Reg<
                timer0::tasks_capture::TASKS_CAPTURE_SPEC,
            >| Ok(()),
        );

        {
            let mut channel = channel_result.unwrap();
            channel.start_capturing(&ppi_ch_mock).unwrap();

            // Channel is dropped at the end of this block
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_start_capturing() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let mut channel = timer.allocate_timestamp_channel().unwrap();

        let expected_task_ptr =
            &timer_mock.tasks_capture[CAPTURE_TIMESTAMP_CH as usize] as *const _ as u32;

        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock
            .expect_subscribe_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::tasks_capture::TASKS_CAPTURE_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));

        let result = channel.start_capturing(&ppi_ch_mock);
        assert!(result.is_ok());

        // Tear down: stop capturing before dropping channel
        ppi_ch_mock
            .expect_stop_subscribing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::tasks_capture::TASKS_CAPTURE_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        channel.stop_capturing(&ppi_ch_mock).unwrap();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_start_capturing_twice_fails() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let mut channel = timer.allocate_timestamp_channel().unwrap();

        let expected_task_ptr =
            &timer_mock.tasks_capture[CAPTURE_TIMESTAMP_CH as usize] as *const _ as u32;

        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock
            .expect_subscribe_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::tasks_capture::TASKS_CAPTURE_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));

        let result = channel.start_capturing(&ppi_ch_mock);
        assert!(result.is_ok());

        let result = channel.start_capturing(&ppi_ch_mock);
        assert_eq!(result, Err(Error::WouldBlock));

        // Tear down: stop capturing before dropping channel
        ppi_ch_mock
            .expect_stop_subscribing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::tasks_capture::TASKS_CAPTURE_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        channel.stop_capturing(&ppi_ch_mock).unwrap();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_capturing_fails_if_not_started() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let mut channel = timer.allocate_timestamp_channel().unwrap();

        let ppi_ch_mock = MockChannel::new();

        let result = channel.stop_capturing(&ppi_ch_mock);
        assert_eq!(result, Err(Error::WouldBlock));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_capturing_when_started() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let mut channel = timer.allocate_timestamp_channel().unwrap();

        let expected_task_ptr =
            &timer_mock.tasks_capture[CAPTURE_TIMESTAMP_CH as usize] as *const _ as u32;

        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock
            .expect_subscribe_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::tasks_capture::TASKS_CAPTURE_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        let result = channel.start_capturing(&ppi_ch_mock);
        assert!(result.is_ok());

        ppi_ch_mock
            .expect_stop_subscribing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::tasks_capture::TASKS_CAPTURE_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        let result = channel.stop_capturing(&ppi_ch_mock);
        assert!(result.is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_capturing_twice_fails() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let mut channel = timer.allocate_timestamp_channel().unwrap();

        let expected_task_ptr =
            &timer_mock.tasks_capture[CAPTURE_TIMESTAMP_CH as usize] as *const _ as u32;

        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock
            .expect_subscribe_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::tasks_capture::TASKS_CAPTURE_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        let result = channel.start_capturing(&ppi_ch_mock);
        assert!(result.is_ok());

        ppi_ch_mock
            .expect_stop_subscribing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::tasks_capture::TASKS_CAPTURE_SPEC,
                >| *t as u32 == expected_task_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        let result = channel.stop_capturing(&ppi_ch_mock);
        assert!(result.is_ok());

        let result = channel.stop_capturing(&ppi_ch_mock);
        assert_eq!(result, Err(Error::WouldBlock));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_allocate_task_channel() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let channel_result = timer.allocate_task_channel();

        channel_result.unwrap();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_allocating_more_task_channels_than_available_fails() {
        const NUM_CHANNELS: usize = 1;

        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let mut channel_results = [None::<TimerTaskChannel>; NUM_CHANNELS];

        for i in 0..NUM_CHANNELS {
            let channel_result = timer.allocate_task_channel();
            channel_results[i] = Some(channel_result.unwrap());
        }

        let channel_result = timer.allocate_task_channel();
        assert!(channel_result.is_err());
        assert_eq!(channel_result.err(), Some(Error::NoResources));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_task_channels_can_be_reallocated_after_dropped() {
        const NUM_CHANNELS: usize = 1;

        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        {
            let mut channel_results = [None::<TimerTaskChannel>; NUM_CHANNELS];

            for i in 0..NUM_CHANNELS {
                let channel_result = timer.allocate_task_channel();
                channel_results[i] = Some(channel_result.unwrap());
            }

            // Dropping all allocated channels
        }

        let channel_result = timer.allocate_task_channel();
        channel_result.unwrap();
    }

    #[test]
    #[should_panic]
    #[cfg_attr(miri, ignore)]
    fn test_dropping_task_channel_in_use_panics() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);
        let channel_result = timer.allocate_task_channel();

        let timestamp = 0x00000000;
        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock.expect_publish_by().returning(
            |_: *const nrf52840_hal::pac::generic::Reg<
                timer0::events_compare::EVENTS_COMPARE_SPEC,
            >| Ok(()),
        );

        {
            let mut channel = channel_result.unwrap();
            channel.trigger_at(&ppi_ch_mock, timestamp).unwrap();

            // Channel is dropped at the end of this block
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_prepare_triggering() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0x87654321;
        let expected_event_ptr =
            &timer_mock.events_compare[TRIGGER_TASK_CH as usize] as *const _ as u32;

        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock
            .expect_publish_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::events_compare::EVENTS_COMPARE_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));

        let mut channel = timer.allocate_task_channel().unwrap();
        let result = channel.trigger_at(&ppi_ch_mock, timestamp);
        assert!(result.is_ok());

        assert_eq!(
            timer_mock.cc[TRIGGER_TASK_CH as usize].read().cc().bits(),
            timestamp
        );

        // Tear down: disable channel before dropping it
        ppi_ch_mock
            .expect_stop_publishing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::events_compare::EVENTS_COMPARE_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        channel.disable(&ppi_ch_mock).unwrap();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_prepare_triggering_twice_fails() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0x01234567;
        let expected_event_ptr =
            &timer_mock.events_compare[TRIGGER_TASK_CH as usize] as *const _ as u32;

        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock
            .expect_publish_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::events_compare::EVENTS_COMPARE_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));

        let mut channel = timer.allocate_task_channel().unwrap();
        let result = channel.trigger_at(&ppi_ch_mock, timestamp);
        assert!(result.is_ok());

        let result = channel.trigger_at(&ppi_ch_mock, timestamp);
        assert_eq!(result, Err(Error::WouldBlock));

        // Tear down: disable channel before dropping it
        ppi_ch_mock
            .expect_stop_publishing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::events_compare::EVENTS_COMPARE_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        channel.disable(&ppi_ch_mock).unwrap();
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_triggering_when_started() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0xcafecafe;
        let expected_event_ptr =
            &timer_mock.events_compare[TRIGGER_TASK_CH as usize] as *const _ as u32;

        let mut ppi_ch_mock = MockChannel::new();
        ppi_ch_mock
            .expect_publish_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::events_compare::EVENTS_COMPARE_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        let mut channel = timer.allocate_task_channel().unwrap();
        let result = channel.trigger_at(&ppi_ch_mock, timestamp);
        assert!(result.is_ok());

        ppi_ch_mock
            .expect_stop_publishing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::events_compare::EVENTS_COMPARE_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        let result = channel.disable(&ppi_ch_mock);
        assert!(result.is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_was() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0x68756d69;
        let now = timestamp + 1;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(true));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_was_not() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0x68756d69;
        let now = timestamp - 1;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(false));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_is_now() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0x68756d69;
        let now = timestamp;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(false));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_was_before_timer_overflow() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = Timestamp::MAX;
        let now = Timestamp::wrapping_add(timestamp, 1);

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(true));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_will_trigger_after_timer_overflow() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0;
        let now = Timestamp::wrapping_sub(timestamp, 1);

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(false));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_is_now_equal_min() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = Timestamp::MIN;
        let now = timestamp;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(false));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_is_now_equal_0() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0;
        let now = timestamp;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(false));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_is_now_equal_max() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = Timestamp::MAX;
        let now = timestamp;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(false));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_was_at_the_detection_boundary() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0;
        let now = Timestamp::MAX / 2;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(true));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_the_detection_boundary_just_passed() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0;
        let now = (Timestamp::MAX / 2) + 1;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(false));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_it_was_at_the_detection_boundary_with_overflow() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = (Timestamp::MAX / 2) + 2;
        let now = 0;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(true));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_if_timestamp_was_in_past_when_the_detection_boundary_with_overflow_just_passed() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = Timestamp::MAX / 2 + 2;
        let now = 1;

        timer_mock.cc[CAPTURE_NOW_CH].write(|w| w.cc().variant(now));

        let result = timer.was_timestamp_in_past(&timestamp);
        assert_eq!(result, Ok(false));
    }
}
