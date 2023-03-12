//! Timer implementation based on the TIMER peripheral available in nRF MCUs
//!
//! This is the simplest freerunning timer with microsecond precision and capability to capture
//! timstamps available in nRF52. However it's usage significantly increases power consumption.
//! This module is fine for tests, however it should replaced with something more power efficient
//! for battery operated devices.

use super::super::ppi::{traits::Channel as PpiChannelTrait, Channel};
use super::{
    traits::{TaskTrigger, Timer, Timestamper},
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
const CAPTURE_TIMESTAMP_CH: usize = 1;
const TRIGGER_TASK_CH: usize = 2;

/// Timer based on `TIMER` peripheral
pub struct TimerUsingTimer {
    timer: TimerPeriphWrapper,
    is_capturing: AtomicBool,
    is_triggering: AtomicBool,
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
            is_capturing: AtomicBool::new(false),
            is_triggering: AtomicBool::new(false),
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

impl Timestamper for TimerUsingTimer {
    fn start_capturing_timestamps(&self, ppi_ch: &Channel) -> Result<(), Error> {
        self.is_capturing
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .map_or(Err(Error::WouldBlock), |_| {
                ppi_ch.subscribe_by(&self.timer.tasks_capture[CAPTURE_TIMESTAMP_CH] as *const _)
            })
    }

    fn stop_capturing_timestamps(&self, ppi_ch: &Channel) -> Result<(), Error> {
        self.is_capturing
            .compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst)
            .map_or(Err(Error::WouldBlock), |_| {
                ppi_ch.stop_subscribing_by(
                    &self.timer.tasks_capture[CAPTURE_TIMESTAMP_CH] as *const _,
                )
            })
    }

    fn timestamp(&self) -> Result<u32, Error> {
        Ok(self.timer.cc[CAPTURE_TIMESTAMP_CH].read().bits())
    }
}

impl TaskTrigger for TimerUsingTimer {
    type TriggerHandle = TriggerHandle;

    fn trigger_task_at(
        &self,
        ppi_ch: &Channel,
        time: Timestamp,
    ) -> Result<Self::TriggerHandle, Error> {
        self.is_triggering
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .map_or(Err(Error::WouldBlock), |_| {
                self.timer.cc[TRIGGER_TASK_CH].write(|w| w.cc().variant(time));
                ppi_ch.publish_by(&self.timer.events_compare[TRIGGER_TASK_CH] as *const _)?;
                Ok(TriggerHandle(TRIGGER_TASK_CH))
            })
    }

    fn stop_triggering_task(
        &self,
        handle: Self::TriggerHandle,
        ppi_ch: &Channel,
    ) -> Result<(), Error> {
        if handle.0 != TRIGGER_TASK_CH {
            return Err(Error::InvalidArgument);
        }

        self.is_triggering
            .compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst)
            .map_or(Err(Error::WouldBlock), |_| {
                ppi_ch.stop_publishing_by(&self.timer.events_compare[TRIGGER_TASK_CH] as *const _)
            })
    }
}

/// Handle to a scheduled timer triggering a hardware task
#[derive(Debug, Eq, PartialEq)]
pub struct TriggerHandle(usize);

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

        let timestamp = timer.timestamp();
        assert_eq!(timestamp.unwrap(), 0);

        let expected_timestamp = 0xdeadbeefu32;
        timer_mock.cc[CAPTURE_TIMESTAMP_CH].write(|w| w.cc().variant(expected_timestamp));
        let timestamp = timer.timestamp();
        assert_eq!(timestamp.unwrap(), expected_timestamp);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_start_capturing() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let expected_task_ptr = &timer_mock.tasks_capture[CAPTURE_TIMESTAMP_CH] as *const _ as u32;

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

        let result = timer.start_capturing_timestamps(&ppi_ch_mock);
        assert!(result.is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_start_capturing_twice_fails() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let expected_task_ptr = &timer_mock.tasks_capture[CAPTURE_TIMESTAMP_CH] as *const _ as u32;

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

        let result = timer.start_capturing_timestamps(&ppi_ch_mock);
        assert!(result.is_ok());

        let result = timer.start_capturing_timestamps(&ppi_ch_mock);
        assert_eq!(result, Err(Error::WouldBlock));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_capturing_fails_if_not_started() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let ppi_ch_mock = MockChannel::new();

        let result = timer.stop_capturing_timestamps(&ppi_ch_mock);
        assert_eq!(result, Err(Error::WouldBlock));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_capturing_when_started() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let expected_task_ptr = &timer_mock.tasks_capture[CAPTURE_TIMESTAMP_CH] as *const _ as u32;

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
        let result = timer.start_capturing_timestamps(&ppi_ch_mock);
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
        let result = timer.stop_capturing_timestamps(&ppi_ch_mock);
        assert!(result.is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_capturing_twice_fails() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let expected_task_ptr = &timer_mock.tasks_capture[CAPTURE_TIMESTAMP_CH] as *const _ as u32;

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
        let result = timer.start_capturing_timestamps(&ppi_ch_mock);
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
        let result = timer.stop_capturing_timestamps(&ppi_ch_mock);
        assert!(result.is_ok());

        let result = timer.stop_capturing_timestamps(&ppi_ch_mock);
        assert_eq!(result, Err(Error::WouldBlock));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_prepare_triggering() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0x87654321;
        let expected_event_ptr = &timer_mock.events_compare[TRIGGER_TASK_CH] as *const _ as u32;

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

        let result = timer.trigger_task_at(&ppi_ch_mock, timestamp);
        assert!(result.is_ok());

        assert_eq!(timer_mock.cc[TRIGGER_TASK_CH].read().cc().bits(), timestamp);
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_prepare_triggering_twice_fails() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0x01234567;
        let expected_event_ptr = &timer_mock.events_compare[TRIGGER_TASK_CH] as *const _ as u32;

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

        let result = timer.trigger_task_at(&ppi_ch_mock, timestamp);
        assert!(result.is_ok());

        let result = timer.trigger_task_at(&ppi_ch_mock, timestamp);
        assert_eq!(result, Err(Error::WouldBlock));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_stop_triggering_when_started() {
        let timer_mock = TimerMock::new();
        let timer = TimerUsingTimer::new(&timer_mock);

        let timestamp = 0xcafecafe;
        let expected_event_ptr = &timer_mock.events_compare[TRIGGER_TASK_CH] as *const _ as u32;

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
        let result = timer.trigger_task_at(&ppi_ch_mock, timestamp);
        assert!(result.is_ok());

        let handle = result.unwrap();

        ppi_ch_mock
            .expect_stop_publishing_by()
            .withf(
                move |t: &*const nrf52840_hal::pac::generic::Reg<
                    timer0::events_compare::EVENTS_COMPARE_SPEC,
                >| *t as u32 == expected_event_ptr,
            )
            .times(1)
            .returning(|_| Ok(()));
        let result = timer.stop_triggering_task(handle, &ppi_ch_mock);
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
