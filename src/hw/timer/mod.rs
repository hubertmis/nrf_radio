//! Portable timer abstraction
//!
//! Timer implementation provides abstract features related to scheduling events. It includes:
//!
//! * scheduling functions to run deferred jobs
//! * scheduling hardware events for [PPIs](super::ppi)
//! * timestamping hardware events from [PPIs](super::ppi)

#[cfg(feature = "nrf52840")]
pub mod timer_using_timer;

// Temporarily use nRF52 timer until mock is available
#[cfg(feature = "mocked_platform")]
pub mod timer_using_timer;

pub mod traits;

/// Absolute time (timestamp) in this system
///
/// The resolution is 1 microsecond
pub type Timestamp = u32;

// TODO: so far I have no idea how to make this module portable. Let's think about it later
//       It needs to be able to use TIMER, RTC, combination of both, or newer hardware peripherals
//
//       I guess I need a trait Timer that will be implemented by sth in the system (using TIMER,
//       RTC, or both). But then how to make static variables holding reference to this trait?
//       Dynamic dispatching?
//
//       Another option would be to reuse the pattern from PPIs where the only available PPI port is
//       defined at the mod level. It would allow avoiding dynamic dispatch, but instead it would
//       limits the software build to a single timer type. Would such limitation be ok?
//
//       Let's try PPI pattern to avoid dynamic dispatching especially when TriggerHandle type is
//       introduced.

/// Selected type of timer implementation for this build
pub type Timer = timer_using_timer::TimerUsingTimer;
