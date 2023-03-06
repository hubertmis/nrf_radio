//! Portable timer abstraction
//!
//! Timer implementation provides abstract features related to scheduling events. It includes:
//!
//! * scheduling functions to run deferred jobs
//! * scheduling hardware events for [PPIs](super::ppi)
//! * timestamping hardware events from [PPIs](super::ppi)

pub mod timer_using_timer;

use super::ppi::traits::Channel;
use crate::error::Error;

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
//       Let's keep dynamic dispatch for now and come back to this decision later.
//       Like most architecture decisions changing this will be difficult, but I don't know Rust
//       well enough yet to take good architectural decisions now.

/// Defines functions required by any module providing timer features
///
/// Modules implementing this trait are expected to use hardware, or lower level features (like
/// operating system timers) to provide required features
pub trait Timer<PC: Channel>: Sync + Timestamper<PC> {
    /// Start this timer
    ///
    /// When timer is started its value is monotonically increasing in time.
    fn start(&mut self) -> Result<(), Error>;
}

/// Capability of timestamping hardware events
///
/// The timestamps must be taken using a freerunning timer synchronized with the freeruning timers
/// for other features of the [`Timer`] trait
// TODO: multiple channels?
pub trait Timestamper<PC: Channel> {
    /// Start capturing timestamps of events published to the passed PPI channel
    ///
    /// When an event is published in the passed PPI channel the timestamp is to be captured. The
    /// value of the timestamp can be checked with the [`timestamp`](Timestamper::timestamp)
    /// function. The module keeps capturing timestamps of following events published in the PPI
    /// channel overwritting previous timestamps until
    /// [`stop_capturing_timestamps`](Timestamper::stop_capturing_timestamps) is called.
    fn start_capturing_timestamps(&self, ppi_ch: &PC) -> Result<(), Error>;

    /// Stop capturing timestamps of events published to the passed PPI channel
    ///
    /// After calling this function the last captured timestamp (if any) is available through a call
    /// to the [`timestamp`](Timestamper::timestamp) function.
    fn stop_capturing_timestamps(&self, ppi_ch: &PC) -> Result<(), Error>;

    /// Get the last captured timestamp (if any) in microseconds
    fn timestamp(&self) -> Result<u32, Error>;
}

// TODO: callback scheduler trait
// TODO: task trigger trait
