//! Traits required from a portable Timer object

use super::Timestamp;
use crate::error::Error;
use crate::hw::ppi::Channel;

/// Defines functions required by any module providing timer features
///
/// Modules implementing this trait are expected to use hardware, or lower level features (like
/// operating system timers) to provide required features
pub trait Timer: Sync + Timestamper + TaskTrigger {
    /// Start this timer
    ///
    /// When timer is started its value is monotonically increasing in time.
    fn start(&mut self) -> Result<(), Error>;

    /// Get current time
    fn now(&self) -> Result<Timestamp, Error>;

    /// Check if the passed `timestamp` is in the past
    fn was_timestamp_in_past(&self, timestamp: &Timestamp) -> Result<bool, Error> {
        let now = self.now()?;
        let one_tick_ago = Timestamp::wrapping_sub(now, 1);
        Ok(Timestamp::wrapping_sub(one_tick_ago, *timestamp) < (Timestamp::MAX / 2))
    }
}

/// Capability of timestamping hardware events
///
/// The timestamps must be taken using a freerunning timer synchronized with the freeruning timers
/// for other features of the [`Timer`] trait
// TODO: multiple channels?
pub trait Timestamper {
    /// Start capturing timestamps of events published to the passed PPI channel
    ///
    /// When an event is published in the passed PPI channel the timestamp is to be captured. The
    /// value of the timestamp can be checked with the [`timestamp`](Timestamper::timestamp)
    /// function. The module keeps capturing timestamps of following events published in the PPI
    /// channel overwritting previous timestamps until
    /// [`stop_capturing_timestamps`](Timestamper::stop_capturing_timestamps) is called.
    fn start_capturing_timestamps(&self, ppi_ch: &Channel) -> Result<(), Error>;

    /// Stop capturing timestamps of events published to the passed PPI channel
    ///
    /// After calling this function the last captured timestamp (if any) is available through a call
    /// to the [`timestamp`](Timestamper::timestamp) function.
    fn stop_capturing_timestamps(&self, ppi_ch: &Channel) -> Result<(), Error>;

    /// Get the last captured timestamp (if any) in microseconds
    fn timestamp(&self) -> Result<Timestamp, Error>;
}

/// Capability of triggering hardware tasks
///
/// The tasks are triggered according to a freeruning timer synchronized with the freerunning
/// timers for other features of the [`Timer`] trait
pub trait TaskTrigger {
    /// Type representing a scheduled trigger task
    type TriggerHandle;

    /// Prepare hardware to publish to a PPI channel at specified time
    ///
    /// At specified `time` this timer published to the passed PPI channel what triggers all tasks
    /// subscribing to this channel.
    fn trigger_task_at(
        &self,
        ppi_ch: &Channel,
        time: Timestamp,
    ) -> Result<Self::TriggerHandle, Error>;

    /// Deconfigure hardware from publishing timer event to the passed PPI channel
    ///
    /// The passed `ppi_ch` must be the same that was passed to the [`publish_task_to`] method.
    /// The object implementing this trait does not keep reference to `ppi_ch` to avoid borrowing
    /// it while the timer is active.
    fn stop_triggering_task(
        &self,
        handle: Self::TriggerHandle,
        ppi_ch: &Channel,
    ) -> Result<(), Error>;
}

// TODO: callback scheduler trait
