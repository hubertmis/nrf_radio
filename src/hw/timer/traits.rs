//! Traits required from a portable Timer object

use super::Timestamp;
use crate::error::Error;
use crate::hw::ppi::Channel;

//use core::any::Any;

/// Defines functions required by any module providing timer features
///
/// Modules implementing this trait are expected to use hardware, or lower level features (like
/// operating system timers) to provide required features
pub trait Timer: Sync + for<'t> Timestamper<'t> + for<'t> TaskTrigger<'t> {
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

/*
// TODO: callback scheduler trait
trait CallbackChannel {
    fn trigger_at(&self, callback: Callback, context: Context) -> Result<(), Error>;

    fn disable(&self) -> Result<(), Error>;
}

type Callback = fn(Context);
type Context = &'static dyn Any;
*/

/// Capability of timestamping hardware events
///
/// The timestamps are taken using a freerunning timer synchronized with the freeruning timers
/// for other features of the [`Timer`] trait
pub trait TimestampChannel {
    /// Start capturing timestamps of events published to the passed PPI channel
    ///
    /// When an event is published in the passed PPI channel the timestamp is to be captured. The
    /// value of the timestamp can be checked with the [`timestamp`](TimestampChannel::timestamp)
    /// function. The module keeps capturing timestamps of following events published in the PPI
    /// channel overwritting previous timestamps until
    /// [`stop_capturing`](TimestampChannel::stop_capturing) is called.
    fn start_capturing(&mut self, ppi_ch: &Channel) -> Result<(), Error>;

    /// Stop capturing timestamps of events published to the passed PPI channel
    ///
    /// After calling this function the last captured timestamp (if any) is available through a call
    /// to the [`timestamp`](TimestampChannel::timestamp) function.
    fn stop_capturing(&mut self, ppi_ch: &Channel) -> Result<(), Error>;

    /// Get the last captured timestamp (if any) in microseconds
    fn timestamp(&self) -> Result<Timestamp, Error>;
}

/// Capability of allocating channels capable of capturing timestamps of hardware events
pub trait Timestamper<'t> {
    /// Allocated channel type
    type Channel: TimestampChannel;

    /// Allocates a channel if one is free
    ///
    /// Bounds the lifetime of the allocator with the allocated channel. The channel cannot outlive
    /// the allocator.
    fn allocate_timestamp_channel(&'t self) -> Result<Self::Channel, Error>;
}

/// Capability of triggering hardware tasks
///
/// The tasks are triggered according to a freeruning timer synchronized with the freerunning
/// timers for other features of the [`Timer`] trait
pub trait TaskChannel {
    /// Prepare hardware to publish to a PPI channel at specified time
    ///
    /// At specified `time` this timer published to the passed PPI channel what triggers all tasks
    /// subscribing to this channel.
    fn trigger_at(&mut self, ppi_ch: &Channel, time: Timestamp) -> Result<(), Error>;

    /// Deconfigure hardware from publishing timer event to the passed PPI channel
    ///
    /// The passed `ppi_ch` must be the same that was passed to the
    /// [`trigger_at`](TaskChannel::trigger_at) method.
    /// The object implementing this trait does not keep reference to `ppi_ch` to avoid borrowing
    /// it while the timer is active.
    fn disable(&mut self, ppi_ch: &Channel) -> Result<(), Error>;
}

/// Capability of allocating channels capable of triggering hardware tasks
pub trait TaskTrigger<'t> {
    /// Allocated channel type
    type Channel: TaskChannel;

    /// Allocates a channel if one is free
    ///
    /// Bounds the lifetime of the allocator with the allocated channel. The channel cannot outlive
    /// the allocator.
    fn allocate_task_channel(&'t self) -> Result<Self::Channel, Error>;
}
