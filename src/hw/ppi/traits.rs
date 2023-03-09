//! Traits used for PPI modules portability
//!
//! Each port of PPI modules to other platform shall implement traits described in this module. The
//! one implementation of traits is selected in the [`ppi`](super) module.

use crate::error::Error;

#[cfg(test)]
use mockall::*;

/// Allocates channels used to connect peripherals' events with tasks
#[cfg_attr(test, automock)]
pub trait Allocator {
    /// Allocate new channel
    fn allocate_channel(&'static self) -> Result<super::Channel, Error>;
}

/// Channel capable of connecting peripherals' events with tasks
///
/// Events publish to this channel, while tasks subscribe to the channel.
///
/// TODO: How can I implement `Channel`?
///
/// TODO: Example publishing and subscribing?
#[cfg_attr(test, automock)]
pub trait Channel {
    /// Register an event to publish to this channel
    ///
    /// All events must be deregistered by user of this channel before the channel is dropped.
    ///
    /// TODO: Example
    fn publish_by<T: 'static>(&self, event_reg: *const T) -> Result<(), Error>;

    /// Deregister an event publishing to this channel
    ///
    /// TODO: Example
    fn stop_publishing_by<T: 'static>(&self, event_reg: *const T) -> Result<(), Error>;

    /// Register a task to subscribe to this channel
    ///
    /// All tasks must be deregistered by user of this channel before the channel is dropped.
    ///
    /// TODO: Example
    fn subscribe_by<T: 'static>(&self, task_reg: *const T) -> Result<(), Error>;

    /// Deregister a task subscribing to this channel
    ///
    /// TODO: Example
    fn stop_subscribing_by<T: 'static>(&self, task_reg: *const T) -> Result<(), Error>;

    /// Enable this channel
    ///
    /// When channel is enabled publishing events trigger subscribed tasks. Channel is disabled
    /// by default.
    ///
    /// TODO: Example
    fn enable(&self);

    /// Disable this channel
    ///
    /// Disabled channel does not trigger subscribed tasks.
    ///
    /// TODO: Example
    fn disable(&self);
}
