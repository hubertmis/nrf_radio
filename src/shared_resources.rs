//! Container for resources shared between radio operation with time slicing

use crate::hw::ppi::Channel as PpiChannel;
use crate::hw::timer::traits::{TaskTrigger, Timestamper};
use crate::hw::timer::Timer;
use crate::radio::Phy;

const NUM_PPI_CHANNELS: usize = 1;

/// Structure containing the resources which are shared between radio operations with time slicing
///
/// Time slicing radio operations allow to run multiple radio operations one by one, what allows to
/// run multiple modes of a radio protocol, or event multiple protocols in parallel, using a shared
/// set of hardware resources.
///
/// This approach requires a scheduler or an arbiter deciding when which of the radio operations
/// gets access to the shared resources.
///
/// This structure allows access to the set of resources being shared. For efficiency, it is
/// intended to be allocated statically and passed around radio operations as `&mut
/// TimeSlicedResources` to avoid copying its content.
pub struct TimeSlicedResources<'a> {
    /// Radio's physical layer
    pub phy: Phy,

    /// A set of PPIs
    pub ppi_channels: [Option<PpiChannel>; NUM_PPI_CHANNELS],

    /// Timer used to schedule PPIs
    pub timer_task_channel: <Timer as TaskTrigger<'a>>::Channel,

    /// Timer used to capture PPI timestamps
    pub timestamp_channel: <Timer as Timestamper<'a>>::Channel,

    /// Timer used to check current time or if a timestamp already passed
    ///
    /// TODO: Move it out of this list, as this operation can be done outside of timestamps. Also
    /// scheduling software callbacks does not require `&mut` to a timer instance, so it can be
    /// shared between radio operations constantly, instead of using time slicing.
    pub timestamp_timer: Timer,
    // TODO: should critical section be distributed only as a shared resource?
    //       probably not, because some operations like ordering a linked list must be done outside
    //       of a time slice
}
