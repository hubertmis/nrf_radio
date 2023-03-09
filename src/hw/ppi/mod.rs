//! Portable PPI abstraction
//!
//! PPI is Programmable peripheral interconnect which allows multiple peripherals in SoC to trigger
//! tasks in other peripherals. Such tasks triggering has minimal latency with controllable jitter
//! and low power consumption, because it does not require CPU processing.
//!
//! This module is intended to be used by any other modules which require low latency direct
//! peripheral to peripheral communication

pub mod traits;

// TODO: is this a porting layer?
//       is such porting layer correct? the limitation would be that the whole software build
//       supports only one type of Ppi Channel and one type of an Allocator.
//       Let's leave it for now and see if we need more
#[cfg(any(all(feature = "mocked_platform", not(test)), feature = "nrf52840"))]
pub mod legacy_ppi;
/// Type of PPI channels allocator used in this build.
///
/// This type must implement [`Allocator`](traits::Allocator) trait.
#[cfg(any(all(feature = "mocked_platform", not(test)), feature = "nrf52840"))]
pub type Allocator = legacy_ppi::PpiAllocator;
#[cfg(all(test, feature = "mocked_platform"))]
pub type Allocator = traits::MockAllocator;
/// Type of PPI channel manager used in this build
///
/// This type must implement [`Channel`](traits::Channel) trait.
#[cfg(any(all(feature = "mocked_platform", not(test)), feature = "nrf52840"))]
pub type Channel = legacy_ppi::PpiChannel<'static>;
#[cfg(all(test, feature = "mocked_platform"))]
pub type Channel = traits::MockChannel;
