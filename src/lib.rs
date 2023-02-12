#![cfg_attr(not(any(test, doctest)), no_std)]

//! Radio protocols usage playground for Nordic nRF SoCs.
//!
//! Currently only physical layer of nRF52840 is supported, but this crate
//! is designed to be extensible for other protocols and other SoCs.

mod crit_sect;
mod mutex;

/// Defines errors reported by this crate
pub mod error;

/// Management of radio frames' buffers
pub mod frame_buffer;

/// Radio physical layer implementation for Nordic nRF SoCs.
///
/// Currently only nRF52840 is supported, but porting to other SoCs should be straightforward.
///
/// To use this module create an instance of [`Phy`](radio::Phy) and use methods of the created instance.
pub mod radio;
