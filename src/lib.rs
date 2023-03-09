#![cfg_attr(not(any(test, doctest)), no_std)]
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
#![warn(rustdoc::missing_doc_code_examples)]

//! Radio protocols usage playground for Nordic nRF SoCs.
//!
//! Currently only physical layer of nRF52840 is supported, but this crate
//! is designed to be extensible for other protocols and other SoCs.

#[cfg(not(any(feature = "mocked_platform", feature = "nrf52840")))]
compile_error!("One platform must be enabled as a build feature");

#[cfg(all(feature = "mocked_platform", feature = "nrf52840"))]
compile_error!("Cannot enable multiple platforms simultaneously (mocked and nrf52840)");

#[cfg(all(test, not(feature = "mocked_platform")))]
compile_error!("For tests \"mocked_platform\" feature shall be selected");

// lazy_mut crate is used in tasklets tests
#[cfg(test)]
#[macro_use]
extern crate lazy_mut;

pub mod crit_sect; // Temporary pub, to support sharing tasklets
pub mod hw;
pub mod ieee802154;
pub mod mutex; // temporary pub, to support sharing tasklets
pub mod utils; // Temporary make utils public to allow simulating "higher layers" in external
               // crates

/// Defines errors reported by this crate
pub mod error;

/// Management of radio frames' buffers
pub mod frm_mem_mng;

/// Radio physical layer implementation for Nordic nRF SoCs.
///
/// Currently only nRF52840 is supported, but porting to other SoCs should be straightforward.
///
/// To use this module create an instance of [`Phy`](radio::Phy) and use methods of the created instance.
pub mod radio;
