#![cfg_attr(not(any(test, doctest)), no_std)]
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
#![warn(rustdoc::missing_doc_code_examples)]

//! Radio protocols usage playground for Nordic nRF SoCs.
//!
//! Currently only physical layer of nRF52840 is supported, but this crate
//! is designed to be extensible for other protocols and other SoCs.

// lazy_mut crate is used in tasklets tests
#[cfg(test)]
#[macro_use]
extern crate lazy_mut;

mod crit_sect;
pub mod ieee802154;
mod mutex;
pub mod utils; // Temporary make utils public to suppress "not used" warnings

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
