//! Features specific to IEEE 802.15.4 MAC

/// Module responsible for parsing and building IEEE 802.15.4 frames
pub mod frame;

/// Module responsible for storing Protocol Information Base
///
/// Protocol Information Base includes run-time configuration of both PHY and MAC layers of
/// IEEE 802.15.4
pub mod pib;
