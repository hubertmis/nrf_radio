/// Errors reported by radio software
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    /// The module is busy with ongoing operation
    WouldBlock,
    /// The passed buffer cannot contain all necessary data
    TooSmallBuffer,
    /// The channel number is out of range for selected Phy
    InvalidChannel,
    /// The CRC value in the received frame is invalid
    IncorrectCrc,
}
