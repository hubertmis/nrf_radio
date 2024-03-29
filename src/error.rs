/// Errors reported by radio software
#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    /// The module is busy with ongoing operation
    WouldBlock,
    /// Not enough available memory
    NoMemory,
    /// No free resources
    NoResources,
    /// Requested resource already taken
    AlreadyTaken,
    /// The passed buffer cannot contain all necessary data
    TooSmallBuffer,
    /// The received frame is invalid
    InvalidFrame,
    /// The requested field was not parsed yet
    NotYetParsedField,
    /// The requested field is missing
    MissingField,
    /// The frame is destined to other Pan ID than this node belongs to
    NotMatchingPanId,
    /// The frame is destined to other address than this node's
    NotMatchingAddress,
    /// The channel number is out of range for selected Phy
    InvalidChannel,
    /// The CRC value in the received frame is invalid
    IncorrectCrc,

    /// Passed argument makes no sense
    InvalidArgument,
    /// Feature not yet implemented
    NotImplemented,
}
