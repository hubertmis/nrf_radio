use crate::error::Error;
use crate::frm_mem_mng::frame_buffer::FrameBuffer;
use core::convert::TryFrom;

// TODO: Move constants to a common module?
const EXT_ADDR_SIZE: usize = 8;
const SHORT_ADDR_SIZE: usize = 2;
const PAN_ID_SIZE: usize = 2;

const PHR_OFFSET: usize = 0;
const PHR_SIZE: usize = 1;
const TYPE_OFFSET: usize = 1;
const FP_OFFSET: usize = 1;
const MP_FP_OFFSET: usize = 2;
const AR_OFFSET: usize = 1;
const MP_AR_OFFSET: usize = 2;
const SEQ_NUM_SUP_OFFSET: usize = 2;
const MP_SEQ_NUM_SUP_OFFSET: usize = 2;
const VERSION_OFFSET: usize = 2;
const MP_PAN_ID_PRESENT_OFFSET: usize = 2;
const DST_ADDR_MODE_OFFSET: usize = 2;
const MP_DST_ADDR_MODE_OFFSET: usize = 1;

const LONG_FRAME_CONTROL_OFFSET: usize = 1;
const LONG_FRAME_CONTROL_MASK: u8 = 0b00001000;

enum ParseStatus<T> {
    Unknown,
    Known(T),
}

/// Frame Types
///
/// Compliant with Table 7-1 in IEEE 802.15.4-2020
#[derive(Debug, Eq, PartialEq)]
pub enum Type {
    /// Beacon frame
    Beacon,
    /// Data frame
    Data,
    /// Acknowledgement frame
    ///
    /// Depending on the frame version this frame type represents immediate acknoledgement
    /// (Imm-Ack) or enhanced acknowledgement (Enh-Ack)
    Ack,
    /// MAC command frame
    Command,
    /// Multipurpose frame
    Multipurpose,
    /// Fragment pakcet or Frak frame
    Fragment,
    /// Extended frame
    ///
    /// This type is used to specify additional frame types by adding more bits to the Frame Type
    /// field. It is expected that this enum variant will be extended to represent more frame
    /// types.
    Extended,
}

impl TryFrom<&[u8]> for Type {
    type Error = Error;

    fn try_from(frame: &[u8]) -> Result<Self, Error> {
        if frame.len() <= TYPE_OFFSET {
            return Err(Error::WouldBlock);
        }

        match frame[TYPE_OFFSET] & 0b00000111 {
            0b000 => Ok(Type::Beacon),
            0b001 => Ok(Type::Data),
            0b010 => Ok(Type::Ack),
            0b011 => Ok(Type::Command),
            0b101 => Ok(Type::Multipurpose),
            0b110 => Ok(Type::Fragment),
            0b111 => Ok(Type::Extended),
            _ => Err(Error::InvalidFrame),
        }
    }
}

/// Frame Versions
///
/// Compliant with table 7-4 in IEEE 802.15.4-2020
/// The "IEEE Std 802.15.4" entries in the table are represented by `V2015` enumeration variant.
/// Other entries match the specification version present in given table entry.
#[derive(Debug, Eq, PartialEq)]
pub enum Version {
    /// "IEEE Std 802.15.4-2003" according to the table 7-4 in IEEE 802.15.4-2020
    V2003,
    /// "IEEE Std 802.15.4-2006" according to the table 7-4 in IEEE 802.15.4-2020
    V2006,
    /// "IEEE Std 802.15.4" according to the table 7-4 in IEEE 802.15.4-2020
    V2015,
}

impl Version {
    fn is_present(frame_type: &Type, buffer: &[u8]) -> Result<bool, Error> {
        match frame_type {
            Type::Beacon | Type::Data | Type::Ack | Type::Command => Ok(true),
            Type::Multipurpose => Frame::is_fcf_2bytes_long(buffer),
            Type::Fragment | Type::Extended => Ok(false),
        }
    }
}

impl TryFrom<&[u8]> for Version {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Error> {
        let r#type = Type::try_from(value)?;

        if Version::is_present(&r#type, value)? {
            if value.len() < VERSION_OFFSET {
                return Err(Error::WouldBlock);
            }

            match r#type {
                Type::Beacon | Type::Data | Type::Ack | Type::Command => {
                    match (value[VERSION_OFFSET] & 0b00110000) >> 4 {
                        0b00 => Ok(Version::V2003),
                        0b01 => Ok(Version::V2006),
                        0b10 => Ok(Version::V2015),
                        _ => Err(Error::InvalidFrame),
                    }
                }
                Type::Multipurpose => match (value[VERSION_OFFSET] & 0b00110000) >> 4 {
                    0b00 => Ok(Version::V2015),
                    _ => Err(Error::InvalidFrame),
                },
                Type::Fragment | Type::Extended => {
                    panic!("Shall not enter this branch, because Frame Version field is missing")
                }
            }
        } else {
            Err(Error::MissingField)
        }
    }
}

enum AddrMode {
    None,
    Short,
    Ext,
}

impl AddrMode {
    fn get_size(&self) -> usize {
        match self {
            AddrMode::None => 0,
            AddrMode::Short => SHORT_ADDR_SIZE,
            AddrMode::Ext => EXT_ADDR_SIZE,
        }
    }
}

impl TryFrom<u8> for AddrMode {
    type Error = Error;

    fn try_from(value: u8) -> Result<Self, Error> {
        match value & 0b00000011 {
            0b00 => Ok(AddrMode::None),
            0b10 => Ok(AddrMode::Short),
            0b11 => Ok(AddrMode::Ext),
            _ => Err(Error::InvalidFrame),
        }
    }
}

/// Frame address
///
/// Represents source or destination address of the frame.
/// Supports both short and extended addressing modes.
#[derive(Debug, Eq, PartialEq)]
pub enum Addr {
    /// Short address (16 bits)
    ///
    /// Keeps little-endian value (like a frame in the air).
    Short([u8; SHORT_ADDR_SIZE]),
    /// Extended address (64 bits)
    ///
    /// Keeps little-endian value (like a frame in the air).
    Ext([u8; EXT_ADDR_SIZE]),
}

/// IEEE 802.15.4 compliant frame
///
/// Contains fields of a IEEE 802.15.4 frame header.
/// This structure is intended to be used to retrieve fields from a frame buffer containing a raw
/// IEEE 802.15.4 frame.
pub struct Frame {
    parsed_bytes: usize,

    r#type: ParseStatus<Type>,
    frame_pending: ParseStatus<Option<bool>>,
    ar: ParseStatus<Option<bool>>,
    version: ParseStatus<Option<Version>>,

    seq_num: ParseStatus<Option<u8>>,

    dst_pan_id: ParseStatus<Option<[u8; PAN_ID_SIZE]>>,
    dst_addr: ParseStatus<Option<Addr>>,
    //src_pan_id: ParseStatus<Option<[u8; PAN_ID_SIZE]>>,
    //src_addr: ParseStatus<Option<Addr>>,
}

impl Default for Frame {
    fn default() -> Self {
        Self::new()
    }
}

impl Frame {
    /// Create an empty frame
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let frame = Frame::new();
    /// ```
    pub fn new() -> Self {
        Self {
            parsed_bytes: 0,
            r#type: ParseStatus::Unknown,
            version: ParseStatus::Unknown,
            frame_pending: ParseStatus::Unknown,
            ar: ParseStatus::Unknown,
            seq_num: ParseStatus::Unknown,
            dst_pan_id: ParseStatus::Unknown,
            dst_addr: ParseStatus::Unknown,
            //src_pan_id: ParseStatus::Unknown,
            //src_addr: ParseStatus::Unknown,
        }
    }

    /// Create a frame from a bytes slice
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let frame_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x98, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let frame = Frame::from_bytestring(&frame_bytes).unwrap();
    /// ```
    pub fn from_bytestring(bytestring: &[u8]) -> Result<Self, Error> {
        let mut frame = Self::new();
        frame.parse(bytestring)?;

        Ok(frame)
    }

    /// Create a frame from a [`FrameBuffer`]
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::frm_mem_mng::frame_buffer::FrameBuffer;
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let mut frame_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x98, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///   let frame_buffer = FrameBuffer::new(&mut frame_bytes, None, &None::<usize>);
    ///
    ///   let frame = Frame::from_frame_buffer(&frame_buffer).unwrap();
    /// ```
    pub fn from_frame_buffer(buffer: &FrameBuffer) -> Result<Self, Error> {
        let mut frame = Self::new();
        frame.parse(buffer)?;

        Ok(frame)
    }

    /// Get type of given frame
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::{Frame, Type};
    ///
    ///   let data_frame_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x98, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///   let ack_bytes = [
    ///       5u8,        // PHR
    ///       0x02, 0x00, // FCF
    ///       0x5e,       // SeqNum
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let data_frame = Frame::from_bytestring(&data_frame_bytes).unwrap();
    ///   let ack_frame = Frame::from_bytestring(&ack_bytes).unwrap();
    ///
    ///   assert_eq!(data_frame.get_type(), Ok(&Type::Data));
    ///   assert_eq!(ack_frame.get_type(), Ok(&Type::Ack));
    /// ```
    pub fn get_type(&self) -> Result<&Type, Error> {
        match &self.r#type {
            ParseStatus::Unknown => Err(Error::NotYetParsedField),
            ParseStatus::Known(r#type) => Ok(r#type),
        }
    }

    /// Get value of the Frame Pending field
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let ack_no_frame_pending_bytes = [
    ///       5u8,        // PHR
    ///       0x02, 0x00, // FCF
    ///       0x5e,       // SeqNum
    ///       0x00, 0x00, // MFR
    ///   ];
    ///   let ack_frame_pending_bytes = [
    ///       5u8,        // PHR
    ///       0x12, 0x00, // FCF
    ///       0x5e,       // SeqNum
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let no_fp_frame = Frame::from_bytestring(&ack_no_frame_pending_bytes).unwrap();
    ///   let fp_frame = Frame::from_bytestring(&ack_frame_pending_bytes).unwrap();
    ///
    ///   assert_eq!(no_fp_frame.get_frame_pending(), Ok(Some(false)));
    ///   assert_eq!(fp_frame.get_frame_pending(), Ok(Some(true)));
    /// ```
    pub fn get_frame_pending(&self) -> Result<Option<bool>, Error> {
        match self.frame_pending {
            ParseStatus::Unknown => Err(Error::NotYetParsedField),
            ParseStatus::Known(fp) => Ok(fp),
        }
    }

    /// Get value of the AR field
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let unicast_data_frame_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x98, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///   let broadcast_data_frame_bytes = [
    ///       16u8, // PHR
    ///       0x41, 0x98, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let unicast_frame = Frame::from_bytestring(&unicast_data_frame_bytes).unwrap();
    ///   let broadcast_frame = Frame::from_bytestring(&broadcast_data_frame_bytes).unwrap();
    ///
    ///   assert_eq!(unicast_frame.get_ar(), Ok(Some(true)));
    ///   assert_eq!(broadcast_frame.get_ar(), Ok(Some(false)));
    /// ```
    pub fn get_ar(&self) -> Result<Option<bool>, Error> {
        match self.ar {
            ParseStatus::Unknown => Err(Error::NotYetParsedField),
            ParseStatus::Known(ar) => Ok(ar),
        }
    }

    /// Get value of the Frame Version field
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::{Frame, Version};
    ///
    ///   let data_2003_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x88, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///   let data_2006_bytes = [
    ///       20u8, // PHR
    ///       0x69, 0x98, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01,       // Security Control
    ///       0x01, 0x00, 0x00, 0x00, // Frame Counter
    ///       0x01, 0x02, 0x03, 0x04, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///   let data_2015_bytes = [
    ///       16u8, // PHR
    ///       0x69, 0xa9, // FCF
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x61,       // Security Control
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let frame_2003 = Frame::from_bytestring(&data_2003_bytes).unwrap();
    ///   let frame_2006 = Frame::from_bytestring(&data_2006_bytes).unwrap();
    ///   let frame_2015 = Frame::from_bytestring(&data_2015_bytes).unwrap();
    ///
    ///   assert_eq!(frame_2003.get_version(), Ok(&Some(Version::V2003)));
    ///   assert_eq!(frame_2006.get_version(), Ok(&Some(Version::V2006)));
    ///   assert_eq!(frame_2015.get_version(), Ok(&Some(Version::V2015)));
    /// ```
    pub fn get_version(&self) -> Result<&Option<Version>, Error> {
        match &self.version {
            ParseStatus::Unknown => Err(Error::NotYetParsedField),
            ParseStatus::Known(version) => Ok(version),
        }
    }

    /// Get Sequence Number value
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let frame_with_seq_num_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x88, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///   let frame_without_seq_num_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0xa9, // FCF
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, 0x06, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let frame_with_seq_num = Frame::from_bytestring(&frame_with_seq_num_bytes).unwrap();
    ///   let frame_without_seq_num = Frame::from_bytestring(&frame_without_seq_num_bytes).unwrap();
    ///
    ///   assert_eq!(frame_with_seq_num.get_sequence_number(), Ok(Some(0x5e)));
    ///   assert_eq!(frame_without_seq_num.get_sequence_number(), Ok(None));
    /// ```
    pub fn get_sequence_number(&self) -> Result<Option<u8>, Error> {
        match self.seq_num {
            ParseStatus::Unknown => Err(Error::NotYetParsedField),
            ParseStatus::Known(seq_num) => Ok(seq_num),
        }
    }

    /// Get Destination PAN Id
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let frame_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x88, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let frame = Frame::from_bytestring(&frame_bytes).unwrap();
    ///
    ///   assert_eq!(frame.get_dst_pan_id(), Ok(&Some([0x4du8, 0x48])));
    /// ```
    pub fn get_dst_pan_id(&self) -> Result<&Option<[u8; PAN_ID_SIZE]>, Error> {
        match &self.dst_pan_id {
            ParseStatus::Unknown => Err(Error::NotYetParsedField),
            ParseStatus::Known(pan_id) => Ok(pan_id),
        }
    }

    /// Get Destination Address
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::ieee802154::frame::{Addr, Frame};
    ///
    ///   let frame_with_extended_dst_addr_bytes = [
    ///       22u8, // PHR
    ///       0x61, 0x8c, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///   let frame_with_short_dst_addr_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x88, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let extended_addr_frame = Frame::from_bytestring(&frame_with_extended_dst_addr_bytes).unwrap();
    ///   let short_addr_frame = Frame::from_bytestring(&frame_with_short_dst_addr_bytes).unwrap();
    ///
    ///   assert_eq!(extended_addr_frame.get_dst_address(), Ok(&Some(Addr::Ext(
    ///           [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01]))));
    ///   assert_eq!(short_addr_frame.get_dst_address(), Ok(&Some(Addr::Short([0x34u8, 0x12]))));
    /// ```
    pub fn get_dst_address(&self) -> Result<&Option<Addr>, Error> {
        match &self.dst_addr {
            ParseStatus::Unknown => Err(Error::NotYetParsedField),
            ParseStatus::Known(addr) => Ok(addr),
        }
    }

    /// Parse a bytestring as a IEEE 802.15.4 frame
    ///
    /// Full content of the frame must be available.
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::error::Error;
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let frame_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x88, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let mut frame = Frame::new();
    ///
    ///   let result = frame.parse(&frame_bytes);
    ///   assert!(result.is_ok());
    ///
    ///   let result = frame.parse(&frame_bytes[0..3]);
    ///   assert_eq!(result, Err(Error::InvalidFrame));
    /// ```
    pub fn parse(&mut self, buffer: &[u8]) -> Result<(), Error> {
        if buffer.is_empty() {
            return Err(Error::WouldBlock);
        }
        let parsed_len = self.parse_available_part(buffer)?;

        if parsed_len == buffer.len() && parsed_len == Frame::len(buffer) + 1 {
            Ok(())
        } else {
            Err(Error::InvalidFrame)
        }
    }

    /// Parse a bytestring containing a part of IEEE 802.15.4 frame
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::error::Error;
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let frame_bytes = [
    ///       16u8, // PHR
    ///       0x61, 0x88, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0x34, 0x12, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   let mut frame = Frame::new();
    ///
    ///   let result = frame.parse_available_part(&frame_bytes[0..3]);
    ///   assert!(result.is_ok());
    ///
    ///   assert_eq!(frame.get_ar(), Ok(Some(true)));
    ///   assert_eq!(frame.get_sequence_number(), Err(Error::NotYetParsedField));
    /// ```
    pub fn parse_available_part(&mut self, frame_part: &[u8]) -> Result<usize, Error> {
        if frame_part.is_empty() {
            return Err(Error::WouldBlock);
        }
        if Frame::len(frame_part) <= self.parsed_bytes {
            return Err(Error::InvalidFrame);
        }
        if frame_part.len() > Frame::len(frame_part) + PHR_SIZE {
            return Err(Error::InvalidFrame);
        }

        let parse_fns = [
            Frame::parse_fcf,
            Frame::parse_seq_num,
            Frame::parse_dst_pan_id,
            Frame::parse_dst_addr,
        ];
        for parse_fn in parse_fns {
            // TODO: skip already parsed fns
            match parse_fn(self, frame_part) {
                Ok(parsed_bytes) => self.parsed_bytes = parsed_bytes,
                Err(Error::WouldBlock) => return Ok(self.parsed_bytes),
                Err(e) => return Err(e),
            }
        }

        Ok(frame_part.len())
        //Ok(self.parsed_bytes)
    }

    /// Get length of the frame indicated by PHR
    /// ```
    ///   use nrf_radio::ieee802154::frame::Frame;
    ///
    ///   let data_frame_bytes = [
    ///       22u8, // PHR
    ///       0x61, 0x8c, // FCF
    ///       0x5e, // SeqNum
    ///       0x4d, 0x48, // Dst Pan Id
    ///       0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01, // Dst Addr
    ///       0xef, 0xcd, // Src Addr
    ///       0x01, 0x02, 0x03, 0x04, 0x05, // Payload
    ///       0x00, 0x00, // MFR
    ///   ];
    ///
    ///   //assert_eq!(Frame::len(&data_frame_bytes), 22);
    /// ```
    fn len(buffer: &[u8]) -> usize {
        buffer[PHR_OFFSET].into()
    }

    fn parse_fcf(&mut self, frame: &[u8]) -> Result<usize, Error> {
        self.r#type = ParseStatus::Known(Type::try_from(frame)?);
        self.frame_pending = ParseStatus::Known(Frame::is_frame_pending_set(frame)?);
        self.ar = ParseStatus::Known(Frame::is_ar_set(frame)?);
        self.version = match Version::try_from(frame) {
            Ok(version) => ParseStatus::Known(Some(version)),
            Err(Error::MissingField) => ParseStatus::Known(None),
            Err(error) => return Err(error),
        };

        Frame::get_seq_num_offset(frame)
    }

    fn parse_seq_num(&mut self, frame: &[u8]) -> Result<usize, Error> {
        self.seq_num = ParseStatus::Known(if Frame::is_seq_num_present(frame)? {
            Some(Frame::get_byte(frame, Frame::get_seq_num_offset(frame)?)?)
        } else {
            None
        });

        Frame::get_addressing_offset(frame)
    }

    fn parse_dst_pan_id(&mut self, frame: &[u8]) -> Result<usize, Error> {
        self.dst_pan_id = ParseStatus::Known(if Frame::is_dst_pan_id_present(frame)? {
            let pan_id_slice = &frame[Frame::get_dst_pan_id_offset(frame)?..];
            let pan_id_array: [u8; PAN_ID_SIZE] = pan_id_slice[..PAN_ID_SIZE].try_into().unwrap();
            Some(pan_id_array)
        } else {
            None
        });

        Frame::get_dst_addr_offset(frame)
    }

    fn parse_dst_addr(&mut self, frame: &[u8]) -> Result<usize, Error> {
        self.dst_addr = ParseStatus::Known(match Frame::get_dst_addr_mode(frame)? {
            AddrMode::None => None,
            AddrMode::Short => {
                const SIZE: usize = SHORT_ADDR_SIZE;
                let addr_slice = &frame[Frame::get_dst_addr_offset(frame)?..];
                let addr_array: [u8; SIZE] = addr_slice[..SIZE].try_into().unwrap();
                Some(Addr::Short(addr_array))
            }
            AddrMode::Ext => {
                const SIZE: usize = EXT_ADDR_SIZE;
                let addr_slice = &frame[Frame::get_dst_addr_offset(frame)?..];
                let addr_array: [u8; SIZE] = addr_slice[..SIZE].try_into().unwrap();
                Some(Addr::Ext(addr_array))
            }
        });

        Frame::get_src_pan_id_offset(frame)
    }

    fn is_frame_pending_set(frame: &[u8]) -> Result<Option<bool>, Error> {
        if Frame::is_fcf_2bytes_long(frame)? {
            match Type::try_from(frame)? {
                Type::Beacon | Type::Data | Type::Ack | Type::Command => {
                    Ok(Some((Frame::get_byte(frame, FP_OFFSET)? & 0b00010000) != 0))
                }
                Type::Multipurpose => Ok(Some(
                    (Frame::get_byte(frame, MP_FP_OFFSET)? & 0b00001000) != 0,
                )),
                _ => Err(Error::NotImplemented),
            }
        } else {
            Ok(None)
        }
    }

    fn is_ar_set(frame: &[u8]) -> Result<Option<bool>, Error> {
        if Frame::is_fcf_2bytes_long(frame)? {
            match Type::try_from(frame)? {
                Type::Beacon | Type::Data | Type::Ack | Type::Command => {
                    Ok(Some((Frame::get_byte(frame, AR_OFFSET)? & 0b00100000) != 0))
                }
                Type::Multipurpose => Ok(Some(
                    (Frame::get_byte(frame, MP_AR_OFFSET)? & 0b01000000) != 0,
                )),
                _ => Err(Error::NotImplemented),
            }
        } else {
            Ok(None)
        }
    }

    fn is_seq_num_present(frame: &[u8]) -> Result<bool, Error> {
        match Type::try_from(frame)? {
            Type::Beacon | Type::Data | Type::Ack | Type::Command => {
                Ok((Frame::get_byte(frame, SEQ_NUM_SUP_OFFSET)? & 0b00000001) == 0)
            }
            Type::Multipurpose => {
                Ok((Frame::get_byte(frame, MP_SEQ_NUM_SUP_OFFSET)? & 0b00000100) == 0)
            }
            Type::Extended | Type::Fragment => Ok(false),
        }
    }

    fn is_dst_pan_id_present(frame: &[u8]) -> Result<bool, Error> {
        match Type::try_from(frame)? {
            Type::Beacon | Type::Data | Type::Ack | Type::Command => {
                match Version::try_from(frame)? {
                    Version::V2003 | Version::V2006 => match Frame::get_dst_addr_mode(frame)? {
                        AddrMode::None => Ok(false),
                        AddrMode::Ext | AddrMode::Short => Ok(true),
                    },
                    Version::V2015 => {
                        // TODO: follow table 7-2
                        Ok(false)
                    }
                }
            }
            Type::Multipurpose => {
                if Frame::is_fcf_2bytes_long(frame)? {
                    Ok((Frame::get_byte(frame, MP_PAN_ID_PRESENT_OFFSET)? & 0b00000001) == 0)
                } else {
                    Ok(false)
                }
            }
            Type::Extended | Type::Fragment => Ok(false),
        }
    }

    fn get_dst_addr_mode(frame: &[u8]) -> Result<AddrMode, Error> {
        match Type::try_from(frame)? {
            Type::Beacon | Type::Data | Type::Ack | Type::Command => Ok(AddrMode::try_from(
                (Frame::get_byte(frame, DST_ADDR_MODE_OFFSET)? & 0b00001100) >> 2,
            )?),
            Type::Multipurpose => Ok(AddrMode::try_from(
                (Frame::get_byte(frame, MP_DST_ADDR_MODE_OFFSET)? & 0b00110000) >> 4,
            )?),
            Type::Extended | Type::Fragment => Ok(AddrMode::None),
        }
    }

    fn get_seq_num_offset(frame: &[u8]) -> Result<usize, Error> {
        let phr_len = 1;
        let fcf_len = if Frame::is_fcf_2bytes_long(frame)? {
            2
        } else {
            1
        };

        Ok(phr_len + fcf_len)
    }

    fn get_addressing_offset(frame: &[u8]) -> Result<usize, Error> {
        let seq_num_len = if Frame::is_seq_num_present(frame)? {
            1
        } else {
            0
        };

        Ok(Frame::get_seq_num_offset(frame)? + seq_num_len)
    }

    fn get_dst_pan_id_offset(frame: &[u8]) -> Result<usize, Error> {
        Frame::get_addressing_offset(frame)
    }

    fn get_dst_addr_offset(frame: &[u8]) -> Result<usize, Error> {
        let dst_pan_id_len = if Frame::is_dst_pan_id_present(frame)? {
            PAN_ID_SIZE
        } else {
            0
        };

        Ok(Frame::get_dst_pan_id_offset(frame)? + dst_pan_id_len)
    }

    fn get_src_pan_id_offset(frame: &[u8]) -> Result<usize, Error> {
        let dst_addr_len = Frame::get_dst_addr_mode(frame)?.get_size();

        Ok(Frame::get_dst_addr_offset(frame)? + dst_addr_len)
    }

    fn is_fcf_2bytes_long(frame: &[u8]) -> Result<bool, Error> {
        match Type::try_from(frame)? {
            Type::Beacon | Type::Data | Type::Ack | Type::Command => Ok(true),
            Type::Multipurpose => Ok((Frame::get_byte(frame, LONG_FRAME_CONTROL_OFFSET)?
                & LONG_FRAME_CONTROL_MASK)
                != 0),
            Type::Extended | Type::Fragment => Ok(false),
        }
    }

    fn get_byte(frame: &[u8], offset: usize) -> Result<u8, Error> {
        if Frame::is_byte_available(frame, offset) {
            Ok(frame[offset])
        } else {
            Err(Error::WouldBlock)
        }
    }

    /*
    fn get_slice(frame: &[u8], start: usize, end_exclusive: usize) -> Result<&[u8], Error> {
        if end_exclusive == 0 {
            return Err(Error::InvalidArgument);
        }

        if Frame::is_byte_available(frame, end_exclusive - 1) {
            Ok(&frame[start..end_exclusive])
        } else {
            Err(Error::WouldBlock)
        }
    }
    */

    fn is_byte_available(frame: &[u8], offset: usize) -> bool {
        frame.len() > offset
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn buffer_from_frame(frame: &mut [u8]) -> FrameBuffer {
        FrameBuffer::new(frame, None, &None::<usize>)
    }

    #[test]
    fn test_parse_broadcast_frame() {
        let frame_data = &mut [
            16u8, // PHR
            0x41, 0x98, // FCF
            0x5e, // SeqNum
            0x01, 0x23, // Dst Pan Id
            0xff, 0xff, // Dst Addr
            0xcd, 0xef, // Src Addr
            0x01, 0x02, 0x03, 0x04, 0x05, // Payload
            0x00, 0x00, // MFR
        ];
        let buffer = buffer_from_frame(frame_data);
        let frame = Frame::from_frame_buffer(&buffer).unwrap();

        assert_eq!(frame.get_type(), Ok(&Type::Data));
        assert_eq!(frame.get_frame_pending(), Ok(Some(false)));
        assert_eq!(frame.get_ar(), Ok(Some(false)));
        assert_eq!(frame.get_version(), Ok(&Some(Version::V2006)));
        assert_eq!(frame.get_sequence_number(), Ok(Some(0x5e)));
        assert_eq!(frame.get_dst_pan_id(), Ok(&Some([0x01u8, 0x23])));
        assert_eq!(
            frame.get_dst_address(),
            Ok(&Some(Addr::Short([0xff, 0xff])))
        );
        //assert_eq!(frame.get_src_pan_id(), Ok(&Some([0x01u8, 0x23])));
    }

    #[test]
    fn test_parse_unicast_frame() {
        let frame_data = &mut [
            16u8, // PHR
            0x61, 0x98, // FCF
            0xff, // SeqNum
            0xfe, 0xde, // Dst Pan Id
            0x00, 0xaa, // Dst Addr
            0xfe, 0x01, // Src Addr
            0x01, 0x02, 0x03, 0x04, 0x05, // Payload
            0x00, 0x00, // MFR
        ];
        let buffer = buffer_from_frame(frame_data);
        let frame = Frame::from_frame_buffer(&buffer).unwrap();

        assert_eq!(frame.get_type(), Ok(&Type::Data));
        assert_eq!(frame.get_frame_pending(), Ok(Some(false)));
        assert_eq!(frame.get_ar(), Ok(Some(true)));
        assert_eq!(frame.get_version(), Ok(&Some(Version::V2006)));
        assert_eq!(frame.get_sequence_number(), Ok(Some(0xff)));
        assert_eq!(frame.get_dst_pan_id(), Ok(&Some([0xfeu8, 0xde])));
        assert_eq!(
            frame.get_dst_address(),
            Ok(&Some(Addr::Short([0x00, 0xaa])))
        );
        //assert_eq!(frame.get_src_pan_id(), Ok(&Some([0x01u8, 0x23])));
    }

    #[test]
    fn test_parse_extended_addresses_in_frame() {
        let frame_data = &mut [
            28u8, // PHR
            0x61, 0xdc, // FCF
            0x00, // SeqNum
            0x00, 0x01, // Dst Pan Id
            0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef, // Dst Addr
            0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10, // Src Addr
            0x01, 0x02, 0x03, 0x04, 0x05, // Payload
            0x00, 0x00, // MFR
        ];
        let buffer = buffer_from_frame(frame_data);
        let frame = Frame::from_frame_buffer(&buffer).unwrap();

        assert_eq!(frame.get_type(), Ok(&Type::Data));
        assert_eq!(frame.get_frame_pending(), Ok(Some(false)));
        assert_eq!(frame.get_ar(), Ok(Some(true)));
        assert_eq!(frame.get_version(), Ok(&Some(Version::V2006)));
        assert_eq!(frame.get_sequence_number(), Ok(Some(0x00)));
        assert_eq!(frame.get_dst_pan_id(), Ok(&Some([0x00u8, 0x01])));
        assert_eq!(
            frame.get_dst_address(),
            Ok(&Some(Addr::Ext([
                0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef
            ])))
        );
        //assert_eq!(frame.get_src_pan_id(), Ok(&Some([0x01u8, 0x23])));
    }

    #[test]
    fn test_parse_ack_frame() {
        let frame_data = &mut [
            5u8, // PHR
            0x02, 0x00, // FCF
            0x5e, // SeqNum
            0x00, 0x00, // MFR
        ];
        let buffer = buffer_from_frame(frame_data);
        let frame = Frame::from_frame_buffer(&buffer).unwrap();

        assert_eq!(frame.get_type(), Ok(&Type::Ack));
        assert_eq!(frame.get_frame_pending(), Ok(Some(false)));
        assert_eq!(frame.get_ar(), Ok(Some(false)));
        assert_eq!(frame.get_version(), Ok(&Some(Version::V2003)));
        assert_eq!(frame.get_sequence_number(), Ok(Some(0x5e)));
        assert_eq!(frame.get_dst_pan_id(), Ok(&None));
        assert_eq!(frame.get_dst_address(), Ok(&None));
        //assert_eq!(frame.get_src_pan_id(), Ok(&Some([0x01u8, 0x23])));
    }
}
