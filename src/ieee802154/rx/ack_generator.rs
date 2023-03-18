//! Generator of acknowledgements
//!
//! Generate acknowledgement frames to be sent as responses to the received frames with the AR field set.

use super::super::frame::{Frame, Parser, Version};
use crate::error::Error;
use crate::frm_mem_mng::frame_allocator::FrameAllocator;
use crate::frm_mem_mng::frame_buffer::FrameBuffer;

/// Object capable of generating Acknowledgement frames
///
/// This object can generate Imm-Ack or Enh-Ack to match the IEEE 802.15.4 protocol specification.
pub struct AckGenerator<'ack_gen, FA: FrameAllocator> {
    frame_allocator: &'ack_gen FA,
}

impl<'ack_gen, FA: FrameAllocator> AckGenerator<'ack_gen, FA> {
    /// Create acknowledgements generator instance
    pub fn new(frame_allocator: &'ack_gen FA) -> Self {
        Self { frame_allocator }
    }

    /// Generate acknowledgement to be a response to the `received_frame`
    pub fn generate_ack_for(&self, received_frame: &Frame) -> Result<FrameBuffer<'static>, Error> {
        let ack_buffer = self.frame_allocator.get_frame()?;

        match &received_frame.version()? {
            Some(Version::V2003) | Some(Version::V2006) => {
                self.generate_imm_ack(received_frame, ack_buffer)
            }
            //Some(Version::V2015) => self.generate_enh_ack(received_frame, ack_buffer),
            Some(Version::V2015) => Err(Error::NotImplemented),
            // There is no frame that can request ack while not reporting its version
            None => Err(Error::InvalidFrame),
        }
    }

    fn generate_imm_ack<'fb>(
        &self,
        received_frame: &Frame,
        mut ack_frame: FrameBuffer<'fb>,
    ) -> Result<FrameBuffer<'fb>, Error> {
        let seq_num = received_frame
            .sequence_number()?
            .ok_or(Error::InvalidFrame)?;

        //let originator_addr = received_frame.src_addr()?;
        //let fp = self.is_frame_pending_for(originator_addr);
        let fp = false;
        let mhr0 = if fp { 0x12 } else { 0x02 };

        let ack_phr_and_psdu = [
            0x05u8, // PHR
            mhr0, 0x00,    // MHR
            seq_num, // Sequence Number
            0x00, 0x00, // MFR
        ];
        ack_frame[0..ack_phr_and_psdu.len()].clone_from_slice(&ack_phr_and_psdu);

        Ok(ack_frame)
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::frame::{Type, Version};
    use super::*;
    use crate::frm_mem_mng::mock_allocator::MockAllocator;

    #[test]
    fn test_generate_ack_to_2003_data_frame() {
        let ack_frame_allocator = MockAllocator::new();
        let received_frame = Frame::from_bytestring(&[
            16u8, // PHR
            0x61, 0x88, // FCF
            0xfe, // SeqNum
            0x4d, 0x48, // Dst Pan Id
            0x34, 0x12, // Dst Addr
            0xef, 0xcd, // Src Addr
            0x01, 0x02, 0x03, 0x04, 0x05, // Payload
            0x00, 0x00, // MFR
        ])
        .unwrap();

        let ack_generator = AckGenerator::new(&ack_frame_allocator);

        let ack_frame = ack_generator.generate_ack_for(&received_frame);
        let ack_frame = ack_frame.unwrap();

        let parsed_ack_frame = Frame::from_frame_buffer(&ack_frame).unwrap();
        assert_eq!(parsed_ack_frame.r#type(), Ok(&Type::Ack));
        assert_eq!(parsed_ack_frame.version(), Ok(&Some(Version::V2003)));
        assert_eq!(parsed_ack_frame.ar(), Ok(Some(false)));
        assert_eq!(parsed_ack_frame.sequence_number(), Ok(Some(0xfe)));
        assert_eq!(parsed_ack_frame.dst_pan_id(), Ok(&None));
        assert_eq!(parsed_ack_frame.dst_address(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_pan_id(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_address(), Ok(&None));
        //TODO: Verify there is no security
    }

    #[test]
    fn test_generate_ack_to_2006_data_frame() {
        let ack_frame_allocator = MockAllocator::new();
        let received_frame = Frame::from_bytestring(&[
            28u8, // PHR
            0x61, 0xdc, // FCF
            0x01, // SeqNum
            0x4d, 0x48, // Dst Pan Id
            0xf0, 0xde, 0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12, // Dst Addr
            0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01, // Src Addr
            0x01, 0x02, 0x03, 0x04, 0x05, // Payload
            0x00, 0x00, // MFR
        ])
        .unwrap();

        let ack_generator = AckGenerator::new(&ack_frame_allocator);

        let ack_frame = ack_generator.generate_ack_for(&received_frame);
        let ack_frame = ack_frame.unwrap();

        let parsed_ack_frame = Frame::from_frame_buffer(&ack_frame).unwrap();
        assert_eq!(parsed_ack_frame.r#type(), Ok(&Type::Ack));
        assert_eq!(parsed_ack_frame.version(), Ok(&Some(Version::V2003)));
        assert_eq!(parsed_ack_frame.ar(), Ok(Some(false)));
        assert_eq!(parsed_ack_frame.sequence_number(), Ok(Some(0x01)));
        assert_eq!(parsed_ack_frame.dst_pan_id(), Ok(&None));
        assert_eq!(parsed_ack_frame.dst_address(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_pan_id(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_address(), Ok(&None));
        //TODO: Verify there is no security
    }

    #[test]
    fn test_generate_ack_to_secured_2006_data_frame() {
        let ack_frame_allocator = MockAllocator::new();
        let received_frame = Frame::from_bytestring(&[
            22u8, // PHR
            0x69, 0x98, // FCF
            0xaa, // SeqNum
            0xde, 0xad, // Dst Pan Id
            0xbe, 0xef, // Dst Addr
            0xca, 0xfe, // Src Addr
            0x90, // Security Control
            0x01, 0x00, 0x00, 0x00, // Frame Counter
            0x02, // Key Index
            0x01, 0x02, 0x03, 0x04, 0x05, // Payload
            0x00, 0x00, // MFR
        ])
        .unwrap();

        let ack_generator = AckGenerator::new(&ack_frame_allocator);

        let ack_frame = ack_generator.generate_ack_for(&received_frame);
        let ack_frame = ack_frame.unwrap();

        let parsed_ack_frame = Frame::from_frame_buffer(&ack_frame).unwrap();
        assert_eq!(parsed_ack_frame.r#type(), Ok(&Type::Ack));
        assert_eq!(parsed_ack_frame.version(), Ok(&Some(Version::V2003)));
        assert_eq!(parsed_ack_frame.ar(), Ok(Some(false)));
        assert_eq!(parsed_ack_frame.sequence_number(), Ok(Some(0xaa)));
        assert_eq!(parsed_ack_frame.dst_pan_id(), Ok(&None));
        assert_eq!(parsed_ack_frame.dst_address(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_pan_id(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_address(), Ok(&None));
        //TODO: Verify there is no security
    }

    #[test]
    fn test_generate_ack_to_2006_data_frame_without_dst_addr() {
        let ack_frame_allocator = MockAllocator::new();
        let received_frame = Frame::from_bytestring(&[
            14u8, // PHR
            0x21, 0x90, // FCF
            0x55, // SeqNum
            0xde, 0xad, // Src Pan Id
            0xca, 0xfe, // Src Addr
            0x01, 0x02, 0x03, 0x04, 0x05, // Payload
            0x00, 0x00, // MFR
        ])
        .unwrap();

        let ack_generator = AckGenerator::new(&ack_frame_allocator);

        let ack_frame = ack_generator.generate_ack_for(&received_frame);
        let ack_frame = ack_frame.unwrap();

        let parsed_ack_frame = Frame::from_frame_buffer(&ack_frame).unwrap();
        assert_eq!(parsed_ack_frame.r#type(), Ok(&Type::Ack));
        assert_eq!(parsed_ack_frame.version(), Ok(&Some(Version::V2003)));
        assert_eq!(parsed_ack_frame.ar(), Ok(Some(false)));
        assert_eq!(parsed_ack_frame.sequence_number(), Ok(Some(0x55)));
        assert_eq!(parsed_ack_frame.dst_pan_id(), Ok(&None));
        assert_eq!(parsed_ack_frame.dst_address(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_pan_id(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_address(), Ok(&None));
        //TODO: Verify there is no security
    }

    #[test]
    fn test_generate_ack_to_2006_command_frame_without_src_addr() {
        let ack_frame_allocator = MockAllocator::new();
        let received_frame = Frame::from_bytestring(&[
            14u8, // PHR
            0x23, 0x18, // FCF
            0x00, // SeqNum
            0xde, 0xad, // Dst Pan Id
            0xca, 0xfe, // Dst Addr
            0x01, 0x02, 0x03, 0x04, 0x05, // Payload
            0x00, 0x00, // MFR
        ])
        .unwrap();

        let ack_generator = AckGenerator::new(&ack_frame_allocator);

        let ack_frame = ack_generator.generate_ack_for(&received_frame);
        let ack_frame = ack_frame.unwrap();

        let parsed_ack_frame = Frame::from_frame_buffer(&ack_frame).unwrap();
        assert_eq!(parsed_ack_frame.r#type(), Ok(&Type::Ack));
        assert_eq!(parsed_ack_frame.version(), Ok(&Some(Version::V2003)));
        assert_eq!(parsed_ack_frame.ar(), Ok(Some(false)));
        assert_eq!(parsed_ack_frame.sequence_number(), Ok(Some(0x00)));
        assert_eq!(parsed_ack_frame.dst_pan_id(), Ok(&None));
        assert_eq!(parsed_ack_frame.dst_address(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_pan_id(), Ok(&None));
        //assert_eq!(parsed_ack_frame.src_address(), Ok(&None));
        //TODO: Verify there is no security
    }

    #[test]
    fn test_cannot_generate_ack_to_multipurpose_frame_without_short_fcf() {
        let ack_frame_allocator = MockAllocator::new();
        let received_frame = Frame::from_bytestring(&[
            12u8, // PHR
            0xa5, // FCF
            0x11, // SeqNum
            0x54, 0x76, // Destination Address
            0x34, 0x12, // Source Address
            0x01, 0x23, 0x45, 0x67, // Payload
            0x00, 0x00, // MFR
        ])
        .unwrap();

        let ack_generator = AckGenerator::new(&ack_frame_allocator);

        let ack_frame = ack_generator.generate_ack_for(&received_frame);
        assert_eq!(ack_frame, Err(Error::InvalidFrame));
    }
}
