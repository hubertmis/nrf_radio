//! Filtering received frames

use super::super::frame::{Addr, Parser};
use super::super::pib::Pib;
use crate::error::Error;

const BROADCAST_PAN_ID: [u8; 2] = [0xff, 0xff];
const BROADCAST_SHORT_ADDR: [u8; 2] = [0xff, 0xff];

/// Capability of filtering received frames
pub trait RxFilter {
    /// Filters received frame according to IEEE 802.15.4 rules
    ///
    /// The FCF filtering is expected to be done by hardware accelerator and implemented in
    /// [`Phy`](crate::radio::Phy). Other filtering rules are implemented in this function.
    ///
    /// If the `frame` passes the filtering, method returns `Ok(())`. If not, it returns
    /// [`Err(Error)`](crate::error::Error) indicating which filter stopped the frame.
    fn filter_parsed_frame_part<F: Parser>(&self, frame: &F) -> Result<(), Error>;
}

/// Basic IEEE 802.15.4 frames filter
pub struct Filter<'f> {
    pib: &'f Pib,
}

impl<'f> Filter<'f> {
    /// Create a new filter
    ///
    /// A filter requires a reference to [`Pib`](super::pib::Pib) to get properties of this network
    /// node.
    pub fn new(pib: &'f Pib) -> Self {
        Self { pib }
    }

    fn filter_dst_pan_id<F: Parser>(&self, frame: &F) -> Result<(), Error> {
        let dst_pan_id = frame.dst_pan_id()?;
        if let Some(dst_pan_id) = dst_pan_id {
            if dst_pan_id != self.pib.get_pan_id() && dst_pan_id != &BROADCAST_PAN_ID {
                Err(Error::NotMatchingPanId)
            } else {
                Ok(())
            }
        } else {
            // TODO: Handle frames with missing dst pan id
            //       PAN coordinator property should be added?
            Err(Error::NotMatchingPanId)
        }
    }

    fn filter_dst_addr<F: Parser>(&self, frame: &F) -> Result<(), Error> {
        let dst_addr = frame.dst_address()?;
        if let Some(dst_addr) = dst_addr {
            match dst_addr {
                Addr::Short(addr) => {
                    if addr != self.pib.get_short_addr() && addr != &BROADCAST_SHORT_ADDR {
                        Err(Error::NotMatchingAddress)
                    } else {
                        Ok(())
                    }
                }
                Addr::Ext(addr) => {
                    if addr != self.pib.get_ext_addr() {
                        Err(Error::NotMatchingAddress)
                    } else {
                        Ok(())
                    }
                }
            }
        } else {
            // TODO: Handle frames with missing dst address
            //       PAN coordinator property should be added?
            Err(Error::NotMatchingAddress)
        }
    }
}

impl RxFilter for Filter<'_> {
    fn filter_parsed_frame_part<F: Parser>(&self, frame: &F) -> Result<(), Error> {
        self.filter_dst_pan_id(frame)?;
        self.filter_dst_addr(frame)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::frame::MockParser;
    use super::*;

    #[test]
    fn test_filter_frame_before_dst_pan_id_is_known() {
        let pib_mock = Pib::new();
        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .return_once(|| Err(Error::NotYetParsedField));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Err(Error::NotYetParsedField));
    }

    #[test]
    fn test_filter_frame_before_dst_addr_is_known() {
        static PAN_ID: Option<[u8; 2]> = Some([0x23, 0x01]);

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(PAN_ID.as_ref().unwrap());

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .return_once(|| Err(Error::NotYetParsedField));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Err(Error::NotYetParsedField));
    }

    #[test]
    fn test_filter_frame_with_unmatching_pan_id() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0x23, 0x00]);
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Err(Error::NotMatchingPanId));
    }

    #[test]
    fn test_filter_frame_with_matching_pan_id_and_broadcast_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0x23, 0x01]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Short([0xff, 0xff]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_filter_frame_with_broadcast_pan_id_and_matching_short_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0xff, 0xff]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Short([0xcd, 0xab]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_filter_frame_with_broadcast_pan_id_and_matching_ext_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0xff, 0xff]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Ext([
            0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01,
        ]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_filter_frame_with_broadcast_pan_id_and_unmatching_short_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0xff, 0xff]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Short([0xcd, 0xaa]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Err(Error::NotMatchingAddress));
    }

    #[test]
    fn test_filter_frame_with_broadcast_pan_id_and_unmatching_ext_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0xff, 0xff]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Ext([
            0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x00,
        ]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Err(Error::NotMatchingAddress));
    }

    #[test]
    fn test_filter_frame_with_broadcast_addresses() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0xff, 0xff]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Short([0xff, 0xff]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_filter_frame_with_matching_pan_id_and_matching_short_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0x23, 0x01]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Short([0xcd, 0xab]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_filter_frame_with_matching_pan_id_and_matching_ext_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0x23, 0x01]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Ext([
            0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01,
        ]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Ok(()));
    }

    #[test]
    fn test_filter_frame_with_matching_pan_id_and_unmatching_short_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0x23, 0x01]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Short([0xcd, 0xaa]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Err(Error::NotMatchingAddress));
    }

    #[test]
    fn test_filter_frame_with_matching_pan_id_and_unmatching_ext_address() {
        static RECEIVED_PAN_ID: Option<[u8; 2]> = Some([0x23, 0x01]);
        static RECEIVED_DST_ADDR: Option<Addr> = Some(Addr::Ext([
            0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x00,
        ]));
        let local_pan_id = [0x23u8, 0x01];
        let local_short_addr = [0xcdu8, 0xab];
        let local_ext_addr = [0xefu8, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01];

        let mut pib_mock = Pib::new();
        pib_mock.set_pan_id(&local_pan_id);
        pib_mock.set_short_addr(&local_short_addr);
        pib_mock.set_ext_addr(&local_ext_addr);

        let mut frame_mock = MockParser::new();
        frame_mock
            .expect_dst_pan_id()
            .times(1)
            .returning(|| Ok(&RECEIVED_PAN_ID));
        frame_mock
            .expect_dst_address()
            .times(1)
            .returning(|| Ok(&RECEIVED_DST_ADDR));

        let filter = Filter::new(&pib_mock);
        let result = filter.filter_parsed_frame_part(&frame_mock);
        assert_eq!(result, Err(Error::NotMatchingAddress));
    }
}
