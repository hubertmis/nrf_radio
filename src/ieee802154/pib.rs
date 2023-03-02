//! Protocol information base for IEEE 802.15.4

const EXT_ADDR_SIZE: usize = 8;
const SHORT_ADDR_SIZE: usize = 2;
const PANID_SIZE: usize = 2;

/// Protocol Information Base storage for IEEE 802.15.4
pub struct Pib {
    panid: [u8; PANID_SIZE],
    short_addr: [u8; SHORT_ADDR_SIZE],
    ext_addr: [u8; EXT_ADDR_SIZE],
}

impl Pib {
    /// Create empty PIB instance
    ///
    /// Empty PIB instance has addressing fields set to invalid (broadcast) values. The extended
    /// address is set to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::ieee802154::pib::Pib;
    ///
    /// let pib = Pib::new();
    /// ```
    pub const fn new() -> Self {
        Self {
            panid: [0xff, 0xff],
            short_addr: [0xff, 0xff],
            ext_addr: [0x0; EXT_ADDR_SIZE],
        }
    }

    /// Get Pan ID of this device
    ///
    /// The Pan ID value is little-endian.
    /// If Pan ID is not set, it contains broadcast value `[0xff, 0xff]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::ieee802154::pib::Pib;
    ///
    /// let pib = Pib::new();
    /// let pan_id = pib.get_pan_id();
    /// assert_eq!(pan_id, &[0xff, 0xff]);
    /// ```
    pub fn get_pan_id(&self) -> &[u8; PANID_SIZE] {
        &self.panid
    }

    /// Set Pan ID of this device
    ///
    /// The Pan ID value is little-endian.
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::ieee802154::pib::Pib;
    ///
    /// let mut pib = Pib::new();
    ///
    /// pib.set_pan_id(&[0x34, 0x12]);
    /// let pan_id = pib.get_pan_id();
    /// assert_eq!(pan_id, &[0x34, 0x12]);
    /// ```
    pub fn set_pan_id(&mut self, pan_id: &[u8; PANID_SIZE]) {
        self.panid = *pan_id;
    }

    /// Get short address of this device
    ///
    /// The address value is little-endian.
    /// If short address is not set, it contains broadcast value `[0xff, 0xff]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::ieee802154::pib::Pib;
    ///
    /// let pib = Pib::new();
    /// let short_addr = pib.get_short_addr();
    /// assert_eq!(short_addr, &[0xff, 0xff]);
    /// ```
    pub fn get_short_addr(&self) -> &[u8; SHORT_ADDR_SIZE] {
        &self.short_addr
    }

    /// Set short address of this device
    ///
    /// The address value is little-endian.
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::ieee802154::pib::Pib;
    ///
    /// let mut pib = Pib::new();
    ///
    /// pib.set_short_addr(&[0xcd, 0xab]);
    /// let short_addr = pib.get_short_addr();
    /// assert_eq!(short_addr, &[0xcd, 0xab]);
    /// ```
    pub fn set_short_addr(&mut self, short_addr: &[u8; SHORT_ADDR_SIZE]) {
        self.short_addr = *short_addr;
    }

    /// Get extended address of this device
    ///
    /// The address value is little-endian.
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::ieee802154::pib::Pib;
    ///
    /// let pib = Pib::new();
    /// let ext_addr = pib.get_short_addr();
    /// println!("Extended address: {:?}", ext_addr);
    /// ```
    pub fn get_ext_addr(&self) -> &[u8; EXT_ADDR_SIZE] {
        &self.ext_addr
    }

    /// Set extended address of this device
    ///
    /// The address value is little-endian.
    ///
    /// Extended address should be set to a correct value before the device starts operating. If
    /// user of this module fials to set the extended address value, it contains some default value
    /// which is most probably invalid for the device.
    ///
    /// # Examples
    ///
    /// ```
    /// use nrf_radio::ieee802154::pib::Pib;
    ///
    /// let mut pib = Pib::new();
    ///
    /// pib.set_ext_addr(&[0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01]);
    /// let ext_addr = pib.get_ext_addr();
    /// assert_eq!(ext_addr, &[0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01]);
    /// ```
    pub fn set_ext_addr(&mut self, ext_addr: &[u8; EXT_ADDR_SIZE]) {
        self.ext_addr = *ext_addr;
    }
}

impl Default for Pib {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_pan_id_is_broadcast() {
        let pib = Pib::new();
        assert_eq!(pib.get_pan_id(), &[0xff, 0xff]);
    }

    #[test]
    fn test_initial_short_addr_is_broadcast() {
        let pib = Pib::new();
        assert_eq!(pib.get_short_addr(), &[0xff, 0xff]);
    }

    #[test]
    fn test_pan_id_is_updateable() {
        let mut pib = Pib::new();
        let new_pan_id: [u8; 2] = [0x01, 0x23];
        pib.set_pan_id(&new_pan_id);
        assert_eq!(pib.get_pan_id(), &new_pan_id);
    }

    #[test]
    fn test_short_addr_is_updateable() {
        let mut pib = Pib::new();
        let new_short_addr: [u8; 2] = [0xcd, 0xef];
        pib.set_short_addr(&new_short_addr);
        assert_eq!(pib.get_short_addr(), &new_short_addr);
    }

    #[test]
    fn test_ext_addr_is_updateable() {
        let mut pib = Pib::new();
        let new_ext_addr: [u8; 8] = [0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef];
        pib.set_ext_addr(&new_ext_addr);
        assert_eq!(pib.get_ext_addr(), &new_ext_addr);
    }
}
