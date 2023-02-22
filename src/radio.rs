use crate::error::Error;
use crate::mutex::Mutex;
use core::any::Any;
use core::cell::RefCell;
use core::ops::Deref;

use crate::frm_mem_mng::frame_buffer::FrameBuffer;

// Port to nRF52840
use nrf52840_hal::pac::radio;
type RadioRegisterBlock = radio::RegisterBlock;

//// Radio Periph Wrapper
//// It is a structure allowing testability of the Phy structure. It allows overriding
//// RADIO peripheral memory space with arbitrary selected memory space (like an array)
//// in unit tests running on a host PC.
unsafe impl Send for RadioPeriphWrapper {} // Is this really safe considering it's just pointer
                                           // dereference?
struct RadioPeriphWrapper {
    ptr: *const RadioRegisterBlock,
}
impl RadioPeriphWrapper {
    pub fn new(radio: &RadioRegisterBlock) -> Self {
        RadioPeriphWrapper { ptr: radio }
    }
}
impl Deref for RadioPeriphWrapper {
    type Target = RadioRegisterBlock;
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.ptr }
    }
}

// TODO: shorter lifetime than static. Is it possible?
//       Maybe it requires FSM refactoring to change FSM type on the fly?
/// Reference to any data selected by a requester
///
/// The same reference is passed in a callback function when the requested operation is completed.
pub type Context = &'static (dyn Any + Send + Sync);

/// Type of the callback function called when the requested TX operation is completed
pub type TxCallback = fn(Result<(), Error>, Context);

/// Internal data required in the TX state
struct TxData {
    callback: TxCallback,
    context: Context,
}

/// Data and metadata of the correctly received frame
#[derive(Debug, PartialEq)]
pub struct RxOk {
    /// Reference to the content of the received frame
    ///
    /// For IEEE 802.15.4 this buffer contains PHR and PSDU of the received frame, where MFR might
    /// be malformed
    pub frame: FrameBuffer<'static>,
}

/// Type of the callback function called when the requested RX operation is completed
pub type RxCallback = fn(Result<RxOk, Error>, Context);

/// Internal data required in the RX state
struct RxData {
    callback: RxCallback,
    context: Context,
    rx_buffer: FrameBuffer<'static>,
}

/// The state of the software PHY FSM
enum State {
    // In Idle state RADIO is being disabled (RXDISABLE, TXDISABLE) or already disabled (DISABLED).
    // The INTEN register is cleared. The SHORTS, PACKETPTR, EVENTS_ are undefined (expected to be
    // overriden when entering the next state).
    Idle,
    Tx(TxData),
    Rx(RxData),
}

/// Data accessible by an ISR
struct IsrData {
    radio: RadioPeriphWrapper,
    state: State,
}

// RefCell is required to verify run-time if critical sections work as expected
// There is only one ISR_DATA instance, because there is only one ISR handler. This instance should
// be multiplied (an array) if there were more peripheral instances (implying more ISRs) to handle.
static ISR_DATA: Mutex<RefCell<Option<IsrData>>> = Mutex::new(RefCell::new(None));

/// Macro used to build tests on a host
///
/// It is used for unit tests and doctest targets
#[doc(hidden)]
#[macro_export]
macro_rules! missing_test_fns {
    () => {
        #[no_mangle]
        pub extern "C" fn __primask_r() -> u32 {
            0
        }

        #[no_mangle]
        pub extern "C" fn __cpsie() {}

        #[no_mangle]
        pub extern "C" fn __cpsid() {}
    };
}

/// Radio physical layer representation
///
/// # Examples
///
/// ```no_run
/// # #[macro_use] extern crate nrf_radio;
/// # missing_test_fns!();
/// # fn main() {
///   use nrf52840_hal::pac::Peripherals;
///   use nrf_radio::radio::Phy;
///
///   let peripherals = Peripherals::take().unwrap();
///   let phy = Phy::new(&peripherals.RADIO);
///   phy.configure_802154();
/// # }
/// ```
pub struct Phy {
    isr_data: &'static Mutex<RefCell<Option<IsrData>>>,
}

impl Phy {
    /// Reset module
    ///
    /// This function is intended to be used between unit tests
    #[doc(hidden)]
    pub fn reset() {
        crate::crit_sect::locked(|cs| {
            ISR_DATA.borrow(cs).replace(None);
        });
    }

    /// Create new instance of the physical layer
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    ///   use nrf52840_hal::pac::Peripherals;
    ///   use nrf_radio::radio::Phy;
    ///
    ///   let peripherals = Peripherals::take().unwrap();
    ///
    ///   let phy = Phy::new(&peripherals.RADIO);
    /// # }
    /// ```
    pub fn new(radio: &RadioRegisterBlock) -> Self {
        let isr_data = IsrData {
            radio: RadioPeriphWrapper::new(radio),
            state: State::Idle,
        };

        crate::crit_sect::locked(|cs| {
            let prev_isr_data = ISR_DATA.borrow(cs).replace(Some(isr_data));
            assert!(prev_isr_data.is_none());
        });

        Self {
            isr_data: &ISR_DATA,
        }
    }

    /// Helper function to get access to data accessible from ISR
    fn use_isr_data<F, R>(&self, func: F) -> R
    where
        F: FnOnce(&mut IsrData) -> R,
    {
        crate::crit_sect::locked(|cs| {
            let isr_data_option = &mut self.isr_data.borrow(cs).borrow_mut();
            let isr_data = &mut isr_data_option.as_mut().unwrap();
            func(isr_data)
        })
    }

    /// Configure physical layer for IEEE 802.15.4 protocol
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    ///   use nrf52840_hal::pac::Peripherals;
    ///   use nrf_radio::radio::Phy;
    ///
    ///   let peripherals = Peripherals::take().unwrap();
    ///   let phy = Phy::new(&peripherals.RADIO);
    ///   phy.configure_802154();
    /// # }
    /// ```
    pub fn configure_802154(&self) {
        self.use_isr_data(|i| {
            i.radio
                .mode
                .write(|w| w.mode().variant(radio::mode::MODE_A::IEEE802154_250KBIT));
            i.radio.pcnf0.write(|w| {
                w.lflen()
                    .variant(8)
                    .plen()
                    .variant(radio::pcnf0::PLEN_A::_32BIT_ZERO)
                    .crcinc()
                    .variant(radio::pcnf0::CRCINC_A::INCLUDE)
            });
            i.radio.pcnf1.write(|w| w.maxlen().variant(127)); // TODO: remove magic numbers
            i.radio
                .modecnf0
                .write(|w| w.ru().variant(radio::modecnf0::RU_A::FAST));
            i.radio.crccnf.write(|w| {
                w.len()
                    .variant(radio::crccnf::LEN_A::TWO)
                    .skipaddr()
                    .variant(radio::crccnf::SKIPADDR_A::IEEE802154)
            });
            i.radio.crcpoly.write(|w| w.crcpoly().variant(0x011021)); // TODO: remove magic numbers

            // TODO: move CCA configuration out
            i.radio.ccactrl.write(|w| {
                w.ccamode()
                    .variant(radio::ccactrl::CCAMODE_A::ED_MODE)
                    .ccaedthres()
                    .variant(20)
            });
        });

        // TODO: enable IRQs?
        //       or perhaps separated function to enable irqs?
    }

    fn get_802154_frequency_from_channel(channel: u8) -> Result<u16, Error> {
        if (11..=26).contains(&channel) {
            Ok(2405u16 + (channel - 11) as u16 * 5)
        } else {
            Err(Error::InvalidChannel)
        }
    }

    /// Sets channel (radio frequency)
    ///
    /// The channel number depends on configured Phy mode. Currently only IEEE 802.15.4 is
    /// supported with channels from range 11-26.
    ///
    /// Returns:
    /// * [`Ok(())`](core::result::Result::Ok) if channel is configured successfully
    /// * [`Err(Error::WouldBlock)`](Error::WouldBlock) if the transceiver is enabled
    /// * [`Err(Error::InvalidChannel)`](Error::InvalidChannel) if the requested channel is out of
    /// range for enabled radio protocol
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// use core::any::Any;
    /// use nrf52840_hal::pac::Peripherals;
    /// use nrf_radio::radio::Phy;
    ///
    /// fn main() {
    ///   let peripherals = Peripherals::take().unwrap();
    ///   let phy = Phy::new(&peripherals.RADIO);
    ///   phy.configure_802154();
    ///
    ///   let result = phy.set_channel(11);
    ///   assert_eq!(result, Ok(()));
    /// }
    /// ```
    pub fn set_channel(&self, channel: u8) -> Result<(), Error> {
        self.use_isr_data(|i| match &i.state {
            State::Idle => {
                let frequency = (Phy::get_802154_frequency_from_channel(channel)? - 2400)
                    .try_into()
                    .unwrap();
                i.radio
                    .frequency
                    .write(|w| w.frequency().variant(frequency));
                Ok(())
            }
            _ => Err(Error::WouldBlock),
        })
    }

    /// Helper function to set PACKETPTR register to point to passed buffer
    fn set_packetptr(buffer: &[u8], i: &mut IsrData) {
        i.radio
            .packetptr
            .write(|w| w.packetptr().variant(buffer.as_ptr() as u32));
    }

    /// FSM procedure on entering TX state
    fn enter_tx(frame: &[u8], i: &mut IsrData) {
        Phy::set_packetptr(frame, i);
        i.radio
            .shorts
            .write(|w| w.txready_start().set_bit().phyend_disable().set_bit());
        i.radio
            .events_phyend
            .write(|w| w.events_phyend().clear_bit());
        i.radio.tasks_txen.write(|w| w.tasks_txen().set_bit());
        i.radio.intenset.write(|w| w.phyend().set_bit());
    }

    /// FSM procedure on exitting TX state
    fn exit_tx(i: &mut IsrData) {
        i.radio.intenclr.write(|w| w.phyend().set_bit());
    }

    /// Transmits a frame
    ///
    /// Transmits the content of `frame` using radio protocol configured for this [`Phy`] instance.
    /// For IEEE 802.15.4 `frame` must include PHR and PSDU. Other protocols are not supported yet.
    ///
    /// Returns [`Ok(())`](core::result::Result::Ok) if the transmission request was accepted. If
    /// the request was not accepted returns [`Err(Error)`](Error).
    ///
    /// After the accepted transmission request is completed the `callback` function is called from
    /// an ISR context. The parameters of the `callback` function are `result` indicating if the
    /// requested transmission was successful, and `context` being any reference provided by the
    /// caller. The caller might use `context` to match callbacks with transmission requests.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// use core::any::Any;
    /// use nrf52840_hal::pac::Peripherals;
    /// use nrf_radio::radio::Phy;
    /// use nrf_radio::error::Error;
    ///
    /// fn tx_callback(result: Result<(), Error>, context: &'static (dyn Any + Send + Sync)) {
    ///   println!("Packet tx procedure finished");
    /// }
    ///
    /// fn main() {
    ///   let peripherals = Peripherals::take().unwrap();
    ///   let phy = Phy::new(&peripherals.RADIO);
    ///   phy.configure_802154();
    ///
    ///   let frame: [u8; 17] = [16, 0x41, 0x98, 0xaa, 0xcd, 0xab, 0xff, 0xff, 0x34, 0x12,
    ///                              0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];
    ///   let result = phy.tx(&frame, tx_callback, &None::<u8>);
    ///   assert_eq!(result, Ok(()));
    /// }
    /// ```
    pub fn tx(&self, frame: &[u8], callback: TxCallback, context: Context) -> Result<(), Error> {
        // FSM:
        // | idle |  <----> | tx |
        self.use_isr_data(|i| match &i.state {
            State::Idle => {
                i.state = State::Tx(TxData { callback, context });
                Phy::enter_tx(frame, i);
                Ok(())
            }
            _ => Err(Error::WouldBlock),
        })
    }

    /// FSM procedure on entering RX state
    fn enter_rx(buffer: &[u8], i: &mut IsrData) {
        Phy::set_packetptr(buffer, i);
        i.radio
            .shorts
            .write(|w| w.rxready_start().set_bit().end_disable().set_bit());
        i.radio.events_crcok.write(|w| w.events_crcok().clear_bit());
        i.radio
            .events_crcerror
            .write(|w| w.events_crcerror().clear_bit());
        i.radio.tasks_rxen.write(|w| w.tasks_rxen().set_bit());
        i.radio
            .intenset
            .write(|w| w.crcok().set_bit().crcerror().set_bit());
    }

    /// FSM procedure on exitting RX state
    fn exit_rx(i: &mut IsrData) {
        i.radio
            .intenclr
            .write(|w| w.crcok().set_bit().crcerror().set_bit());
    }

    /// Enables receiver
    ///
    /// The receiver is enabled until a frame is received.
    ///
    /// Returns [`Ok(())`](core::result::Result::Ok) if the request was accepted. If the request
    /// was not accepted returns [`Err(Error)`](Error).
    ///
    /// After a frame is received the `callback` function is called from an ISR context. The
    /// `result` parameter of the `callback` function is [`Ok(RxOk)`](RxOk) if the received frame
    /// is valid. Alternatively it is [`Err(Error)`](Error) if the received frame is invalid.
    ///
    /// When the callback is called the receiver is not enabled anymore.
    ///
    /// The `rx_buffer` is returned to the caller through `callback` when received a valid frame.
    /// The `rx_buffer` is dropped on any error.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// use nrf52840_hal::pac::Peripherals;
    /// use nrf_radio::radio::{Phy, RxOk, Context};
    /// use nrf_radio::error::Error;
    /// use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator;
    /// use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
    ///
    /// fn rx_callback(result: Result<RxOk, Error>, context: Context) {
    ///   match result {
    ///     Ok(rx_ok) => {
    ///       println!("Received frame: {:x?}", rx_ok.frame);
    ///     }
    ///     Err(error) => {
    ///       println!("Received invalid frame because of {:?}", error);
    ///     }
    ///   }
    /// }
    ///
    /// fn main() {
    ///   let buffer_allocator = SingleFrameAllocator::new();
    ///
    ///   let peripherals = Peripherals::take().unwrap();
    ///   let phy = Phy::new(&peripherals.RADIO);
    ///   phy.configure_802154();
    ///
    ///   let result = phy.rx(buffer_allocator.get_frame().unwrap(), rx_callback, &None::<usize>);
    ///   assert_eq!(result, Ok(()));
    /// }
    /// ```
    pub fn rx(
        &self,
        rx_buffer: FrameBuffer<'static>,
        callback: RxCallback,
        context: Context,
    ) -> Result<(), Error> {
        if rx_buffer.len() <= 127 {
            // TODO: remove magic number
            return Err(Error::TooSmallBuffer);
        }

        self.use_isr_data(|i| match &i.state {
            State::Idle => {
                Phy::enter_rx(&rx_buffer, i);
                i.state = State::Rx(RxData {
                    callback,
                    context,
                    rx_buffer,
                });
                Ok(())
            }
            _ => Err(Error::WouldBlock),
        })
    }
}

// TODO: remove when extenral IRQ managing library is used
use nrf52840_hal::pac::interrupt;
#[interrupt]
fn RADIO() {
    irq_handler();
}

fn irq_handler() {
    enum Callback {
        None,
        Tx(TxCallback, Context),
        Rx(RxCallback, Context, Result<RxOk, Error>),
    }

    let mut callback = Callback::None;

    crate::crit_sect::locked(|cs| {
        //let mut r = ISR_DATA.borrow(cs).borrow_mut();
        //let i = r.as_mut().unwrap();

        let mut i = ISR_DATA.borrow(cs).replace(None).unwrap();

        match i.state {
            State::Rx(rx_data) => {
                if i.radio.events_crcok.read().events_crcok().bit_is_set() {
                    i.radio.events_crcok.write(|w| w.events_crcok().clear_bit());

                    callback = Callback::Rx(
                        rx_data.callback,
                        rx_data.context,
                        Ok(RxOk {
                            frame: rx_data.rx_buffer,
                        }),
                    );
                } else if i
                    .radio
                    .events_crcerror
                    .read()
                    .events_crcerror()
                    .bit_is_set()
                {
                    i.radio
                        .events_crcerror
                        .write(|w| w.events_crcerror().clear_bit());

                    callback =
                        Callback::Rx(rx_data.callback, rx_data.context, Err(Error::IncorrectCrc));
                } else {
                    panic!("Unexpected event received in Rx state");
                }

                i.state = State::Idle;
                Phy::exit_rx(&mut i);
            }

            State::Tx(tx_data) => {
                if i.radio.events_phyend.read().events_phyend().bit_is_set() {
                    i.radio
                        .events_phyend
                        .write(|w| w.events_phyend().clear_bit());

                    callback = Callback::Tx(tx_data.callback, tx_data.context);
                } else {
                    panic!("Unexpected event received in Tx state");
                }

                i.state = State::Idle;
                Phy::exit_tx(&mut i);
            }

            State::Idle => panic!("An event received in Idle state"),
        }

        let temp_i = ISR_DATA.borrow(cs).replace(Some(i));
        debug_assert!(temp_i.is_none());
    });

    match callback {
        Callback::None => (),
        Callback::Rx(callback, context, result) => callback(result, context),
        Callback::Tx(callback, context) => callback(Ok(()), context),
    };
}

#[cfg(test)]
missing_test_fns!();

#[cfg(test)]
mod tests {
    use super::*;
    use serial_test::serial;

    // RADIO peripheral mock
    #[repr(align(4))]
    struct RadioMock {
        memory: [u8; 4096],
    }

    impl RadioMock {
        pub fn new() -> Self {
            Self { memory: [0; 4096] }
        }
    }

    impl Deref for RadioMock {
        type Target = RadioRegisterBlock;
        fn deref(&self) -> &Self::Target {
            let ptr: *const RadioRegisterBlock = self.memory.as_ptr() as *const _;
            unsafe { ptr.as_ref().unwrap() }
        }
    }

    fn create_frame_buffer_from_static_buffer(static_buffer: &'static mut [u8]) -> FrameBuffer {
        FrameBuffer::new(static_buffer, None, &None::<usize>)
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_configuring_802154() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        assert_eq!(
            radio_mock.mode.read().mode().variant().unwrap(),
            radio::mode::MODE_A::IEEE802154_250KBIT
        );
        assert_eq!(radio_mock.pcnf0.read().lflen().bits(), 8);
        assert_eq!(radio_mock.pcnf0.read().s0len().bit(), false);
        assert_eq!(radio_mock.pcnf0.read().s1len().bits(), 0);
        assert_eq!(radio_mock.pcnf0.read().cilen().bits(), 0);
        assert_eq!(
            radio_mock.pcnf0.read().plen().variant(),
            radio::pcnf0::PLEN_A::_32BIT_ZERO
        );
        assert_eq!(
            radio_mock.pcnf0.read().crcinc().variant(),
            radio::pcnf0::CRCINC_A::INCLUDE
        );
        assert_eq!(radio_mock.pcnf0.read().termlen().bits(), 0);
        assert_eq!(radio_mock.pcnf1.read().maxlen().bits(), 127);
        assert_eq!(radio_mock.pcnf1.read().statlen().bits(), 0);
        assert_eq!(radio_mock.pcnf1.read().balen().bits(), 0);
        assert_eq!(
            radio_mock.pcnf1.read().endian().variant(),
            radio::pcnf1::ENDIAN_A::LITTLE
        );
        assert_eq!(
            radio_mock.pcnf1.read().whiteen().variant(),
            radio::pcnf1::WHITEEN_A::DISABLED
        );
        assert_eq!(
            radio_mock.modecnf0.read().ru().variant(),
            radio::modecnf0::RU_A::FAST
        );
        assert_eq!(
            radio_mock.modecnf0.read().dtx().variant().unwrap(),
            radio::modecnf0::DTX_A::CENTER
        );
        assert_eq!(
            radio_mock.crccnf.read().len().variant(),
            radio::crccnf::LEN_A::TWO
        );
        assert_eq!(
            radio_mock.crccnf.read().skipaddr().variant().unwrap(),
            radio::crccnf::SKIPADDR_A::IEEE802154
        );
        assert_eq!(radio_mock.crcpoly.read().crcpoly().bits(), 0x011021);
        assert_eq!(radio_mock.crcinit.read().crcinit().bits(), 0);
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_tx() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);

        let frame: [u8; 17] = [
            16, 0x41, 0x98, 0xaa, 0xcd, 0xab, 0xff, 0xff, 0x34, 0x12, 0x01, 0x02, 0x03, 0x04, 0x05,
            0x06, 0x07,
        ];

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Result<(), Error> = Err(Error::IncorrectCrc);
        static mut RECEIVED_CONTEXT: &Option<u8> = &Some(0);

        fn callback(result: Result<(), Error>, context: Context) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = result };
            unsafe { RECEIVED_CONTEXT = context.downcast_ref().unwrap() };
        }

        phy.configure_802154();
        let result = phy.tx(&frame, callback, &None::<u8>);

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Check peripheral configuration before IRQ
        assert_eq!(radio_mock.packetptr.read().bits(), frame.as_ptr() as u32);
        assert!(radio_mock.shorts.read().txready_start().bit_is_set());
        assert!(radio_mock.shorts.read().phyend_disable().bit_is_set());
        assert!(radio_mock
            .events_phyend
            .read()
            .events_phyend()
            .bit_is_clear());
        assert!(radio_mock.intenset.read().phyend().bit_is_set());

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_phyend
            .write(|w| w.events_phyend().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        assert_eq!(unsafe { &RECEIVED_RESULT }, &Ok(()));
        assert_eq!(unsafe { RECEIVED_CONTEXT }, &None::<u8>); // TODO check address instead of value
        assert!(radio_mock.intenclr.read().phyend().bit_is_set());
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_enter_rx() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut FRAME: [u8; 128] = [0; 128];

        fn callback(_result: Result<RxOk, Error>, _context: Context) {
            unsafe { CALLED = true };
        }

        let result = phy.rx(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        );

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // TODO check bits that should be clear? Can I easily check "all other bits"?
        assert!(radio_mock.shorts.read().rxready_start().bit_is_set());
        assert!(radio_mock.shorts.read().end_disable().bit_is_set());
        assert!(radio_mock.events_crcok.read().events_crcok().bit_is_clear());
        assert!(radio_mock
            .events_crcerror
            .read()
            .events_crcerror()
            .bit_is_clear());
        assert!(radio_mock.intenset.read().crcok().bit_is_set());
        assert!(radio_mock.intenset.read().crcerror().bit_is_set());
        assert_eq!(
            radio_mock.packetptr.read().bits(),
            unsafe { FRAME.as_ptr() } as u32
        );

        assert!(!unsafe { CALLED });
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_rx_correct_frame() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Option<Result<RxOk, Error>> = None;
        static mut FRAME: [u8; 128] = [0; 128];

        fn callback(result: Result<RxOk, Error>, _context: Context) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = Some(result) };
        }

        let result = phy.rx(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        );

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_crcok
            .write(|w| w.events_crcok().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        unsafe {
            assert!(RECEIVED_RESULT.is_some());
            let received_option = RECEIVED_RESULT.replace(Err(Error::WouldBlock)).unwrap();
            assert!(received_option.is_ok());
            assert_eq!(
                received_option.as_ref().unwrap().frame.as_ptr() as u32,
                FRAME.as_ptr() as u32
            );
        }
        assert!(radio_mock.intenclr.read().crcok().bit_is_set());
        assert!(radio_mock.intenclr.read().crcerror().bit_is_set());
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_rx_frame_with_incorrect_crc() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut CALLED: bool = false;
        static mut RECEIVED_RESULT: Option<Result<RxOk, Error>> = None;
        static mut FRAME: [u8; 128] = [0; 128];

        fn callback(result: Result<RxOk, Error>, _context: Context) {
            unsafe { CALLED = true };
            unsafe { RECEIVED_RESULT = Some(result) };
        }

        let result = phy.rx(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            callback,
            &None::<usize>,
        );

        assert_eq!(result, Ok(()));
        assert!(!unsafe { CALLED });

        // Set IRQ event and trigger IRQ
        radio_mock
            .events_crcerror
            .write(|w| w.events_crcerror().set_bit());
        irq_handler();

        assert!(unsafe { CALLED });
        assert_eq!(unsafe { &RECEIVED_RESULT }, &Some(Err(Error::IncorrectCrc)));
        assert!(radio_mock.intenclr.read().crcok().bit_is_set());
        assert!(radio_mock.intenclr.read().crcerror().bit_is_set());
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_tx_request_in_rx_state_returns_error() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        static mut RX_CALLED: bool = false;
        static mut FRAME: [u8; 128] = [0; 128];

        fn rx_callback(_result: Result<RxOk, Error>, _context: Context) {
            unsafe { RX_CALLED = true };
        }

        let result = phy.rx(
            create_frame_buffer_from_static_buffer(unsafe { &mut FRAME }),
            rx_callback,
            &None::<usize>,
        );
        assert_eq!(result, Ok(()));

        let frame: [u8; 17] = [
            16, 0x41, 0x98, 0xaa, 0xcd, 0xab, 0xff, 0xff, 0x34, 0x12, 0x01, 0x02, 0x03, 0x04, 0x05,
            0x06, 0x07,
        ];

        static mut TX_CALLED: bool = false;
        static mut TX_RECEIVED_RESULT: Option<Result<(), Error>> = None;
        static mut TX_RECEIVED_CONTEXT: &Option<u8> = &Some(0);

        fn tx_callback(result: Result<(), Error>, context: Context) {
            unsafe { TX_CALLED = true };
            unsafe { TX_RECEIVED_RESULT = Some(result) };
            unsafe { TX_RECEIVED_CONTEXT = context.downcast_ref().unwrap() };
        }

        let result = phy.tx(&frame, tx_callback, &None::<u8>);
        assert_eq!(result, Err(Error::WouldBlock));

        assert!(!unsafe { RX_CALLED });
        assert!(!unsafe { TX_CALLED });
    }

    #[test]
    #[serial]
    #[cfg_attr(miri, ignore)]
    fn test_802154_rx_request_during_tx_returns_error() {
        let radio_mock = RadioMock::new();
        Phy::reset();
        let phy = Phy::new(&radio_mock);
        phy.configure_802154();

        let frame: [u8; 17] = [
            16, 0x41, 0x98, 0xaa, 0xcd, 0xab, 0xff, 0xff, 0x34, 0x12, 0x01, 0x02, 0x03, 0x04, 0x05,
            0x06, 0x07,
        ];

        static mut TX_CALLED: bool = false;
        static mut TX_RECEIVED_RESULT: Option<Result<(), Error>> = None;
        static mut TX_RECEIVED_CONTEXT: &Option<u8> = &Some(0);
        static mut RX_FRAME: [u8; 128] = [0; 128];

        fn tx_callback(result: Result<(), Error>, context: Context) {
            unsafe { TX_CALLED = true };
            unsafe { TX_RECEIVED_RESULT = Some(result) };
            unsafe { TX_RECEIVED_CONTEXT = context.downcast_ref().unwrap() };
        }

        let result = phy.tx(&frame, tx_callback, &None::<u8>);
        assert_eq!(result, Ok(()));

        static mut RX_CALLED: bool = false;

        fn rx_callback(_result: Result<RxOk, Error>, _context: Context) {
            unsafe { RX_CALLED = true };
        }

        let result = phy.rx(
            create_frame_buffer_from_static_buffer(unsafe { &mut RX_FRAME }),
            rx_callback,
            &None::<usize>,
        );
        assert_eq!(result, Err(Error::WouldBlock));

        assert!(!unsafe { RX_CALLED });
        assert!(!unsafe { TX_CALLED });
    }
}
