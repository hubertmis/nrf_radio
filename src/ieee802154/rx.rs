//! IEEE 802.15.4 compliant receiver module
//!
//! This module is responsible for:
//!
//! * receiving frames from `Phy`
//! * filtering frames being received
//! * sending Acks if necessary
//! * decrypting frames on-the-fly

use crate::crit_sect;
use crate::error::Error;
use crate::frm_mem_mng::frame_buffer::FrameBuffer;
use crate::hw::ppi::{
    self,
    traits::{Allocator, Channel},
};
use crate::hw::timer::Timer;
use crate::ieee802154::frame::{Addr, Frame};
use crate::ieee802154::pib::Pib;
use crate::mutex::Mutex;
use crate::radio::{Context, Phy, RxOk, RxRequest, RxResources};
use crate::utils::tasklet::{Tasklet, TaskletListItem, TaskletQueue};

const BROADCAST_PAN_ID: [u8; 2] = [0xff, 0xff];
const BROADCAST_SHORT_ADDR: [u8; 2] = [0xff, 0xff];

// TODO: context as an argument?
/// Signature of a callback function called when the requested receive operation is finished
pub type RxDoneCallback = fn(Result<(FrameBuffer, u64), Error>);

// Callbacks are to be called from IRQs. That's why it require static data
static CALLBACK_DATA: Mutex<Option<CallbackData>> = Mutex::new(None);

struct CallbackData {
    phy: &'static Phy,
    timer: &'static dyn Timer<ppi::Channel>,
    pib: &'static Pib,
    ppi_allocator: &'static ppi::Allocator,
    tasklet_queue: &'static TaskletQueue<'static>,

    rx_result: Option<Result<(FrameBuffer<'static>, u64), Error>>,
    receive_done_tasklet: Tasklet<'static>,
    receive_done_tasklet_ref: Option<&'static mut TaskletListItem<'static>>,
    receive_done_callback: Option<RxDoneCallback>,
}

/// IEEE 802.15.4 receiver
pub struct Rx {
    callback_data: &'static Mutex<Option<CallbackData>>,
}

impl Rx {
    /// Create new IEEE 802.15.4 receiver
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    ///   use nrf52840_hal::pac::Peripherals;
    ///   use nrf_radio::hw::ppi::legacy_ppi::PpiAllocator;
    ///   use nrf_radio::hw::timer::timer_using_timer::TimerUsingTimer;
    ///   use nrf_radio::ieee802154::pib::Pib;
    ///   use nrf_radio::ieee802154::rx::Rx;
    ///   use nrf_radio::radio::Phy;
    ///   use nrf_radio::utils::tasklet::TaskletQueue;
    ///
    ///   static mut PHY: Option<Phy> = None;
    ///   static PIB: Pib = Pib::new();
    ///   static mut TASKLET_QUEUE: Option<TaskletQueue> = None;
    ///   static mut PPI_ALLOC: Option<PpiAllocator> = None;
    ///   static mut TIMER: Option<TimerUsingTimer> = None;
    ///
    ///   let peripherals = Peripherals::take().unwrap();
    ///
    ///   // Safety: at this point no other module has access to static variables
    ///   unsafe {
    ///     PHY.replace(Phy::new(&peripherals.RADIO));
    ///     PHY.as_ref().unwrap().configure_802154();
    ///     TASKLET_QUEUE.replace(TaskletQueue::new());
    ///     PPI_ALLOC.replace(PpiAllocator::new(&peripherals.PPI));
    ///     TIMER.replace(TimerUsingTimer::new(&peripherals.TIMER0));
    ///
    ///     let rx = Rx::new(PHY.as_ref().unwrap(),
    ///                      &PIB,
    ///                      TASKLET_QUEUE.as_ref().unwrap(),
    ///                      PPI_ALLOC.as_ref().unwrap(),
    ///                      TIMER.as_ref().unwrap(),
    ///                     );
    ///   }
    ///
    /// # }
    /// ```
    pub fn new(
        phy: &'static Phy,
        pib: &'static Pib,
        tasklet_queue: &'static TaskletQueue<'static>,
        ppi_allocator: &'static ppi::Allocator,
        timer: &'static dyn Timer<ppi::Channel>,
    ) -> Self {
        let new_callback_data = CallbackData {
            phy,
            pib,
            tasklet_queue,
            ppi_allocator,
            timer,
            rx_result: None,
            receive_done_tasklet: Tasklet::new(Rx::receive_done_tasklet_fn, &CALLBACK_DATA),
            receive_done_tasklet_ref: None,
            receive_done_callback: None,
        };

        crit_sect::locked(|cs| {
            let prev_data = CALLBACK_DATA.borrow_mut(cs).replace(new_callback_data);
            assert!(prev_data.is_none());

            let data_option = &mut CALLBACK_DATA.borrow_mut(cs);
            let data = &mut data_option.as_mut().unwrap();
            let receive_done_tasklet_ptr: *mut Tasklet<'static> = &mut data.receive_done_tasklet;
            // TODO: describe safety
            let receive_done_tasklet_ref: &'static mut Tasklet<'static> =
                unsafe { receive_done_tasklet_ptr.as_mut() }.unwrap();
            data.receive_done_tasklet_ref = Some(receive_done_tasklet_ref);
        });

        Self {
            callback_data: &CALLBACK_DATA,
        }
    }

    /// Helper function to get access to the structure data
    fn use_data<F, R>(&self, func: F) -> R
    where
        F: FnOnce(&mut CallbackData) -> R,
    {
        crit_sect::locked(|cs| {
            let data_option = &mut self.callback_data.borrow_mut(cs);
            let data = &mut data_option.as_mut().unwrap();
            func(data)
        })
    }

    /// Helper function to get access to the callback data retrieved from Context
    fn use_data_from_context<F, R>(context: Context, func: F) -> R
    where
        F: FnOnce(&mut CallbackData) -> R,
    {
        let callback_data = context
            .downcast_ref::<Mutex<Option<CallbackData>>>()
            .unwrap();
        crit_sect::locked(|cs| {
            let data_option = &mut callback_data.borrow_mut(cs);
            let data = &mut data_option.as_mut().unwrap();
            func(data)
        })
    }

    /// Starts the RX operation
    ///
    /// During the RX operation the receiver receives a frame to the passed `rx_buffer`.
    /// When the RX operation is finished the `rx_done_callback` is called reporting the status of
    /// the operation.
    ///
    /// The operation is finished when one of the following conditions occur:
    ///
    /// * Received a frame destined to this node which does not require sending Ack
    /// * Sent Ack as a response to a received frame destinged to this node
    /// * Received a frame destined to other node
    /// * Received an invalid frame
    /// * Physical layer reports an error
    /// * TODO: Something with security errors?
    ///
    /// The callback is called from the tasklets context, because handling such callback is not
    /// considered timing-critical.
    ///
    /// # Example
    ///
    /// ```no_run
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    ///   use nrf52840_hal::pac::Peripherals;
    ///   use nrf_radio::error::Error;
    ///   use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator;
    ///   use nrf_radio::frm_mem_mng::frame_buffer::FrameBuffer;
    ///   use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
    ///   use nrf_radio::hw::ppi::Allocator;
    ///   use nrf_radio::hw::timer::timer_using_timer::TimerUsingTimer;
    ///   use nrf_radio::ieee802154::pib::Pib;
    ///   use nrf_radio::ieee802154::rx::Rx;
    ///   use nrf_radio::radio::Phy;
    ///   use nrf_radio::utils::tasklet::TaskletQueue;
    ///
    ///   static mut PHY: Option<Phy> = None;
    ///   static PIB: Pib = Pib::new();
    ///   static mut TASKLET_QUEUE: Option<TaskletQueue> = None;
    ///   static mut PPI_ALLOC: Option<Allocator> = None;
    ///   static mut TIMER: Option<TimerUsingTimer> = None;
    ///
    ///   let peripherals = Peripherals::take().unwrap();
    ///
    ///   // Safety: at this point no other module has access to static variables
    ///   unsafe {
    ///     PHY.replace(Phy::new(&peripherals.RADIO));
    ///     PHY.as_ref().unwrap().configure_802154();
    ///     TASKLET_QUEUE.replace(TaskletQueue::new());
    ///     PPI_ALLOC.replace(Allocator::new(&peripherals.PPI));
    ///     TIMER.replace(TimerUsingTimer::new(&peripherals.TIMER0));
    ///   }
    ///
    ///   let rx;
    ///   // Safety: at this point no other module has access to static variables
    ///   unsafe {
    ///     rx = Rx::new(PHY.as_ref().unwrap(),
    ///                  &PIB,
    ///                  TASKLET_QUEUE.as_ref().unwrap(),
    ///                  PPI_ALLOC.as_ref().unwrap(),
    ///                  TIMER.as_ref().unwrap(),
    ///                 );
    ///   }
    ///
    ///   let frame_allocator = SingleFrameAllocator::new();
    ///   let frame_buffer = frame_allocator.get_frame().unwrap();
    ///
    ///   let result = rx.start(frame_buffer, rx_done_callback);
    ///
    ///   fn rx_done_callback(result: Result<(FrameBuffer, u64), Error>) {
    ///     match result {
    ///       Ok((frame, timestamp)) => { /* Do something with received frame */ },
    ///       Err(Error::InvalidFrame) => { /* Handle error */ },
    ///       Err(_) => { /* Handle other errors */ },
    ///     }
    ///   }
    /// # }
    /// ```
    pub fn start(
        &self,
        rx_buffer: FrameBuffer<'static>,
        rx_done_callback: RxDoneCallback,
    ) -> Result<(), Error> {
        // TODO: return error if already receiving
        self.use_data(|d| {
            let ppi_ch = d.ppi_allocator.allocate_channel()?;

            d.receive_done_callback = Some(rx_done_callback);
            let result = d.timer.start_capturing_timestamps(&ppi_ch);
            debug_assert!(result.is_ok());
            ppi_ch.enable();
            d.phy.rx(
                RxRequest::new(rx_buffer, Rx::phy_callback, self.callback_data)
                    .with_ppi_channel_on_phyend(ppi_ch)
                    .now(),
            )
        })
    }

    fn phy_callback(result: Result<RxOk, Error>, context: Context, resources: &mut RxResources) {
        defmt::info!("rx callback");

        if let Some(ppi_ch) = resources.phyend_ppi_channel() {
            Rx::use_data_from_context(context, |d| {
                ppi_ch.disable();
                let result = d.timer.stop_capturing_timestamps(&ppi_ch);
                debug_assert!(result.is_ok());
            });
            drop(ppi_ch);
        }

        match result {
            Ok(rx_ok) => {
                let frame = Frame::from_frame_buffer(&rx_ok.frame);
                if let Ok(frame) = frame {
                    Rx::use_data_from_context(context, |d| {
                        // TODO: move filtering to a separated module
                        if !d.pib.get_promiscuous() {
                            let dst_pan_id = frame.get_dst_pan_id().unwrap();
                            if let Some(dst_pan_id) = dst_pan_id {
                                if dst_pan_id != d.pib.get_pan_id()
                                    && dst_pan_id != &BROADCAST_PAN_ID
                                {
                                    notify_rx_done(d, Err(Error::NotMatchingPanId));
                                    return;
                                }
                            } else {
                                // TODO: Handle frames with missing dst pan id
                                return;
                            }

                            let dst_addr = frame.get_dst_address().unwrap();
                            if let Some(dst_addr) = dst_addr {
                                match dst_addr {
                                    Addr::Short(addr) => {
                                        if addr != d.pib.get_short_addr()
                                            && addr != &BROADCAST_SHORT_ADDR
                                        {
                                            notify_rx_done(d, Err(Error::NotMatchingAddress));
                                            return;
                                        }
                                    }
                                    Addr::Ext(addr) => {
                                        if addr != d.pib.get_ext_addr() {
                                            notify_rx_done(d, Err(Error::NotMatchingAddress));
                                            return;
                                        }
                                    }
                                }
                            } else {
                                // TODO: Handle frames with missing dst address
                                return;
                            }
                        }

                        // TODO: Handle transmitting ACK
                        // TODO: Handle transmitting ACK after relevant fields are received
                        //       (src addr, security?)
                        // TODO: Report received frame for us (after ACK transmitted?)!
                        notify_rx_done(d, Ok((rx_ok.frame, d.timer.timestamp().unwrap().into())));
                    });
                } else {
                    Rx::use_data_from_context(context, |d| {
                        if d.pib.get_promiscuous() {
                            notify_rx_done(
                                d,
                                Ok((rx_ok.frame, d.timer.timestamp().unwrap().into())),
                            )
                        } else {
                            notify_rx_done(d, Err(Error::InvalidFrame))
                        }
                    });
                }
            }
            Err(e) => {
                Rx::use_data_from_context(context, |d| notify_rx_done(d, Err(e)));
            }
        }

        // TODO: move filtering to callbacks called while the frame is being received

        fn notify_rx_done(
            d: &mut CallbackData,
            result: Result<(FrameBuffer<'static>, u64), Error>,
        ) {
            defmt::info!("scheduling rx done notification");
            let prev_result = d.rx_result.replace(result);
            debug_assert!(prev_result.is_none());
            // TODO: call the callback directly instead of using a tasklet, and let user to
            //       decide in the callback to defer to tasklet?
            //       I expect some users like async RX could prefer to restart RX from ISR context
            //       to potentially catch more frames
            // TODO: something safer than unwrap?
            d.tasklet_queue
                .push(d.receive_done_tasklet_ref.take().unwrap());
        }
    }

    fn receive_done_tasklet_fn(tasklet_ref: &'static mut TaskletListItem, context: Context) {
        let mut callback = None;
        let mut rx_result = None;

        Rx::use_data_from_context(context, |d| {
            d.receive_done_tasklet_ref.replace(tasklet_ref);
            callback = d.receive_done_callback.take();
            rx_result = d.rx_result.take();
        });

        let callback = callback.unwrap();
        let rx_result = rx_result.unwrap();

        callback(rx_result);
    }
}
