//! IEEE 802.15.4 compliant receiver module
//!
//! This module is responsible for:
//!
//! * receiving frames from `Phy`
//! * filtering frames being received
//! * sending Acks if necessary
//! * decrypting frames on-the-fly

mod ack_generator;
mod filter;

use ack_generator::AckGenerator;
use filter::{Filter, RxFilter};

use crate::crit_sect;
use crate::error::Error;
use crate::frm_mem_mng::frame_buffer::FrameBuffer;
use crate::frm_mem_mng::single_pool_allocator::SinglePoolAllocator;
use crate::hw::ppi::traits::Channel;
use crate::hw::timer::{
    traits::{TaskChannel, Timer as TimerTrait, TimestampChannel, Timestamper},
    Timer, Timestamp,
};
use crate::ieee802154::frame::{Frame, Parser};
use crate::ieee802154::pib::Pib;
use crate::mutex::Mutex;
use crate::radio::{Context, RxOk as PhyRxOk, RxRequest, RxResources, TxRequest, TxResources};
use crate::shared_resources::TimeSlicedResources;
use crate::utils::tasklet::{Tasklet, TaskletListItem, TaskletQueue};

type AckFrameAllocator = SinglePoolAllocator;

// TODO: context as an argument?
/// Signature of a callback function called when the requested receive operation is finished
pub type RxDoneCallback = fn(Result<RxOk, Error>);

// Callbacks are to be called from IRQs. That's why it require static data
static CALLBACK_DATA: Mutex<Option<CallbackData>> = Mutex::new(None);

struct CallbackData {
    shared_resources: Option<&'static mut TimeSlicedResources<'static>>,
    pib: &'static Pib,
    tasklet_queue: &'static TaskletQueue<'static>,
    ack_frame_allocator: &'static AckFrameAllocator,

    rx_result: Option<Result<RxOk, Error>>,
    receive_done_tasklet: Tasklet<'static>,
    receive_done_tasklet_ref: Option<&'static mut TaskletListItem<'static>>,
    receive_done_callback: Option<RxDoneCallback>,
}
unsafe impl Send for CallbackData {}

/// Data associated with a successful RX operation
pub struct RxOk {
    frame: Option<FrameBuffer<'static>>,
    timestamp: Timestamp,
    ack: Option<FrameBuffer<'static>>,
}

impl RxOk {
    fn new(frame: FrameBuffer<'static>, timestamp: Timestamp) -> Self {
        Self {
            frame: Some(frame),
            timestamp,
            ack: None,
        }
    }

    /// Get received frame
    ///
    /// This function moves ownership of the received frame to the caller. It can be used once on
    /// a single `RxOk` instance.
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::error::Error;
    /// use nrf_radio::ieee802154::rx::RxOk;
    ///
    /// fn rx_done_callback(result: Result<RxOk, Error>) {
    ///   match result {
    ///     Ok(mut rx_ok) => {
    ///       // First call always returns `Ok(frame)`.
    ///       let frame_buffer = rx_ok.frame().unwrap();
    ///       let phr = frame_buffer[0];
    ///
    ///       let frame_result = rx_ok.frame();
    ///       assert!(frame_result.is_err());
    ///     },
    ///     Err(Error::InvalidFrame) => { /* Handle error */ },
    ///     Err(_) => { /* Handle other errors */ },
    ///   }
    /// }
    /// ```
    pub fn frame(&mut self) -> Result<FrameBuffer<'static>, Error> {
        self.frame.take().ok_or(Error::AlreadyTaken)
    }

    /// Get timestamp of the end of the last on-air part of the received frame
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::error::Error;
    /// use nrf_radio::ieee802154::rx::RxOk;
    ///
    /// fn rx_done_callback(result: Result<RxOk, Error>) {
    ///   match result {
    ///     Ok(rx_ok) => {
    ///       let timestamp = rx_ok.timestamp();
    ///     },
    ///     Err(_) => { /* Handle errors */ },
    ///   }
    /// }
    /// ```
    pub fn timestamp(&self) -> Timestamp {
        self.timestamp
    }

    /// Get sent acknowledgement frame (if one was sent)
    ///
    /// This function moves ownership of the transmitted ack frame to the caller. It can be used
    /// once on a single `RxOk` instance. Calling this function multiple times has the same result
    /// as calling it when no Ack was sent (returning `None`).
    ///
    /// # Example
    ///
    /// ```
    /// use nrf_radio::error::Error;
    /// use nrf_radio::ieee802154::rx::RxOk;
    ///
    /// fn rx_done_callback(result: Result<RxOk, Error>) {
    ///   match result {
    ///     Ok(mut rx_ok) => {
    ///       if let Some(ack_frame) = rx_ok.ack_frame() {
    ///         let ack_phr = ack_frame[0];
    ///         // Do something with ack content
    ///       } else {
    ///         // Ack was not transmitted.
    ///         // The reason might be no need to transmit an Ack frame or software latency
    ///         // prevented ack transmission at required time
    ///       }
    ///
    ///       // Each following attempt of getting ack results in None
    ///       let ack_option = rx_ok.ack_frame();
    ///       assert!(ack_option.is_none());
    ///     },
    ///     Err(Error::InvalidFrame) => { /* Handle error */ },
    ///     Err(_) => { /* Handle other errors */ },
    ///   }
    /// }
    /// ```
    pub fn ack_frame(&mut self) -> Option<FrameBuffer<'static>> {
        self.ack.take()
    }
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
    ///   use nrf_radio::frm_mem_mng::single_pool_allocator::SinglePoolAllocator as FrameAllocator;
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
    ///   static mut FRAME_ALLOCATOR: Option<FrameAllocator> = None;
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
    ///     FRAME_ALLOCATOR.replace(FrameAllocator::new());
    ///
    ///     let rx = Rx::new(PHY.as_ref().unwrap(),
    ///                      &PIB,
    ///                      TASKLET_QUEUE.as_ref().unwrap(),
    ///                      PPI_ALLOC.as_ref().unwrap(),
    ///                      TIMER.as_ref().unwrap(),
    ///                      FRAME_ALLOCATOR.as_ref().unwrap(),
    ///                     );
    ///   }
    ///
    /// # }
    /// ```
    pub fn new(
        pib: &'static Pib,
        tasklet_queue: &'static TaskletQueue<'static>,
        ack_frame_allocator: &'static AckFrameAllocator,
    ) -> Self {
        let new_callback_data = CallbackData {
            shared_resources: None,
            pib,
            tasklet_queue,
            ack_frame_allocator,
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
    ///   use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator as FrameAllocatorTrait;
    ///   use nrf_radio::frm_mem_mng::frame_buffer::FrameBuffer;
    ///   use nrf_radio::frm_mem_mng::single_pool_allocator::SinglePoolAllocator as FrameAllocator;
    ///   use nrf_radio::hw::ppi::Allocator;
    ///   use nrf_radio::hw::timer::timer_using_timer::TimerUsingTimer;
    ///   use nrf_radio::ieee802154::pib::Pib;
    ///   use nrf_radio::ieee802154::rx::{Rx, RxOk};
    ///   use nrf_radio::radio::Phy;
    ///   use nrf_radio::utils::tasklet::TaskletQueue;
    ///
    ///   static mut PHY: Option<Phy> = None;
    ///   static PIB: Pib = Pib::new();
    ///   static mut TASKLET_QUEUE: Option<TaskletQueue> = None;
    ///   static mut PPI_ALLOC: Option<Allocator> = None;
    ///   static mut TIMER: Option<TimerUsingTimer> = None;
    ///   static mut FRAME_ALLOCATOR: Option<FrameAllocator> = None;
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
    ///     FRAME_ALLOCATOR.replace(FrameAllocator::new());
    ///   }
    ///
    ///   let rx;
    ///   let frame_allocator;
    ///   // Safety: at this point no other module has access to static variables
    ///   unsafe {
    ///     frame_allocator = FRAME_ALLOCATOR.as_ref().unwrap();
    ///     rx = Rx::new(PHY.as_ref().unwrap(),
    ///                  &PIB,
    ///                  TASKLET_QUEUE.as_ref().unwrap(),
    ///                  PPI_ALLOC.as_ref().unwrap(),
    ///                  TIMER.as_ref().unwrap(),
    ///                  frame_allocator,
    ///                 );
    ///   }
    ///
    ///   let frame_buffer = frame_allocator.get_frame().unwrap();
    ///
    ///   let result = rx.start(frame_buffer, rx_done_callback);
    ///
    ///   fn rx_done_callback(result: Result<RxOk, Error>) {
    ///     match result {
    ///       Ok(rx_ok) => { /* Do something with received frame */ },
    ///       Err(Error::InvalidFrame) => { /* Handle error */ },
    ///       Err(_) => { /* Handle other errors */ },
    ///     }
    ///   }
    /// # }
    /// ```
    pub fn start(
        &self,
        shared_resources: &'static mut TimeSlicedResources,
        rx_buffer: FrameBuffer<'static>,
        rx_done_callback: RxDoneCallback,
    ) -> Result<(), Error> {
        // TODO: return error if already receiving
        self.use_data(|d| {
            d.shared_resources = Some(shared_resources);
            let shared_resources = d.shared_resources.as_mut().unwrap();
            let ppi_ch = shared_resources.ppi_channels[0].take().unwrap();

            d.receive_done_callback = Some(rx_done_callback);
            let result = shared_resources.timestamp_channel.start_capturing(&ppi_ch);
            debug_assert!(result.is_ok());
            ppi_ch.enable();
            shared_resources.phy.rx(RxRequest::new(
                rx_buffer,
                Rx::phy_rx_callback,
                self.callback_data,
            )
            .with_ppi_channel_on_phyend(ppi_ch)
            .now())
        })
    }

    fn phy_rx_callback(
        result: Result<PhyRxOk, Error>,
        context: Context,
        resources: &mut RxResources,
    ) {
        defmt::info!("rx callback");

        Rx::use_data_from_context(context, |d| {
            let ppi_ch = resources.phyend_ppi_channel().unwrap();
            let sh_res = d.shared_resources.as_mut().unwrap();
            ppi_ch.disable();
            let result = sh_res.timestamp_channel.stop_capturing(&ppi_ch);
            debug_assert!(result.is_ok());
            sh_res.ppi_channels[0] = Some(ppi_ch);
        });

        match result {
            Ok(rx_ok) => {
                let frame = Frame::from_frame_buffer(&rx_ok.frame);
                if let Ok(frame) = frame {
                    Rx::use_data_from_context(context, |d| {
                        let sh_res = d.shared_resources.as_mut().unwrap();

                        let filter = Filter::new(d.pib);
                        let filter_result = filter.filter_parsed_frame_part(&frame);
                        let filter_passed = filter_result.is_ok();

                        let ar_option = frame.ar().unwrap();
                        let ack_requested = ar_option.is_some() && ar_option.unwrap();

                        let phyend_timestamp = Rx::phyend_timestamp(&sh_res.timestamp_channel);

                        if filter_passed && ack_requested {
                            // TODO: Handle transmitting ACK after relevant fields are received
                            //       (src addr, security?)

                            let mut new_rx_result = RxOk::new(rx_ok.frame, phyend_timestamp);

                            let ack_generate_result =
                                AckGenerator::new(d.ack_frame_allocator).generate_ack_for(&frame);
                            let ack_frame = ack_generate_result.unwrap();
                            new_rx_result.ack = Some(ack_frame);

                            let prev_rx_result = d.rx_result.replace(Ok(new_rx_result));
                            debug_assert!(prev_rx_result.is_none());

                            let ppi_ch = sh_res.ppi_channels[0].take().unwrap();
                            // TODO: Replace magic number 192 with AIFS
                            // TODO: Get TX ramp up time + some other delay (40 + 23) from Phy
                            let target_tx_time = Timestamp::wrapping_add(phyend_timestamp, 192);
                            let target_tx_start_time = Timestamp::wrapping_sub(target_tx_time, 63);
                            let timer_channel = &mut sh_res.timer_task_channel;
                            let timer_result =
                                timer_channel.trigger_at(&ppi_ch, target_tx_start_time);
                            timer_result.unwrap();

                            ppi_ch.enable();

                            let rx_result_ref = d.rx_result.as_ref().unwrap();
                            let rx_ok_ref = rx_result_ref.as_ref().unwrap();
                            let ack_ref = rx_ok_ref.ack.as_ref().unwrap();
                            let tx_request =
                                TxRequest::new(ack_ref, Rx::phy_tx_ack_callback, context)
                                    .at_event(ppi_ch);
                            let tx_detectability_delay = tx_request.detectability_delay();
                            let tx_detectability_timestamp = Timestamp::wrapping_add(
                                target_tx_start_time,
                                tx_detectability_delay,
                            );
                            let tx_result = sh_res.phy.tx(tx_request);
                            debug_assert!(tx_result.is_ok());

                            if sh_res
                                .timestamp_timer
                                .was_timestamp_in_past(&target_tx_start_time)
                                .unwrap()
                            {
                                while !sh_res
                                    .timestamp_timer
                                    .was_timestamp_in_past(&tx_detectability_timestamp)
                                    .unwrap()
                                {}
                                if !sh_res.phy.was_tx_started().unwrap() {
                                    let mut rx_result = d.rx_result.take().unwrap();
                                    rx_result.as_mut().unwrap().ack = None;
                                    Rx::notify_rx_done(d, rx_result);
                                    // TODO: abort hanged TX in Phy
                                    /*
                                    let result = d
                                        .timer
                                        .stop_triggering_task(d.timer_trigger_handle.take().unwrap(), &ppi_ch);
                                    debug_assert!(result.is_ok());
                                    */
                                }
                            }
                        } else {
                            let result = if filter_passed || d.pib.get_promiscuous() {
                                Ok(RxOk::new(rx_ok.frame, phyend_timestamp))
                            } else {
                                Err(filter_result.err().unwrap())
                            };

                            Rx::notify_rx_done(d, result);
                        }
                    });
                } else {
                    Rx::use_data_from_context(context, |d| {
                        if d.pib.get_promiscuous() {
                            Rx::notify_rx_done(
                                d,
                                Ok(RxOk::new(
                                    rx_ok.frame,
                                    Rx::phyend_timestamp(
                                        &d.shared_resources.as_ref().unwrap().timestamp_channel,
                                    ),
                                )),
                            )
                        } else {
                            Rx::notify_rx_done(d, Err(Error::InvalidFrame));
                        }
                    });
                }
            }
            Err(e) => {
                Rx::use_data_from_context(context, |d| Rx::notify_rx_done(d, Err(e)));
            }
        }
    }

    fn phyend_timestamp(timestamp_channel: &<Timer as Timestamper>::Channel) -> Timestamp {
        timestamp_channel.timestamp().unwrap()
    }

    fn phy_tx_ack_callback(
        _result: Result<(), Error>,
        context: Context,
        resources: &mut TxResources,
    ) {
        Rx::use_data_from_context(context, |d| {
            let sh_res = d.shared_resources.as_mut().unwrap();
            let ppi_ch = resources.start_channel().unwrap();
            ppi_ch.disable();
            let result = sh_res.timer_task_channel.disable(&ppi_ch);
            debug_assert!(result.is_ok());

            sh_res.ppi_channels[0] = Some(ppi_ch);

            let rx_result = d.rx_result.take();
            Rx::notify_rx_done(d, rx_result.unwrap());
        });
    }

    fn notify_rx_done(d: &mut CallbackData, result: Result<RxOk, Error>) {
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
