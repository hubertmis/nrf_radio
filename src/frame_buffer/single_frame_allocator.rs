use super::frame_allocator::FrameAllocator;
use super::frame_buffer::{DropMetadata, FrameBuffer};
use crate::crit_sect;
use crate::error::Error;
use crate::mutex::Mutex;
use core::cell::RefCell;

#[cfg(test)]
const NUM_BUFS: usize = 1;
const BUF_SIZE: usize = 128;

static FRAME_ALLOCATOR: Mutex<RefCell<Option<SingleFrameAllocator>>> =
    Mutex::new(RefCell::new(None));
static mut DATA: [u8; BUF_SIZE] = [0; BUF_SIZE];

/// Simple radio frames allocator
///
/// Has [`FrameAllocator`](super::frame_allocator::FrameAllocator) trait.
///
/// Supports only one instance, allocating single frame.
pub struct SingleFrameAllocator {
    is_allocated: bool,
}

impl SingleFrameAllocator {
    /// Reset module
    ///
    /// This function is intended to be used between unit tests
    #[doc(hidden)]
    pub fn reset() {
        crit_sect::locked(|cs| {
            FRAME_ALLOCATOR.borrow(cs).replace(None);
        });
    }

    /// Helper function to get access to the frame allocator singleton
    fn use_frame_allocator<F>(func: F)
    where
        F: FnOnce(&mut SingleFrameAllocator),
    {
        crit_sect::locked(|cs| {
            let frame_allocator_option = &mut FRAME_ALLOCATOR.borrow(cs).borrow_mut();
            let frame_allocator = &mut frame_allocator_option.as_mut().unwrap();
            func(frame_allocator);
        });
    }

    /// Initializes the [`SingleFrameAllocator`] singleton
    ///
    /// This function returns a phantom allocator to implement the
    /// [`FrameAllocator`](super::frame_allocator::FrameAllocator) trait. The content of the
    /// phantom allocator is useless, because on each method call the global singleton data is used
    /// instead of the phantom instance data.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    ///   use nrf_radio::frame_buffer::single_frame_allocator::SingleFrameAllocator;
    ///
    ///   let allocator = SingleFrameAllocator::new();
    /// # }
    /// ```
    pub fn new() -> Self {
        let frame_allocator = Self {
            is_allocated: false,
        };

        crit_sect::locked(|cs| {
            let prev_frame_allocator = FRAME_ALLOCATOR.borrow(cs).replace(Some(frame_allocator));
            assert!(prev_frame_allocator.is_none());
        });

        let phantom_allocator = Self { is_allocated: true };
        phantom_allocator
    }

    /// Releases an allocated frame
    ///
    /// Function called when any [`FrameBuffer`](super::frame_buffer::FrameBuffer) created by this
    /// allocator is dropped.
    fn release_frame(_frame: &mut FrameBuffer, _metadata: DropMetadata) {
        SingleFrameAllocator::use_frame_allocator(|fa| {
            assert!(fa.is_allocated);
            fa.is_allocated = false;
        });
    }
}

impl FrameAllocator for SingleFrameAllocator {
    fn get_frame(&self) -> Result<FrameBuffer<'static>, Error> {
        let mut result = Err(Error::WouldBlock);
        SingleFrameAllocator::use_frame_allocator(|fa| {
            result = if fa.is_allocated {
                Err(Error::WouldBlock)
            } else {
                fa.is_allocated = true;
                Ok(FrameBuffer::new(
                    unsafe { &mut DATA },
                    Some(SingleFrameAllocator::release_frame),
                    &None::<usize>,
                ))
            }
        });

        result
    }
}

#[cfg(test)]
mod tests {
    use super::super::frame_allocator::tests::*;
    use super::*;
    use serial_test::serial;

    static PHANTOM_ALLOCATOR: SingleFrameAllocator = SingleFrameAllocator { is_allocated: true };

    #[test]
    #[serial]
    fn test_allocate_a_frame() {
        SingleFrameAllocator::reset();
        SingleFrameAllocator::new();

        test_body_allocate_a_frame(&PHANTOM_ALLOCATOR);
    }

    #[test]
    #[serial]
    fn test_allocate_more_frames_than_available() {
        SingleFrameAllocator::reset();
        SingleFrameAllocator::new();

        test_body_allocate_more_frames_than_available(&PHANTOM_ALLOCATOR, NUM_BUFS);
    }

    #[test]
    #[serial]
    fn test_allocated_frame_stored_in_static_variable() {
        SingleFrameAllocator::reset();
        SingleFrameAllocator::new();

        test_body_allocated_frame_stored_in_static_variable(&PHANTOM_ALLOCATOR, NUM_BUFS);
    }

    #[test]
    #[serial]
    fn test_allocated_frame_dropped_after_released_from_static_variable() {
        SingleFrameAllocator::reset();
        SingleFrameAllocator::new();

        test_body_allocated_frame_dropped_after_released_from_static_variable(
            &PHANTOM_ALLOCATOR,
            NUM_BUFS,
        );
    }
}
