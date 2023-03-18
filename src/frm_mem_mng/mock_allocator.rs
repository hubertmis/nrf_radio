//! Basic allocator intended to be used in simple unit tests
//!
//! The limitation of this allocator is capability of allocating single frame buffer.
//! For unit tests requiring more than a single buffer a more complex allocator must be used.

#[cfg(not(feature = "mocked_platform"))]
compile_error!("MockAllocator cannot be used on real hardware");

use super::frame_allocator::FrameAllocator;
use super::frame_buffer::{DropMetadata, FrameBuffer};
use crate::error::Error;

use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;

#[cfg(test)]
const NUM_BUFS: usize = 1;
const BUF_SIZE: usize = 128;

static FRAME_ALLOCATOR: MockAllocator = MockAllocator {
    is_allocated: AtomicBool::new(false),
};
static mut DATA: [u8; BUF_SIZE] = [0; BUF_SIZE];

/// Object representing the allocator mock
pub struct MockAllocator {
    is_allocated: AtomicBool,
}

impl MockAllocator {
    /// Reset module
    ///
    /// This function is intended to be used between unit tests
    #[doc(hidden)]
    pub fn reset() {
        FRAME_ALLOCATOR.is_allocated.store(false, Ordering::SeqCst);
    }

    /// Helper function to get access to the frame allocator singleton
    fn use_frame_allocator<F, R>(func: F) -> R
    where
        F: FnOnce(&MockAllocator) -> R,
    {
        func(&FRAME_ALLOCATOR)
    }

    /// Initializes the [`MockAllocator`] singleton
    ///
    /// This function returns a phantom allocator to implement the
    /// [`FrameAllocator`](super::frame_allocator::FrameAllocator) trait. The content of the
    /// phantom allocator is useless, because on each method call the global singleton data is used
    /// instead of the phantom instance data.
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::frm_mem_mng::mock_allocator::MockAllocator;
    ///
    ///   let allocator = MockAllocator::new();
    /// ```
    pub fn new() -> Self {
        // create a phantom allocator
        Self {
            is_allocated: AtomicBool::new(true),
        }
    }

    /// Releases an allocated frame
    ///
    /// Function called when any [`FrameBuffer`](super::frame_buffer::FrameBuffer) created by this
    /// allocator is dropped.
    fn release_frame(_frame: &mut FrameBuffer, _metadata: DropMetadata) {
        MockAllocator::use_frame_allocator(|fa| {
            let was_allocated =
                fa.is_allocated
                    .compare_exchange(true, false, Ordering::Release, Ordering::Relaxed);
            assert!(was_allocated.unwrap());
        });
    }
}

impl FrameAllocator for MockAllocator {
    fn get_frame(&self) -> Result<FrameBuffer<'static>, Error> {
        MockAllocator::use_frame_allocator(|fa| {
            let was_allocated =
                fa.is_allocated
                    .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if was_allocated.is_ok() {
                Ok(FrameBuffer::new(
                    // Safety: guarded by is_allocated mutex acquired here
                    unsafe { &mut DATA },
                    Some(MockAllocator::release_frame),
                    &None::<usize>,
                ))
            } else {
                Err(Error::NoMemory)
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::frame_allocator::tests::*;
    use super::*;
    use serial_test::serial;

    static PHANTOM_ALLOCATOR: MockAllocator = MockAllocator {
        is_allocated: AtomicBool::new(true),
    };

    #[test]
    #[serial]
    fn test_allocate_a_frame() {
        MockAllocator::reset();
        MockAllocator::new();

        test_body_allocate_a_frame(&PHANTOM_ALLOCATOR);
    }

    #[test]
    #[serial]
    fn test_allocate_more_frames_than_available() {
        MockAllocator::reset();
        MockAllocator::new();

        test_body_allocate_more_frames_than_available(&PHANTOM_ALLOCATOR, NUM_BUFS);
    }

    #[test]
    #[serial]
    fn test_allocated_frame_stored_in_static_variable() {
        MockAllocator::reset();
        MockAllocator::new();

        test_body_allocated_frame_stored_in_static_variable(&PHANTOM_ALLOCATOR, NUM_BUFS);
    }

    #[test]
    #[serial]
    fn test_allocated_frame_dropped_after_released_from_static_variable() {
        MockAllocator::reset();
        MockAllocator::new();

        test_body_allocated_frame_dropped_after_released_from_static_variable(
            &PHANTOM_ALLOCATOR,
            NUM_BUFS,
        );
    }
}
