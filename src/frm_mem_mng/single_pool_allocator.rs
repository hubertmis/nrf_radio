//! Frame buffers allocator capable of allocating multiple frames from a single pool
//!
//! The size of the pool is set as a constant in the implementation of the allocator.

use super::frame_allocator::FrameAllocator;
use super::frame_buffer::{DropMetadata, FrameBuffer};
use crate::error::Error;

use core::sync::atomic::AtomicBool;
use core::sync::atomic::Ordering;

const NUM_BUFS: usize = 16;
const BUF_SIZE: usize = 128;

// using magic number because of https://github.com/JoshMcguigan/arr_macro/issues/2
static IS_ALLOCATED: [AtomicBool; NUM_BUFS] = arr_macro::arr![AtomicBool::new(false); 16];
static mut DATA: [[u8; BUF_SIZE]; NUM_BUFS] = [[0; BUF_SIZE]; NUM_BUFS];

/// Object representing the allocator
///
/// It is an empty object, because all the allocator data is static.
pub struct SinglePoolAllocator {}

impl SinglePoolAllocator {
    /// Reset module
    ///
    /// This function is intended to be used between unit tests
    #[doc(hidden)]
    pub fn reset() {
        for is_allocated in IS_ALLOCATED.iter() {
            is_allocated.store(false, Ordering::SeqCst);
        }
    }

    /// Returns an phantom object used to access the [`SinglePoolAllocator`] singleton
    ///
    /// This function returns a phantom allocator to implement the
    /// [`FrameAllocator`](super::frame_allocator::FrameAllocator) trait.
    ///
    /// # Examples
    ///
    /// ```
    ///   use nrf_radio::frm_mem_mng::single_pool_allocator::SinglePoolAllocator;
    ///
    ///   let allocator = SinglePoolAllocator::new();
    /// ```
    pub fn new() -> Self {
        Self {}
    }

    /// Releases an allocated frame
    ///
    /// Function called when any [`FrameBuffer`](super::frame_buffer::FrameBuffer) created by this
    /// allocator is dropped.
    fn release_frame(_frame: &mut FrameBuffer, metadata: DropMetadata) {
        let is_allocated = metadata.downcast_ref::<AtomicBool>().unwrap();
        let was_allocated =
            is_allocated.compare_exchange(true, false, Ordering::Release, Ordering::Relaxed);
        assert!(was_allocated.unwrap());
    }
}

impl FrameAllocator for SinglePoolAllocator {
    fn get_frame(&self) -> Result<FrameBuffer<'static>, Error> {
        for (idx, is_allocated) in IS_ALLOCATED.iter().enumerate() {
            let was_allocated =
                is_allocated.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed);
            if was_allocated == Ok(false) {
                return Ok(FrameBuffer::new(
                    // Safety: guarded by IS_ALLOCATED mutex acquired here
                    unsafe { &mut DATA[idx] },
                    Some(SinglePoolAllocator::release_frame),
                    &IS_ALLOCATED[idx],
                ));
            }
        }

        Err(Error::NoMemory)
    }
}

#[cfg(test)]
mod tests {
    use super::super::frame_allocator::tests::*;
    use super::*;
    use serial_test::serial;

    static PHANTOM_ALLOCATOR: SinglePoolAllocator = SinglePoolAllocator {};

    #[test]
    #[serial]
    fn test_allocate_a_frame() {
        SinglePoolAllocator::reset();

        test_body_allocate_a_frame(&PHANTOM_ALLOCATOR);
    }

    #[test]
    #[serial]
    fn test_allocate_more_frames_than_available() {
        SinglePoolAllocator::reset();

        test_body_allocate_more_frames_than_available(&PHANTOM_ALLOCATOR, NUM_BUFS);
    }

    #[test]
    #[serial]
    fn test_allocated_frame_dropped_after_released() {
        SinglePoolAllocator::reset();

        test_body_allocated_frame_dropped_after_released(&PHANTOM_ALLOCATOR, NUM_BUFS);
    }
}
