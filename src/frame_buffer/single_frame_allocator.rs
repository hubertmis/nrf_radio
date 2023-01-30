use super::frame_allocator::{FrameAllocator, Free, GetFrame};
use super::frame_buffer::FrameBuffer;
use crate::crit_sect;
use crate::error::Error;
use core::{cell::UnsafeCell, sync::atomic::AtomicBool};

#[cfg(test)]
const NUM_BUFS: usize = 1;

static FRAME_ALLOCATOR: SingleFrameAllocator = SingleFrameAllocator::new();

/// Simple radio frames allocator
///
/// Has [`FrameAllocator`](super::frame_allocator::FrameAllocator) trait.
///
/// Supports only one instance, allocating single frame.
pub struct SingleFrameAllocator {
    is_allocated: AtomicBool,
    data: UnsafeCell<[u8; SingleFrameAllocator::BUF_SIZE]>,
}

impl SingleFrameAllocator {
    const BUF_SIZE: usize = 128;

    /// Helper function to get access to the frame allocator singleton
    pub fn use_frame_allocator<F>(func: F)
    where
        F: FnOnce(&SingleFrameAllocator),
    {
        crit_sect::locked(|_cs| {
            let frame_allocator = &FRAME_ALLOCATOR;
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
    pub const fn new() -> Self {
        Self {
            is_allocated: AtomicBool::new(false),
            data: UnsafeCell::new([0; Self::BUF_SIZE]),
        }
    }
}

// Safety: All methods of SingleFrameAllocator can be called from multiple threads and it's internal state is always coherent.
unsafe impl Sync for SingleFrameAllocator {}

impl GetFrame for SingleFrameAllocator {
    fn get_frame(&self) -> Result<FrameBuffer, Error> {
        if self
            .is_allocated
            .compare_exchange(
                false,
                true,
                core::sync::atomic::Ordering::Release,
                core::sync::atomic::Ordering::Relaxed,
            )
            .is_ok()
        {
            Ok(FrameBuffer::new(
                FrameAllocator::SingleFrameAllocator(self),
                // Safety: We are in this branch only if we successfully locked the allocator, thus we are the only one that can access the shared internal state.
                unsafe { &mut *self.data.get() },
            ))
        } else {
            Err(Error::WouldBlock)
        }
    }
}

impl Free for SingleFrameAllocator {
    /// Releases an allocated frame
    ///
    /// Function called when any [`FrameBuffer`](super::frame_buffer::FrameBuffer) created by this
    /// allocator is dropped.
    fn free(&self) {
        self.is_allocated
            .store(false, core::sync::atomic::Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use super::super::frame_allocator::tests::*;
    use super::*;
    use serial_test::serial;

    #[test]
    fn test_allocate_a_frame() {
        let allocator = SingleFrameAllocator::new();

        test_body_allocate_a_frame(&allocator);
    }

    #[test]
    fn test_allocate_more_frames_than_available() {
        let allocator = SingleFrameAllocator::new();

        test_body_allocate_more_frames_than_available(&allocator, NUM_BUFS);
    }

    #[test]
    #[serial]
    fn test_allocated_frame_stored_in_static_variable() {
        static ALLOCATOR: SingleFrameAllocator = SingleFrameAllocator::new();

        test_body_allocated_frame_stored_in_static_variable(&ALLOCATOR, NUM_BUFS);
    }

    #[test]
    #[serial]
    fn test_allocated_frame_dropped_after_released_from_static_variable() {
        static ALLOCATOR: SingleFrameAllocator = SingleFrameAllocator::new();

        test_body_allocated_frame_dropped_after_released_from_static_variable(&ALLOCATOR, NUM_BUFS);
    }
}
