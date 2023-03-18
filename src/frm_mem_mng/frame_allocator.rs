use super::frame_buffer::FrameBuffer;
use crate::error::Error;

#[cfg(test)]
use mockall::*;

/// Trait of any frame buffers allocator for radio frames
#[cfg_attr(test, automock)]
pub trait FrameAllocator: Sync {
    // TODO: consider size of the requested frame
    /// Allocates a single frame
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate nrf_radio;
    /// # missing_test_fns!();
    /// # fn main() {
    ///   use nrf_radio::frm_mem_mng::frame_allocator::FrameAllocator; // Import trait
    ///   use nrf_radio::frm_mem_mng::single_frame_allocator::SingleFrameAllocator;
    ///
    ///   let allocator = SingleFrameAllocator::new();
    ///
    ///   {
    ///     let frame_result = allocator.get_frame();
    ///     assert!(frame_result.is_ok());
    ///     // frame is dropped when leaving this scope
    ///   }
    ///
    ///   // a new frame can be allocated
    ///   let frame_result = allocator.get_frame();
    ///   assert!(frame_result.is_ok());
    ///
    ///   // if the allocator supports only one frame, no more frames can be allocated
    ///   let frame_error = allocator.get_frame();
    ///   assert!(frame_error.is_err());
    /// # }
    /// ```
    fn get_frame(&self) -> Result<FrameBuffer<'static>, Error>;
}

#[cfg(test)]
pub mod tests {
    use super::*;

    fn allocate_number_of_frames<FA: FrameAllocator>(allocator: &FA, i: usize) -> Vec<FrameBuffer> {
        let mut frames = Vec::new();

        for _ in 0..i {
            let frame = allocator.get_frame();
            assert!(frame.is_ok());
            frames.push(frame.unwrap());
        }

        frames
    }

    fn allocate_all_frames<FA: FrameAllocator>(
        allocator: &FA,
        num_bufs: usize,
    ) -> Vec<FrameBuffer> {
        allocate_number_of_frames(allocator, num_bufs)
    }

    fn allocate_all_frames_but_one<FA: FrameAllocator>(
        allocator: &FA,
        num_bufs: usize,
    ) -> Vec<FrameBuffer> {
        allocate_number_of_frames(allocator, num_bufs - 1)
    }

    pub fn test_body_allocate_a_frame<FA: FrameAllocator>(allocator: &FA) {
        let frame = allocator.get_frame();
        assert!(frame.is_ok());

        let mut frame = frame.unwrap();
        for i in 0..frame.len() {
            frame[i] = i as u8;
        }
    }

    pub fn test_body_allocate_more_frames_than_available<FA: FrameAllocator>(
        allocator: &FA,
        num_available_frames: usize,
    ) {
        let _frames = allocate_all_frames(allocator, num_available_frames);

        let frame = allocator.get_frame();
        assert!(frame.is_err());
        // TODO: Verify which error
    }

    pub fn test_body_allocated_frame_dropped_after_released<FA: FrameAllocator>(
        allocator: &FA,
        num_available_frames: usize,
    ) {
        let _frames = allocate_all_frames_but_one(allocator, num_available_frames);

        {
            let frame = allocator.get_frame();
            assert!(frame.is_ok());
        }

        let frame = allocator.get_frame();
        assert!(frame.is_ok());
    }
}
