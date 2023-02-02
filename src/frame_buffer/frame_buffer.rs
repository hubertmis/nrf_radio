use core::fmt::{Debug, Formatter};
use core::ops::{Deref, DerefMut};

use crate::frame_buffer::frame_allocator::{FrameAllocator, Free};

/// Buffer representing a radio frame data and buffer management metadata
///
/// This buffer is opaque for radio protocols. It can contain data necessary for any protocol.
///
/// Buffers are to be allocated by a [`FrameAllocator`](super::frame_allocator::FrameAllocator).
/// Buffers are released in their destructor methods provided by the buffer allocator.
///
/// [`FrameBuffer`] is a smart pointer dereferencing a bytes slice.
pub struct FrameBuffer<'a> {
    allocator: FrameAllocator<'a>,
    frame: &'a mut [u8],
}

impl<'a> FrameBuffer<'a> {
    pub fn new(allocator: FrameAllocator<'a>, frame: &'a mut [u8]) -> Self {
        Self { allocator, frame }
    }
}

impl<'a> Debug for FrameBuffer<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.debug_struct("FrameBuffer")
            .field("frame", &self.frame)
            .finish()
    }
}

impl<'a> Deref for FrameBuffer<'a> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl<'a> DerefMut for FrameBuffer<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.frame
    }
}

impl<'a> Drop for FrameBuffer<'a> {
    fn drop(&mut self) {
        self.allocator.free();
    }
}

impl<'a> PartialEq for FrameBuffer<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.frame == other.frame
    }
}

// TODO: conditional on features
impl<'a> defmt::Format for FrameBuffer<'a> {
    fn format(&self, fmt: defmt::Formatter) {
        defmt::write!(fmt, "Frame({:x})", self.frame);
    }
}
