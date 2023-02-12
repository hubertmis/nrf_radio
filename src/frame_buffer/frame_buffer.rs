use core::any::Any;
use core::fmt::{Debug, Formatter};
use core::ops::{Deref, DerefMut};

pub type DropFunction = fn(&mut FrameBuffer, DropMetadata);
pub type DropMetadata = &'static (dyn Any + Send + Sync);

/// Buffer representing a radio frame data and buffer management metadata
///
/// This buffer is opaque for radio protocols. It can contain data necessary for any protocol.
///
/// Buffers are to be allocated by a [`FrameAllocator`](super::frame_allocator::FrameAllocator).
/// Buffers are released in their destructor methods provided by the buffer allocator.
///
/// [`FrameBuffer`] is a smart pointer dereferencing a bytes slice.
pub struct FrameBuffer {
    frame: &'static mut [u8],
    drop_fn: Option<DropFunction>,
    drop_md: DropMetadata,
}

impl FrameBuffer {
    /// Creates a new buffer
    ///
    /// ---
    /// **NOTE** this function is to be used only by [frame buffer
    /// allocators](super::frame_allocator::FrameAllocator) or in tests.
    ///
    /// ---
    ///
    /// The buffer structure points to the `frame` memory slice provided by the caller. This slice
    /// is considered owned by the [`FrameBuffer`] until the `FrameBuffer` is dropped. While the
    /// slice is owned by the `FrameBuffer` it shall not be accessed in any other way than by
    /// dereferencing the `FrameBuffer`.
    ///
    /// Releasing the memory slice for other use is indicated by the `FrameBuffer` by calling the
    /// `drop_fn` function passing a reference to the buffer being freed and a caller-defined
    /// `drop_md` reference.
    pub fn new(
        frame: &'static mut [u8],
        drop_fn: Option<DropFunction>,
        drop_md: DropMetadata,
    ) -> Self {
        Self {
            frame,
            drop_fn,
            drop_md,
        }
    }
}

impl Debug for FrameBuffer {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.debug_struct("FrameBuffer")
            .field("frame", &self.frame)
            .finish()
    }
}

impl Deref for FrameBuffer {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl DerefMut for FrameBuffer {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.frame
    }
}

impl Drop for FrameBuffer {
    fn drop(&mut self) {
        if let Some(drop_fn) = self.drop_fn {
            drop_fn(self, self.drop_md)
        }
    }
}

impl PartialEq for FrameBuffer {
    fn eq(&self, other: &Self) -> bool {
        self.frame == other.frame
    }
}

// TODO: conditional on features
impl defmt::Format for FrameBuffer {
    fn format(&self, fmt: defmt::Formatter) {
        defmt::write!(fmt, "Frame({:x})", self.frame);
    }
}
