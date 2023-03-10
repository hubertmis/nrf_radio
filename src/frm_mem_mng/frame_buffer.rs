use core::any::Any;
use core::fmt::{Debug, Formatter};
use core::ops::{Deref, DerefMut};

/// Function called when a FrameBuffer instance is dropped
///
/// This function is intended to be implemeted by an
/// [allocator](super::frame_allocator::FrameAllocator) creating given
/// [`FrameBuffer`] instance to deallocate the frame when dropped.
pub type DropFunction = fn(&mut FrameBuffer, DropMetadata);

/// Metadata passed as a parameter to the [`DropFunction`] function
///
/// When a [`FrameBuffer`] instance is dropped, associated [`DropFunction`] is called with
/// parameters presenting reference to  the [`FrameBuffer`] instance and `DropMetadata` being any
/// metadata selected by the [frame allocator](super::frame_allocator::FrameAllocator). The
/// intention of `DropMetadata` is to help the allocator to identify the memory to free. It might
/// contain an address, pointer, index in an array or any other useful data.
pub type DropMetadata = &'static (dyn Any + Send + Sync);

// TODO: Implement MutFrameBuffer as a separated type?
// User should be able to create frames to transmit using an immutable buffer. But maybe such
// buffer shall be copied to mutable `FrameBuffer`?

/// Buffer representing a radio frame data and buffer management metadata
///
/// This buffer is opaque for radio protocols. It can contain data necessary for any protocol.
///
/// Buffers are to be allocated by a [`FrameAllocator`](super::frame_allocator::FrameAllocator).
/// Buffers are released in their destructor methods provided by the buffer allocator.
///
/// [`FrameBuffer`] is a smart pointer dereferencing a bytes slice.
pub struct FrameBuffer<'a> {
    frame: &'a mut [u8],
    drop_fn: Option<DropFunction>,
    drop_md: DropMetadata,
}

impl<'a> FrameBuffer<'a> {
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
    pub fn new(frame: &'a mut [u8], drop_fn: Option<DropFunction>, drop_md: DropMetadata) -> Self {
        Self {
            frame,
            drop_fn,
            drop_md,
        }
    }
}

impl Debug for FrameBuffer<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), core::fmt::Error> {
        f.debug_struct("FrameBuffer")
            .field("frame", &self.frame)
            .finish()
    }
}

impl Deref for FrameBuffer<'_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.frame
    }
}

impl DerefMut for FrameBuffer<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.frame
    }
}

impl Drop for FrameBuffer<'_> {
    fn drop(&mut self) {
        if let Some(drop_fn) = self.drop_fn {
            drop_fn(self, self.drop_md)
        }
    }
}

impl PartialEq for FrameBuffer<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.frame == other.frame
    }
}

// TODO: conditional on features
impl defmt::Format for FrameBuffer<'_> {
    fn format(&self, fmt: defmt::Formatter) {
        defmt::write!(fmt, "Frame({:x})", self.frame);
    }
}
