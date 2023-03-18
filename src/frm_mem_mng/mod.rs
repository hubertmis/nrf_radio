/// Contains a trait of all frame buffer allocators usable by this crate
pub mod frame_allocator;

/// Defines a buffer to contain a single frame
pub mod frame_buffer;

#[cfg(feature = "mocked_platform")]
pub mod mock_allocator;
pub mod single_frame_allocator;
pub mod single_pool_allocator;
