use std::ptr::NonNull;

pub fn is_aligned(size: usize, align: usize) -> bool {
    size & (align - 1) == 0
}

pub fn align_down(size: usize, align: usize) -> usize {
    size & !(align - 1)
}

pub fn align_up(size: usize, align: usize) -> usize {
    // (I always look this one up. >_>)
    align_down(size + align - 1, align)
}

#[derive(Debug, PartialEq)]
pub enum AllocError {
    HeapAlreadyAllocated,
    HeapNotAllocated,
    MapFailed,
    OutOfMemory,
    OutOfBounds,
    InsufficientAddressSpace,
    InvalidAddress,
    Unimplemented,
}

// Simplified version of std::alloc::Allocator
pub unsafe trait Allocator {
    fn allocate(&mut self, size: usize, align: usize) -> Result<NonNull<u8>, AllocError>;
    unsafe fn deallocate(&mut self, ptr: NonNull<u8>) -> Result<(), AllocError>;
}
