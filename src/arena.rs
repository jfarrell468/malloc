use crate::allocator::{align_up, AllocError, Allocator};
use crate::heap::Heap;
use std::ptr::NonNull;

#[derive(Debug)]
pub struct Arena {
    heap: Heap,
    cursor: usize,
}

impl Arena {
    pub fn new(size: usize, align: usize) -> Result<Arena, AllocError> {
        let mut arena = Arena {
            heap: Heap::new(),
            cursor: 0,
        };
        arena.heap.allocate(align_up(size, align), align)?;
        Ok(arena)
    }
    pub fn max_size(&self) -> usize {
        self.heap.size()
    }
    pub fn offset(&self, off: usize) -> Result<NonNull<u8>, AllocError> {
        // TODO: align?
        if off > self.cursor {
            return Err(AllocError::OutOfBounds);
        }
        self.heap.offset(off)
    }
    pub fn offset_from(&self, addr: NonNull<u8>) -> Result<usize, AllocError> {
        let diff = self.heap.offset_from(addr)?;
        if diff > self.cursor {
            return Err(AllocError::OutOfBounds);
        }
        Ok(diff)
    }
}

unsafe impl Allocator for Arena {
    fn allocate(&mut self, size: usize, align: usize) -> Result<NonNull<u8>, AllocError> {
        // TODO: Cursor might not be aligned for the requested alignment.
        let aligned_size = align_up(size, align);
        if self.cursor + aligned_size > self.heap.size() {
            return Err(AllocError::OutOfMemory);
        }
        let addr = self.heap.offset(self.cursor)?;
        self.cursor += aligned_size;
        Ok(addr)
    }
    unsafe fn deallocate(&mut self, _ptr: NonNull<u8>) -> Result<(), AllocError> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let arena = Arena::new(1024, 128).expect("Failed to create arena");
        assert_eq!(arena.cursor, 0);
        assert_eq!(arena.max_size(), 1024);
    }

    #[test]
    fn test_allocate() {
        let mut arena = Arena::new(1024, 128).expect("Failed to create arena");
        let addr = arena.allocate(8, 8).expect("Failed to allocate");
        assert_eq!(addr, arena.offset(0).expect("Offset failed"));
        assert_eq!(arena.cursor, 8);
        let addr = arena.allocate(8, 8).expect("Failed to allocate");
        assert_eq!(addr, arena.offset(8).expect("Offset failed"));
        assert_eq!(arena.cursor, 16);
        assert_eq!(arena.allocate(1024, 8), Err(AllocError::OutOfMemory));
        assert_eq!(arena.cursor, 16);
    }

    #[test]
    fn test_offset() {
        let mut arena = Arena::new(1024, 128).expect("Failed to create arena");
        assert!(arena.allocate(8, 8).is_ok());
        assert!(arena.offset(4).is_ok());
        assert_eq!(arena.offset(10), Err(AllocError::OutOfBounds));
    }

    #[test]
    fn test_deallocate() {
        let mut arena = Arena::new(1024, 128).expect("Failed to create arena");
        assert!(arena.allocate(8, 8).is_ok());
        assert_eq!(arena.cursor, 8);
        unsafe {
            assert!(arena
                .deallocate(arena.offset(0).expect("Offset failed"))
                .is_ok());
        }
        assert_eq!(arena.cursor, 8);
    }
}
