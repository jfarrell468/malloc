// An allocator that allows a single allocation of a heap, backed by mmap.

use crate::allocator::{align_up, AllocError, Allocator};
use libc::{mmap, munmap};
use std::ptr::NonNull;

#[derive(Debug)]
pub struct Heap {
    // Invariant:
    // addr.is_some() iff:
    //   1. addr contains a valid address (allocated with mmap)
    //   2. size > 0 (no 0-size allocations)
    addr: Option<NonNull<u8>>,
    size: usize,
}

impl Heap {
    pub fn new() -> Heap {
        Heap {
            addr: None,
            size: 0,
        }
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn offset(&self, off: usize) -> Result<NonNull<u8>, AllocError> {
        match self.addr {
            None => Err(AllocError::HeapNotAllocated),
            Some(addr) => {
                if off > self.size {
                    Err(AllocError::OutOfBounds)
                } else if off > isize::MAX as usize {
                    Err(AllocError::InsufficientAddressSpace)
                } else {
                    // Safety:
                    // - "off as isize" is safe because of bounds check above.
                    // - offset is safe because of bounds check above.
                    // - new_unchecked is safe because the heap is allocated (self.addr.is_some())
                    //   and we have checked that the offset is within the allocated space.
                    unsafe { Ok(NonNull::new_unchecked(addr.as_ptr().offset(off as isize))) }
                }
            },
        }
    }
    pub fn offset_from(&self, ptr: NonNull<u8>) -> Result<usize, AllocError> {
        match self.addr {
            None => Err(AllocError::HeapNotAllocated),
            Some(addr) => {
                // Safety:
                // - The heap is allocated (self.addr.is_some()) so addr is valid.
                // - After computing the diff, we check that addr is within the heap.
                let diff;
                unsafe { diff = ptr.as_ptr().offset_from(addr.as_ptr()) }
                if diff < 0 || diff as usize > self.size {
                    return Err(AllocError::OutOfBounds);
                }
                // Safety:
                // - We checked that diff > 0
                // - usize::MAX > isize::MAX
                Ok(diff as usize)
            },
        }
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        // println!("Dropping heap");
        if let Some(addr) = self.addr {
            // Safety:
            // - We only try to deallocate if the heap is allocated (self.addr.is_some())
            unsafe {
                self.deallocate(addr);
            }
        }
    }
}

unsafe impl Allocator for Heap {
    fn allocate(&mut self, size: usize, align: usize) -> Result<NonNull<u8>, AllocError> {
        if self.addr.is_some() {
            return Err(AllocError::HeapAlreadyAllocated);
        }
        assert_eq!(self.size, 0);  // Invariant
        // Safety:
        // - We check the return value of mmap
        // - We use NonNull::new to further check the returned address.
        // - We only modify self if we are going to return Ok().
        unsafe {
            let aligned_size = align_up(size, align);
            let addr;
            addr = mmap(
                std::ptr::null_mut(),
                aligned_size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            );
            if addr == libc::MAP_FAILED {
                Err(AllocError::MmapFailed)
            } else {
                // TODO: Check alignment
                match NonNull::new(std::mem::transmute::<*mut libc::c_void, *mut u8>(addr)) {
                    None => Err(AllocError::MmapFailed),
                    Some(addr) => {
                        self.addr = Some(addr);
                        self.size = aligned_size;
                        Ok(addr)
                    },
                }
            }
        }
    }
    unsafe fn deallocate(&mut self, ptr: NonNull<u8>) -> Result<(), AllocError> {
        // Safety:
        // - We check that the heap is allocated.
        // - We check that ptr matches the address of the heap.
        // - We check the return value of munmap.
        // - We only modify self if we are going to return Ok().
        match self.addr {
            None => Err(AllocError::HeapNotAllocated),
            Some(addr) => {
                if addr != ptr {
                    return Err(AllocError::InvalidAddress);
                }
                let result = munmap(
                    std::mem::transmute::<*mut u8, *mut libc::c_void>(addr.as_ptr()),
                    self.size,
                );
                if result != 0 {
                    return Err(AllocError::MunmapFailed);
                }
                self.addr = None;
                self.size = 0;
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let heap = Heap::new();
        assert_eq!(heap.size(), 0);
        assert!(heap.addr.is_none());
    }

    #[test]
    fn test_allocate() {
        let mut heap = Heap::new();
        assert!(heap.allocate(128, 16).is_ok());
        assert_eq!(heap.size(), 128);
        assert!(heap.addr.is_some());
    }

    #[test]
    fn test_offset() -> Result<(), AllocError> {
        let mut heap = Heap::new();
        assert_eq!(heap.offset(1), Err(AllocError::HeapNotAllocated));
        assert!(heap.allocate(128, 16).is_ok());
        assert_eq!(
            heap.offset(1)?,
            NonNull::new(unsafe { heap.addr.unwrap().as_ptr().offset(1) }).unwrap()
        );
        assert_eq!(heap.offset(1000), Err(AllocError::OutOfBounds));
        Ok(())
    }

    #[test]
    fn test_offset_from() {
        let mut heap = Heap::new();
        assert!(heap.allocate(128, 16).is_ok());
        unsafe {
            assert_eq!(heap.offset_from(heap.addr.unwrap()), Ok(0));
            assert_eq!(
                heap.offset_from(NonNull::new(heap.addr.unwrap().as_ptr().offset(10)).unwrap()),
                Ok(10)
            );
            assert_eq!(
                heap.offset_from(NonNull::new(heap.addr.unwrap().as_ptr().offset(-1)).unwrap()),
                Err(AllocError::OutOfBounds)
            );
            assert_eq!(
                heap.offset_from(NonNull::new(heap.addr.unwrap().as_ptr().offset(1000)).unwrap()),
                Err(AllocError::OutOfBounds)
            );
        }
    }

    #[test]
    fn test_alignment() {
        let mut heap = Heap::new();
        assert!(heap.allocate(128, 512).is_ok());
        assert_eq!(heap.size(), 512);
        assert!(heap.addr.is_some());
    }

    #[test]
    fn test_deallocate() -> Result<(), AllocError> {
        let mut heap = Heap::new();
        let mut x = 1;
        unsafe {
            assert_eq!(
                heap.deallocate(NonNull::new_unchecked(&mut x)),
                Err(AllocError::HeapNotAllocated)
            );
        }
        assert!(heap.allocate(128, 16).is_ok());
        unsafe {
            assert_eq!(
                heap.deallocate(heap.offset(1)?),
                Err(AllocError::InvalidAddress)
            );
            assert!(heap.deallocate(heap.addr.unwrap()).is_ok());
        }
        assert_eq!(heap.size(), 0);
        assert!(heap.addr.is_none());
        unsafe {
            assert_eq!(
                heap.deallocate(NonNull::new_unchecked(&mut x)),
                Err(AllocError::HeapNotAllocated)
            );
        }
        Ok(())
    }
}
