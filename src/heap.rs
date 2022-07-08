use crate::allocator::{align_up, AllocError, Allocator};
use libc::{mmap, munmap};
use std::ptr::NonNull;

#[derive(Debug)]
pub struct Heap {
    // TODO: Option<NonNull<u8>>
    addr: *mut u8,
    size: usize,
}

impl Heap {
    pub fn new() -> Heap {
        Heap {
            addr: std::ptr::null_mut(),
            size: 0,
        }
    }
    pub fn size(&self) -> usize {
        self.size
    }
    pub fn offset(&self, off: usize) -> Result<NonNull<u8>, AllocError> {
        // TODO: align
        if self.size == 0 {
            return Err(AllocError::HeapNotAllocated);
        }
        if off > self.size {
            return Err(AllocError::OutOfBounds);
        }
        unsafe { Ok(NonNull::new_unchecked(self.addr.offset(off as isize))) }
    }
    pub fn offset_from(&self, addr: NonNull<u8>) -> Result<usize, AllocError> {
        let diff;
        unsafe { diff = addr.as_ptr().offset_from(self.addr) }
        if diff < 0 || diff as usize > self.size {
            return Err(AllocError::OutOfBounds);
        }
        Ok(diff as usize)
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        // println!("Dropping heap");
        if !self.addr.is_null() {
            unsafe {
                self.deallocate(NonNull::new_unchecked(self.addr)).unwrap();
            }
        }
    }
}

unsafe impl Allocator for Heap {
    fn allocate(&mut self, size: usize, align: usize) -> Result<NonNull<u8>, AllocError> {
        if !self.addr.is_null() {
            return Err(AllocError::HeapAlreadyAllocated);
        }
        self.size = align_up(size, align);
        let addr;
        unsafe {
            addr = mmap(
                std::ptr::null_mut(),
                self.size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
                -1,
                0,
            );
            if addr == libc::MAP_FAILED {
                self.size = 0;
                self.addr = std::ptr::null_mut();
                Err(AllocError::MapFailed)
            } else {
                // TODO: Check alignment
                self.addr = std::mem::transmute::<*mut libc::c_void, *mut u8>(addr);
                Ok(NonNull::new_unchecked(self.addr))
            }
        }
    }
    unsafe fn deallocate(&mut self, ptr: NonNull<u8>) -> Result<(), AllocError> {
        if self.size == 0 {
            return Err(AllocError::HeapNotAllocated);
        }
        if self.addr != ptr.as_ptr() {
            return Err(AllocError::InvalidAddress);
        }
        munmap(
            std::mem::transmute::<*mut u8, *mut libc::c_void>(self.addr),
            self.size,
        );
        self.addr = std::ptr::null_mut();
        self.size = 0;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let heap = Heap::new();
        assert_eq!(heap.size(), 0);
        assert_eq!(heap.addr, std::ptr::null_mut());
    }

    #[test]
    fn test_allocate() {
        let mut heap = Heap::new();
        assert!(heap.allocate(128, 16).is_ok());
        assert_eq!(heap.size(), 128);
    }

    #[test]
    fn test_offset() {
        let mut heap = Heap::new();
        assert_eq!(heap.offset(1), Err(AllocError::HeapNotAllocated));
        assert!(heap.allocate(128, 16).is_ok());
        assert_eq!(
            heap.offset(1).unwrap(),
            NonNull::new(unsafe { heap.addr.offset(1) }).unwrap()
        );
        assert_eq!(heap.offset(1000), Err(AllocError::OutOfBounds));
    }

    #[test]
    fn test_offset_from() {
        let mut heap = Heap::new();
        assert!(heap.allocate(128, 16).is_ok());
        unsafe {
            assert_eq!(
                heap.offset_from(NonNull::new(heap.addr).expect("NonNull::new failed")),
                Ok(0)
            );
            assert_eq!(
                heap.offset_from(NonNull::new(heap.addr.offset(10)).expect("NonNull::new failed")),
                Ok(10)
            );
            assert_eq!(
                heap.offset_from(NonNull::new(heap.addr.offset(-1)).expect("NonNull::new failed")),
                Err(AllocError::OutOfBounds)
            );
            assert_eq!(
                heap.offset_from(
                    NonNull::new(heap.addr.offset(1000)).expect("NonNull::new failed")
                ),
                Err(AllocError::OutOfBounds)
            );
        }
    }

    #[test]
    fn test_alignment() {
        let mut heap = Heap::new();
        assert!(heap.allocate(128, 512).is_ok());
        assert_eq!(heap.size(), 512);
    }

    #[test]
    fn test_deallocate() {
        let mut heap = Heap::new();
        let mut x = 1;
        unsafe {
            assert_eq!(
                heap.deallocate(NonNull::new(&mut x).expect("NonNull::new failed")),
                Err(AllocError::HeapNotAllocated)
            );
        }
        assert!(heap.allocate(128, 16).is_ok());
        unsafe {
            assert_eq!(
                heap.deallocate(heap.offset(1).expect("Offset failed")),
                Err(AllocError::InvalidAddress)
            );
            assert!(heap
                .deallocate(NonNull::new(heap.addr).expect("NonNull::new failed"))
                .is_ok());
        }
        assert_eq!(heap.size(), 0);
        assert_eq!(heap.addr, std::ptr::null_mut());
        unsafe {
            assert_eq!(
                heap.deallocate(NonNull::new(&mut x).expect("NonNull::new failed")),
                Err(AllocError::HeapNotAllocated)
            );
        }
    }
}
