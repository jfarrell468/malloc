use crate::allocator::{align_up, AllocError, Allocator};
use crate::arena::Arena;
use std::iter::Iterator;
use std::mem;
use std::ptr::NonNull;

#[derive(Debug)]
pub enum SizeClass {
    Ream,
    Page,
    Slab(u16),
}

#[derive(Debug)]
struct Pd {
    gc_bits: u64,
    prev: Option<u32>,
    next: Option<u32>,
    len: u16,
    class: SizeClass,
}

pub struct ReamAlloc {
    arena: Arena,
    page_size: usize,
    max_pages: u32,
    pd_pages: u32,
    num_pages: u32,
    free_list: Option<u32>,
}

impl ReamAlloc {
    pub fn new(size: usize, page_size: usize) -> Result<ReamAlloc, AllocError> {
        let aligned_size = align_up(size, page_size);
        // if aligned_size > 1<<32 {
        //     return Err(AllocError::InsufficientAddressSpace);
        // }
        let max_pages = aligned_size / (page_size + mem::size_of::<Pd>());
        if max_pages > u32::MAX as usize {
            return Err(AllocError::InsufficientAddressSpace);
        }
        let pd_pages = align_up(mem::size_of::<Pd>() * max_pages, page_size) / page_size;
        let mut arena = Arena::new(aligned_size, page_size)?;
        arena.allocate(pd_pages * page_size, page_size)?;
        Ok(ReamAlloc {
            arena: arena,
            page_size: page_size,
            max_pages: max_pages as u32,
            pd_pages: pd_pages as u32,
            num_pages: 0,
            free_list: None,
        })
    }
    fn get_pd(&self, idx: usize) -> Result<&mut Pd, AllocError> {
        if idx >= self.num_pages as usize {
            return Err(AllocError::OutOfBounds);
        }
        unsafe {
            Ok(std::mem::transmute::<NonNull<u8>, NonNull<Pd>>(
                self.arena.offset(idx * mem::size_of::<Pd>())?,
            )
            .as_mut())
        }
    }
    fn get_page_from_addr(&mut self, addr: NonNull<u8>) -> Result<u32, AllocError> {
        Ok((self.arena.offset_from(addr)? / self.page_size) as u32 - self.pd_pages)
    }
}

unsafe impl Allocator for ReamAlloc {
    fn allocate(&mut self, size: usize, align: usize) -> Result<NonNull<u8>, AllocError> {
        let aligned_size = align_up(size, self.page_size);
        let requested_pages = aligned_size / self.page_size;
        if requested_pages > u16::max as usize {
            return Err(AllocError::InsufficientAddressSpace);
        }
        let requested_pages = requested_pages as u16;

        // See if we can satisfy from the free list.
        let mut next_free = self.free_list;
        // println!("Searching free list. next_free = {:?}", next_free);
        while next_free.is_some() {
            let idx = next_free.unwrap();
            let this_pd: &Pd = self.get_pd(idx as usize)?; // Immutable
                                                           // println!("{:?}", this_pd);
            if this_pd.len <= requested_pages {
                // println!("Found a free ream.");
                let mut new_free_list = self.free_list.clone();
                if let Some(next_idx) = this_pd.next {
                    self.get_pd(next_idx as usize)?.prev = this_pd.prev;
                }

                if self.free_list == Some(idx) {
                    new_free_list = this_pd.next;
                } else if let Some(prev_idx) = this_pd.prev {
                    self.get_pd(prev_idx as usize)?.next = this_pd.next;
                }
                let this_pd = self.get_pd(idx as usize)?;
                this_pd.gc_bits = 1;
                this_pd.prev = None;
                this_pd.next = None;
                self.free_list = new_free_list;
                return self
                    .arena
                    .offset((self.pd_pages + idx) as usize * self.page_size);
            }
            next_free = this_pd.next;
            // println!("Searching free list. next_free = {:?}", next_free);
        }
        // println!("Failed to find a free ream.");
        let addr = self.arena.allocate(aligned_size, self.page_size)?;
        let pd = self.num_pages;
        self.num_pages += requested_pages as u32;
        let pd = self.get_pd(pd as usize)?;
        *pd = Pd {
            gc_bits: 1,
            prev: None,
            next: None,
            len: requested_pages,
            class: SizeClass::Ream,
        };
        // TODO: If more than one page, maybe clear those PDs too?
        Ok(addr)
    }

    unsafe fn deallocate(&mut self, ptr: NonNull<u8>) -> Result<(), AllocError> {
        let idx = self.get_page_from_addr(ptr)?;
        let pd = self.get_pd(idx as usize)?;
        pd.gc_bits = 0;
        match &self.free_list {
            None => self.free_list = Some(idx as u32),
            Some(old_head) => {
                self.get_pd(*old_head as usize)?.prev = Some(idx);
                pd.next = Some(*old_head);
                self.free_list = Some(idx);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const HEAP_SIZE: usize = 1 << 30; // 1 GB
    const PAGE_SIZE: usize = 1 << 12; // 4K

    #[test]
    fn test_size_of() {
        assert_eq!(mem::size_of::<Pd>(), 32);
    }

    #[test]
    fn test_new() {
        let alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE).expect("Failed to create ReamAlloc");
        assert_eq!(alloc.page_size, PAGE_SIZE);
        assert_eq!(
            alloc.max_pages as usize,
            HEAP_SIZE / (PAGE_SIZE + mem::size_of::<Pd>())
        );
        assert_eq!(
            alloc.pd_pages as usize,
            ((alloc.max_pages as usize) * mem::size_of::<Pd>() + PAGE_SIZE - 1) / PAGE_SIZE
        );
        assert_eq!(alloc.num_pages, 0);
        assert!(alloc.free_list.is_none());
    }

    #[test]
    fn test_allocate() {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE).expect("Failed to create ReamAlloc");
        assert!(alloc.allocate(8, 8).is_ok());
        assert_eq!(alloc.num_pages, 1);
        let pd = alloc.get_pd(0).expect("Failed to get page descriptor");
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 1);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert!(alloc.free_list.is_none());
    }

    #[test]
    fn test_deallocate() {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE).expect("Failed to create ReamAlloc");
        let addr = alloc.allocate(8, 8).expect("Failed to allocate");
        let pd;
        unsafe {
            pd = std::mem::transmute::<NonNull<u8>, NonNull<Pd>>(
                alloc.arena.offset(0).expect("Failed to get arena offset"),
            )
            .as_ref();
        }
        unsafe {
            assert!(alloc.deallocate(addr).is_ok());
        }
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 0);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert_eq!(alloc.free_list, Some(0));
    }

    #[test]
    fn test_reallocate() {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE).expect("Failed to create ReamAlloc");
        let old_addr = alloc.allocate(8, 8).expect("Failed to allocate");
        unsafe {
            assert!(alloc.deallocate(old_addr).is_ok());
        }
        let addr = alloc.allocate(8, 8).expect("Failed to allocate");
        assert_eq!(addr, old_addr);
        let pd = alloc.get_pd(0).expect("Failed to get page descriptor");
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 1);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert!(alloc.free_list.is_none());
    }

    #[test]
    fn test_multi_allocate() {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE).expect("Failed to create ReamAlloc");
        assert!(alloc.allocate(8, 8).is_ok());
        assert_eq!(alloc.num_pages, 1);
        let pd = alloc.get_pd(0).expect("Failed to get page descriptor");
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 1);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert!(alloc.free_list.is_none());

        assert!(alloc.allocate(8, 8).is_ok());
        assert_eq!(alloc.num_pages, 2);
        let pd = alloc.get_pd(1).expect("Failed to get page descriptor");
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 1);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert!(alloc.free_list.is_none());
    }

    #[test]
    fn test_multi_deallocate() {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE).expect("Failed to create ReamAlloc");
        let addr0 = alloc.allocate(8, 8).expect("Failed to allocate");
        let addr1 = alloc.allocate(8, 8).expect("Failed to allocate");
        let pd0;
        let pd1;
        unsafe {
            pd0 = std::mem::transmute::<NonNull<u8>, NonNull<Pd>>(
                alloc.arena.offset(0).expect("Failed to get arena offset"),
            )
            .as_ref();
            pd1 = std::mem::transmute::<NonNull<u8>, NonNull<Pd>>(
                alloc
                    .arena
                    .offset(mem::size_of::<Pd>())
                    .expect("Failed to get arena offset"),
            )
            .as_ref();
        }
        unsafe {
            assert!(alloc.deallocate(addr0).is_ok());
        }
        assert_eq!(alloc.free_list, Some(0));
        assert_eq!(pd0.len, 1);
        assert_eq!(pd0.gc_bits, 0);
        assert!(pd0.prev.is_none());
        assert!(pd0.next.is_none());
        assert_eq!(pd1.len, 1);
        assert_eq!(pd1.gc_bits, 1);
        assert!(pd1.prev.is_none());
        assert!(pd1.next.is_none());

        unsafe {
            assert!(alloc.deallocate(addr1).is_ok());
        }
        assert_eq!(pd0.len, 1);
        assert_eq!(pd0.gc_bits, 0);
        assert_eq!(pd0.prev, Some(1));
        assert!(pd0.next.is_none());
        assert_eq!(pd1.len, 1);
        assert_eq!(pd1.gc_bits, 0);
        assert!(pd1.prev.is_none());
        assert_eq!(pd1.next, Some(0));
        assert_eq!(alloc.free_list, Some(1));
    }
}
