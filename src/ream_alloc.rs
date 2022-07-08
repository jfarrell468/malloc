use crate::allocator::{align_up, AllocError, Allocator};
use crate::arena::Arena;
use std::iter::{IntoIterator, Iterator};
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

#[derive(Debug)]
struct PdRef {
    idx: u32,
    list: NonNull<PdList>,
}

impl PdRef {
    fn pd(&self) -> Result<&mut Pd, AllocError> {
        unsafe { self.list.as_ref().pd(self.idx) }
    }
    fn unlink(&mut self) -> Result<&mut Pd, AllocError> {
        let pd_next = self.pd()?.next;
        let pd_prev = self.pd()?.prev;
        if let Some(next_idx) = pd_next {
            let next;
            unsafe {
                next = self.list.as_mut().pd(next_idx)?;
            }
            next.prev = pd_prev;
        }

        if unsafe { self.list.as_ref().root } == Some(self.idx) {
            unsafe {
                self.list.as_mut().root = pd_next;
            }
        } else if let Some(prev_idx) = pd_prev {
            let prev;
            unsafe {
                prev = self.list.as_mut().pd(prev_idx)?;
            }
            prev.next = pd_next;
        }
        let pd = self.pd()?;
        pd.prev = None;
        pd.next = None;
        Ok(pd)
    }
}

#[derive(Debug)]
struct PdList {
    root: Option<u32>,
    addr: NonNull<Pd>,
    num_pds: u32,
}

impl PdList {
    unsafe fn pd(&self, idx: u32) -> Result<&mut Pd, AllocError> {
        // println!("Pdlist.pd(idx = {})", idx);
        if idx >= self.num_pds {
            // println!("Out of bounds");
            return Err(AllocError::OutOfBounds);
        }
        Ok(&mut *self.addr.as_ptr().offset(idx as isize))
    }
    fn push(&mut self, idx: u32) -> Result<&mut Pd, AllocError> {
        if let Some(old_idx) = self.root {
            let old_head;
            unsafe {
                old_head = self.pd(old_idx)?;
            }
            old_head.prev = Some(idx);
        }
        let old_root = self.root;
        self.root = Some(idx);
        let pd;
        unsafe {
            pd = self.pd(idx)?;
        }
        pd.prev = None;
        pd.next = old_root;
        Ok(pd)
    }
}

impl<'a> IntoIterator for &'a mut PdList {
    type Item = PdRef;
    type IntoIter = PdListIter;
    fn into_iter(self) -> Self::IntoIter {
        // println!("PdList.into_iter, self = {:?}", self);
        PdListIter {
            next: self.root,
            list: NonNull::from(self),
        }
    }
}

#[derive(Debug)]
struct PdListIter {
    next: Option<u32>,
    list: NonNull<PdList>,
}

impl Iterator for PdListIter {
    type Item = PdRef;
    fn next(&mut self) -> Option<Self::Item> {
        // println!("PdListIter.next()");
        match self.next {
            Some(idx) => {
                unsafe {
                    self.next = self.list.as_mut().pd(idx).unwrap().next;
                }
                Some(PdRef {
                    idx,
                    list: self.list,
                })
            }
            None => None,
        }
    }
}

pub struct ReamAlloc {
    arena: Arena,
    page_size: usize,
    pd_pages: u32,
    num_pages: u32,
    free_list: PdList,
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
        let arena_addr;
        unsafe {
            arena_addr = std::mem::transmute::<NonNull<u8>, NonNull<Pd>>(arena.offset(0)?);
        }
        Ok(ReamAlloc {
            arena: arena,
            page_size: page_size,
            pd_pages: pd_pages as u32,
            num_pages: 0,
            free_list: PdList {
                root: None,
                addr: arena_addr,
                num_pds: max_pages as u32,
            },
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

        // println!("Searching free list: {:?}", self.free_list);
        for mut iter in &mut self.free_list {
            // println!("Searching free list. iter = {:?}", iter);
            if iter.pd()?.len <= requested_pages {
                // println!("Found a free ream.");
                let pd = iter.unlink()?;
                pd.gc_bits = 1;
                return self
                    .arena
                    .offset((self.pd_pages + iter.idx) as usize * self.page_size);
            }
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
        let pd = self.free_list.push(idx)?;
        pd.gc_bits = 0;
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
    fn test_new() -> Result<(), AllocError> {
        let alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE)?;
        assert_eq!(alloc.page_size, PAGE_SIZE);
        assert_eq!(
            alloc.free_list.num_pds as usize,
            HEAP_SIZE / (PAGE_SIZE + mem::size_of::<Pd>())
        );
        assert_eq!(
            alloc.pd_pages as usize,
            ((alloc.free_list.num_pds as usize) * mem::size_of::<Pd>() + PAGE_SIZE - 1) / PAGE_SIZE
        );
        assert_eq!(alloc.num_pages, 0);
        assert!(alloc.free_list.root.is_none());
        Ok(())
    }

    #[test]
    fn test_allocate() -> Result<(), AllocError> {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE)?;
        assert!(alloc.allocate(8, 8).is_ok());
        assert_eq!(alloc.num_pages, 1);
        let pd = alloc.get_pd(0)?;
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 1);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert!(alloc.free_list.root.is_none());
        Ok(())
    }

    #[test]
    fn test_deallocate() -> Result<(), AllocError> {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE)?;
        let addr = alloc.allocate(8, 8)?;
        let pd;
        unsafe {
            pd = std::mem::transmute::<NonNull<u8>, NonNull<Pd>>(alloc.arena.offset(0)?).as_ref();
        }
        unsafe {
            assert!(alloc.deallocate(addr).is_ok());
        }
        // println!("{:?}", pd);
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 0);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert_eq!(alloc.free_list.root, Some(0));
        Ok(())
    }

    #[test]
    fn test_reallocate() -> Result<(), AllocError> {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE)?;
        let old_addr = alloc.allocate(8, 8)?;
        unsafe {
            assert!(alloc.deallocate(old_addr).is_ok());
        }
        // println!("Free list after deallocate: {:?}", alloc.free_list);
        let addr = alloc.allocate(8, 8)?;
        assert_eq!(addr, old_addr);
        let pd = alloc.get_pd(0)?;
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 1);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert!(alloc.free_list.root.is_none());
        Ok(())
    }

    #[test]
    fn test_multi_allocate() -> Result<(), AllocError> {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE)?;
        assert!(alloc.allocate(8, 8).is_ok());
        assert_eq!(alloc.num_pages, 1);
        let pd = alloc.get_pd(0)?;
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 1);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert!(alloc.free_list.root.is_none());

        assert!(alloc.allocate(8, 8).is_ok());
        assert_eq!(alloc.num_pages, 2);
        let pd = alloc.get_pd(1)?;
        assert_eq!(pd.len, 1);
        assert_eq!(pd.gc_bits, 1);
        assert!(pd.prev.is_none());
        assert!(pd.next.is_none());
        assert!(alloc.free_list.root.is_none());
        Ok(())
    }

    #[test]
    fn test_multi_deallocate() -> Result<(), AllocError> {
        let mut alloc = ReamAlloc::new(HEAP_SIZE, PAGE_SIZE)?;
        let addr0 = alloc.allocate(8, 8)?;
        let addr1 = alloc.allocate(8, 8)?;
        let pd0;
        let pd1;
        unsafe {
            pd0 = std::mem::transmute::<NonNull<u8>, NonNull<Pd>>(alloc.arena.offset(0)?).as_ref();
            pd1 = std::mem::transmute::<NonNull<u8>, NonNull<Pd>>(
                alloc.arena.offset(mem::size_of::<Pd>())?,
            )
            .as_ref();
        }
        unsafe {
            assert!(alloc.deallocate(addr0).is_ok());
        }
        assert_eq!(alloc.free_list.root, Some(0));
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
        assert_eq!(alloc.free_list.root, Some(1));
        Ok(())
    }
}
