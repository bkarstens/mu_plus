//! Rust Boot Services Allocator
//!
//! Implements a global allocator based on UEFI AllocatePool().
//! Memory is allocated from the EFI_BOOT_SERVICES_DATA pool.
//!
//! ## Examples and Usage
//!
//! ```no_run
//! use r_efi::efi::Status;
//! pub extern "efiapi" fn efi_main(
//!   _image_handle: *const core::ffi::c_void,
//!   system_table: *const r_efi::system::SystemTable,
//! ) -> u64 {
//!   rust_boot_services_allocator_dxe::GLOBAL_ALLOCATOR.init(unsafe { (*system_table).boot_services});
//!
//!   let mut foo = vec!["asdf", "xyzpdq", "abcdefg", "theoden"];
//!   foo.sort();
//!
//!   let bar = Box::new(foo);
//!
//!   Status::SUCCESS.as_usize() as u64
//! }
//! ```
//!
//! ## License
//!
//! Copyright (C) Microsoft Corporation. All rights reserved.
//!
//! SPDX-License-Identifier: BSD-2-Clause-Patent
//!
#![no_std]
#![feature(allocator_api)]

use core::alloc::{GlobalAlloc, Layout};

use boot_services::allocation::MemoryType;
use r_efi::efi;

/// Static GLOBAL_ALLOCATOR instance that is marked with the `#[global_allocator]` attribute.
#[cfg_attr(not(test), global_allocator)]
pub static mut GLOBAL_ALLOCATOR: BootServicesAllocator<boot_services::StandardBootServices> = BootServicesAllocator::new();

const ALLOC_TRACKER_SIG: u32 = 0x706F6F6C; //arbitrary sig

// Used to track allocations that need larger alignment than the UEFI Pool alignment (8 bytes).
struct AllocationTracker {
    signature: u32,
    orig_ptr: *mut u8,
}

/// Boot services allocator implementation. Must be initialized with a boot_services pointer before use,
/// see [`BootServicesAllocator::init()`].
pub struct BootServicesAllocator<BS: boot_services::BootServices> {
    boot_services: Option<BS>,
}

impl<BS> BootServicesAllocator<BS>
where
    BS: boot_services::BootServices,
{
    // Create a new instance. const fn to allow static initialization.
    const fn new() -> Self {
        BootServicesAllocator { boot_services: None }
    }

    // Implement allocation using EFI boot services AllocatePool() call.
    fn boot_services_alloc(&self, layout: Layout, boot_services: &BS) -> *mut u8 {
        match layout.align() {
            0..=8 => match boot_services.allocate_pool(MemoryType::BOOT_SERVICES_DATA, layout.size()) {
                Ok(ptr) => ptr,
                Err(_status) => core::ptr::null_mut(),
            },
            _ => {
                // Allocate extra space to align the allocation as requested and include a tracking structure to allow
                // recovery of the original pointer for de-allocation. Tracking structure follows the allocation.
                let (expanded_layout, tracking_offset) = match layout.extend(Layout::new::<AllocationTracker>()) {
                    Ok((layout, offset)) => (layout, offset),
                    Err(_) => return core::ptr::null_mut(),
                };
                let expanded_size = expanded_layout.size() + expanded_layout.align();

                let orig_ptr = match boot_services.allocate_pool(MemoryType::BOOT_SERVICES_DATA, expanded_size) {
                    Ok(ptr) => ptr,
                    Err(_status) => return core::ptr::null_mut(),
                };

                // Align the pointer up to the required alignment.
                let final_ptr = unsafe { orig_ptr.add(orig_ptr.align_offset(expanded_layout.align())) };

                // Get a reference to the allocation tracking structure after the allocation and populate it.
                let tracker = unsafe {
                    final_ptr
                        .add(tracking_offset)
                        .cast::<AllocationTracker>()
                        .as_mut()
                        .expect("tracking pointer is invalid")
                };

                tracker.signature = ALLOC_TRACKER_SIG;
                tracker.orig_ptr = orig_ptr;

                final_ptr
            }
        }
    }

    // Implement dealloc (free) using EFI boot services FreePool() call.
    fn boot_services_dealloc(&self, boot_services: &BS, ptr: *mut u8, layout: Layout) {
        match layout.align() {
            0..=8 => {
                // Pointer was allocated directly, so free it directly.
                let _ = boot_services.free_pool(ptr);
            }
            _ => {
                // Pointer was potentially adjusted for alignment. Recover tracking structure to retrieve the original
                // Pointer to free.
                let (_layout, tracking_offset) = match layout.extend(Layout::new::<AllocationTracker>()) {
                    Ok((layout, offset)) => (layout, offset),
                    Err(_) => return,
                };
                let tracker = unsafe {
                    ptr.add(tracking_offset).cast::<AllocationTracker>().as_mut().expect("tracking pointer is invalid")
                };

                debug_assert_eq!(tracker.signature, ALLOC_TRACKER_SIG);
                let _ = boot_services.free_pool(tracker.orig_ptr);
            }
        }
    }
}

impl<'a> BootServicesAllocator<boot_services::StandardBootServices<'a>> {
    /// Initializes the allocator instance with a pointer to the UEFI Boot Services table.
    pub fn init(&mut self, efi_boot_services: *mut efi::BootServices) {
        let standard_boot_services = unsafe { boot_services::StandardBootServices::new(&*efi_boot_services) };
        self.boot_services = Some(standard_boot_services)
    }
}

unsafe impl<BS> GlobalAlloc for BootServicesAllocator<BS>
where
    BS: boot_services::BootServices,
{
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        match &self.boot_services {
            Some(bs) => self.boot_services_alloc(layout, &bs),
            None => core::ptr::null_mut(),
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        match &self.boot_services {
            Some(bs) => self.boot_services_dealloc(&bs, ptr, layout),
            None => (),
        }
    }
}

unsafe impl<BS> Sync for BootServicesAllocator<BS> where BS: boot_services::BootServices {}
unsafe impl<BS> Send for BootServicesAllocator<BS> where BS: boot_services::BootServices {}

#[cfg(test)]
mod tests {
    extern crate std;

    use core::alloc::{GlobalAlloc, Layout};
    use std::alloc::System;
    use std::collections::BTreeMap;

    use boot_services::{allocation::MemoryType, MockBootServices};
    use r_efi::efi;

    use crate::{AllocationTracker, BootServicesAllocator, ALLOC_TRACKER_SIG};

    static ALLOCATION_TRACKER: spin::Mutex<BTreeMap<usize, Layout>> = spin::Mutex::new(BTreeMap::new());
    fn mock_allocate_pool(pool_type: MemoryType, size: usize) -> Result<*mut u8, efi::Status> {
        assert_eq!(pool_type, MemoryType::BOOT_SERVICES_DATA);

        let layout = Layout::from_size_align(size, 8).unwrap();
        unsafe {
            let ptr = System.alloc(layout);
            let existing_key = ALLOCATION_TRACKER.lock().insert(ptr as usize, layout);
            assert!(existing_key.is_none());
            Ok(ptr)
        }
    }

    fn mock_free_pool(buffer: *mut u8) -> Result<(), efi::Status> {
        let layout = ALLOCATION_TRACKER.lock().remove(&(buffer as usize)).expect("freeing an un-allocated pointer");
        unsafe {
            System.dealloc(buffer, layout);
        }
        Ok(())
    }

    fn mock_boot_services() -> MockBootServices {
        let mut mock_boot_services = MockBootServices::new();
        mock_boot_services.expect_allocate_pool().returning(mock_allocate_pool);
        mock_boot_services.expect_free_pool().returning(mock_free_pool);
        mock_boot_services
    }

    #[test]
    fn basic_alloc_and_dealloc() {
        let allocator: BootServicesAllocator<MockBootServices> =
            BootServicesAllocator { boot_services: Some(mock_boot_services()) };

        let layout = Layout::from_size_align(0x40, 0x8).unwrap();
        let ptr = unsafe { allocator.alloc_zeroed(layout) };
        assert!(!ptr.is_null());
        assert!(ALLOCATION_TRACKER.lock().contains_key(&(ptr as usize)));

        unsafe { allocator.dealloc(ptr, layout) };
        assert!(!ALLOCATION_TRACKER.lock().contains_key(&(ptr as usize)));
    }

    #[test]
    fn big_alignment_should_allocate_tracking_structure() {
        let allocator: BootServicesAllocator<MockBootServices> =
            BootServicesAllocator { boot_services: Some(mock_boot_services()) };

        let layout = Layout::from_size_align(0x40, 0x1000).unwrap();
        let ptr = unsafe { allocator.alloc_zeroed(layout) };
        assert!(!ptr.is_null());
        assert_eq!(ptr.align_offset(0x1000), 0);

        // reconstruct a reference to the tracker structure at the end of the allocation.
        let (_, tracking_offset) = layout.extend(Layout::new::<AllocationTracker>()).unwrap();
        let tracker = unsafe {
            ptr.add(tracking_offset).cast::<AllocationTracker>().as_mut().expect("tracking pointer is invalid")
        };
        assert_eq!(tracker.signature, ALLOC_TRACKER_SIG);

        let orig_ptr_addr = tracker.orig_ptr as usize;

        assert!(ALLOCATION_TRACKER.lock().contains_key(&(orig_ptr_addr)));

        unsafe { allocator.dealloc(ptr, layout) };

        assert!(!ALLOCATION_TRACKER.lock().contains_key(&(orig_ptr_addr)));
    }
}
