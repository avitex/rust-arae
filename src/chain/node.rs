use core::ptr::NonNull;
use core::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};
use alloc::boxed::Box;

pub(crate) struct Node<C, T> {
    /// The cursed data.
    pub data: C,
    /// The previous node.
    pub prev: NodePtr<C, T>,
    /// The next node.
    pub next: NodePtr<C, T>,
    /// The number of references to this node.
    /// This is used as a reference count
    /// for dropping the data once it
    /// reaches zero.
    ///
    /// When a node pointer is dropped,
    /// it decreases this count for us.
    refs: AtomicUsize,
}

impl<C, T> Node<C, T> {
    pub fn new(data: C, refs: usize) -> Self {
        Self {
            data,
            prev: NodePtr::new_null(),
            next: NodePtr::new_null(),
            refs: AtomicUsize::new(refs),
        }
    }

    pub fn new_for_insertion(data: C) -> NonNull<Self> {
        Self::new(data, 2).into_boxed_ptr()
    }

    pub fn new_self_referential(data: C) -> NonNull<Self> {
        let this = Self::new(data, 2);
        let this_ptr = this.into_boxed_ptr();
        let this_mut = unsafe { &mut *this_ptr.as_ptr() };
        //
        this_mut.prev.excusive_set(this_ptr.as_ptr());
        this_mut.next.excusive_set(this_ptr.as_ptr());
        //
        this_ptr
    }

    pub fn as_ptr(&self) -> *mut Self {
        (self as *const Self) as _
    }

    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }

    /// Decreases the ref count by one.
    /// Returns `true` if was the last ref, `false` if there are still links to this node.
    fn rem_ref(&self) -> bool {
        self.refs.fetch_sub(1, Ordering::Relaxed) == 0
    }

    /// Increases the ref count by a given amount.
    fn add_refs(&self, refs: u8) {
        if self.refs.fetch_add(refs as usize, Ordering::Relaxed) > isize::max_value() as usize {
            panic!("ref count to node greater than isize::MAX!");
        }
    }

    unsafe fn as_ptr_non_null(&self) -> NonNull<Self> {
        NonNull::new_unchecked(self.as_ptr() as _)
    }

    pub fn into_boxed_ptr(self) -> NonNull<Self> {
        // TODO: Use Box::into_raw_non_null when stable.
        let ptr = Box::into_raw(Box::new(self));
        unsafe { NonNull::new_unchecked(ptr) }
    }

    pub fn init_boundary_tail(&mut self, prev: NonNull<Node<C, T>>) {
        self.prev.excusive_set(prev.as_ptr());
        self.next.excusive_set(0 as _);
    }

    pub fn init_boundary_head(&mut self, next: NonNull<Node<C, T>>) {
        self.prev.excusive_set(0 as _);
        self.next.excusive_set(next.as_ptr());
    }
}

///////////////////////////////////////////////////////////////////////////////

pub(crate) struct NodePtr<C, T> {
    ptr: AtomicPtr<Node<C, T>>,
}

impl<C, T> NodePtr<C, T> {
    pub fn new(ptr: NonNull<Node<C, T>>) -> Self {
        Self {
            ptr: AtomicPtr::new(ptr.as_ptr()),
        }
    }

    pub fn new_null() -> Self {
        Self {
            ptr: AtomicPtr::new(0 as _),
        }
    }

    pub fn load(&self, order: Ordering) -> Option<&Node<C, T>> {
        unsafe { self.load_ptr(order).as_ref() }
    }

    fn load_ptr(&self, order: Ordering) -> *mut Node<C, T> {
        self.ptr.load(order)
    }

    fn store(&self, ptr: *mut Node<C, T>, order: Ordering) {
        self.ptr.store(ptr, order);
    }

    pub fn excusive_set(&mut self, ptr: *mut Node<C, T>) {
        *self.ptr.get_mut() = ptr;
    }

    // pub fn load_non_null(&self) -> NonNull<Node<C, T>> {
    //     match NonNull::new(self.load()) {
    //         Some(ptr) => ptr,
    //         None => panic!("attempted to node ptr not initialized!"),
    //     }
    // }

    // unsafe fn load_non_null_unchecked(&self) -> NonNull<Node<C, T>> {
    //     let ptr = self.load();
    //     debug_assert_ne!(ptr, 0);
    //     unsafe { NonNull::new_unchecked(ptr) }
    // }

    // fn take(&self) -> Option<NonNull<Node<C, T>>> {
    //     NonNull::new(self.ptr.swap(0 as _, Ordering::SeqCst))
    // }
}
