use std::mem::MaybeUninit;

/// Brings [unlikely](core::intrinsics::unlikely) to stable rust.
#[inline(always)]
pub const fn unlikely(b: bool) -> bool {
    #[allow(clippy::needless_bool)]
    if (1i32).checked_div(if b { 0 } else { 1 }).is_none() {
        true
    } else {
        false
    }
}

pub struct ArrayVec<T, const N: usize> {
    inner: [MaybeUninit<T>; N],
    len: u8,
}

impl<T, const N: usize> Default for ArrayVec<T, N> {
    #[inline(always)]
    fn default() -> Self {
        Self {
            // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
            inner: unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() },
            len: 0,
        }
    }
}

impl<T, const N: usize> ArrayVec<T, N> {
    const _ASSERT_LEN: () = assert!(N <= u8::MAX as usize);

    /// Initialized next item
    ///
    /// # Safety
    ///
    /// - at most `N-1` items were initialized
    #[inline(always)]
    pub unsafe fn push(&mut self, item: T) {
        debug_assert!((self.len as usize) < N);

        *self.inner.get_unchecked_mut(self.len as usize) = MaybeUninit::new(item);
        self.len += 1;
    }

    /// Returns inner array without dropping its elements
    #[inline(always)]
    pub unsafe fn into_inner(self) -> [MaybeUninit<T>; N] {
        let this = std::mem::ManuallyDrop::new(self);
        std::ptr::read(&this.inner)
    }
}

impl<R, const N: usize> AsRef<[R]> for ArrayVec<R, N> {
    fn as_ref(&self) -> &[R] {
        // SAFETY: {len} elements were initialized
        unsafe { std::slice::from_raw_parts(self.inner.as_ptr() as *const R, self.len as usize) }
    }
}

impl<T, const N: usize> Drop for ArrayVec<T, N> {
    fn drop(&mut self) {
        debug_assert!(self.len as usize <= N);

        let references_ptr = self.inner.as_mut_ptr() as *mut T;
        for i in 0..self.len {
            // SAFETY: len items were initialized
            unsafe { std::ptr::drop_in_place(references_ptr.add(i as usize)) };
        }
    }
}
