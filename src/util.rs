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

/// Helper struct to prerry-print hash.
#[derive(Clone, Copy)]
pub struct DisplayHash<'a>(pub &'a [u8; 32]);

impl std::fmt::Display for DisplayHash<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut output = [0u8; 64];
        hex::encode_to_slice(self.0, &mut output).ok();

        // SAFETY: output is guaranteed to contain only [0-9a-f]
        let output = unsafe { std::str::from_utf8_unchecked(&output) };
        f.write_str(output)
    }
}

impl std::fmt::Debug for DisplayHash<'_> {
    #[inline(always)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

/// Small on-stack vector of max lenth N.
pub struct ArrayVec<T, const N: usize> {
    inner: [MaybeUninit<T>; N],
    len: u8,
}

impl<T, const N: usize> Default for ArrayVec<T, N> {
    #[inline]
    fn default() -> Self {
        Self {
            // SAFETY: An uninitialized `[MaybeUninit<_>; LEN]` is valid.
            inner: unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() },
            len: 0,
        }
    }
}

impl<T, const N: usize> ArrayVec<T, N> {
    /// Ensure that provided length is small enough.
    const _ASSERT_LEN: () = assert!(N <= u8::MAX as usize);

    /// Returns the number of elements in the vector, also referred to as its ‘length’.
    #[inline]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns true if the vector contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Safety
    ///
    /// The following must be true:
    /// - The length of this vector is less than `N`.
    #[inline]
    pub unsafe fn push(&mut self, item: T) {
        debug_assert!((self.len as usize) < N);

        *self.inner.get_unchecked_mut(self.len as usize) = MaybeUninit::new(item);
        self.len += 1;
    }

    /// Returns the inner data without dropping its elements.
    ///
    /// # Safety
    ///
    /// The caller is responsible for calling the destructor for
    /// `len` initialized items in the returned array.
    #[inline]
    pub unsafe fn into_inner(self) -> [MaybeUninit<T>; N] {
        let this = std::mem::ManuallyDrop::new(self);
        std::ptr::read(&this.inner)
    }
}

impl<R, const N: usize> AsRef<[R]> for ArrayVec<R, N> {
    #[inline]
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
