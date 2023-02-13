//! General stuff.

use std::mem::MaybeUninit;

/// Brings [unlikely](core::intrinsics::unlikely) to stable rust.
#[inline(always)]
pub const fn unlikely(b: bool) -> bool {
    #[allow(clippy::needless_bool, clippy::bool_to_int_with_if)]
    if (1i32).checked_div(if b { 0 } else { 1 }).is_none() {
        true
    } else {
        false
    }
}

/// Helper struct to pretty-print hash.
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

/// Small on-stack vector of max length N.
pub struct ArrayVec<T, const N: usize> {
    inner: [MaybeUninit<T>; N],
    len: u8,
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

impl<R, const N: usize> AsRef<[R]> for ArrayVec<R, N> {
    #[inline]
    fn as_ref(&self) -> &[R] {
        // SAFETY: {len} elements were initialized
        unsafe { std::slice::from_raw_parts(self.inner.as_ptr() as *const R, self.len as usize) }
    }
}

impl<T: Clone, const N: usize> Clone for ArrayVec<T, N> {
    fn clone(&self) -> Self {
        let mut res = Self::default();
        for item in self.as_ref() {
            // SAFETY: {len} elements were initialized
            unsafe { res.push(item.clone()) };
        }
        res
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

#[derive(Clone, Copy)]
pub(crate) enum IterStatus {
    /// Iterator is still valid.
    Valid,
    /// Iterator started with a pruned branch cell.
    Pruned,
    /// [`RawDict`] has invalid structure.
    Broken,
}

impl IterStatus {
    #[inline]
    pub(crate) const fn is_valid(self) -> bool {
        matches!(self, Self::Valid)
    }

    #[inline]
    pub(crate) const fn is_pruned(self) -> bool {
        matches!(self, Self::Pruned)
    }
}

pub(crate) fn debug_tuple_field1_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    value1: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_tuple(f, name);
    builder.field(value1);
    builder.finish()
}

pub(crate) fn debug_tuple_field2_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    value1: &dyn std::fmt::Debug,
    value2: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_tuple(f, name);
    builder.field(value1);
    builder.field(value2);
    builder.finish()
}

pub(crate) fn debug_struct_field1_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    name1: &str,
    value1: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_struct(f, name);
    builder.field(name1, value1);
    builder.finish()
}

pub(crate) fn debug_struct_field2_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    name1: &str,
    value1: &dyn std::fmt::Debug,
    name2: &str,
    value2: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_struct(f, name);
    builder.field(name1, value1);
    builder.field(name2, value2);
    builder.finish()
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn debug_struct_field3_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    name1: &str,
    value1: &dyn std::fmt::Debug,
    name2: &str,
    value2: &dyn std::fmt::Debug,
    name3: &str,
    value3: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_struct(f, name);
    builder.field(name1, value1);
    builder.field(name2, value2);
    builder.field(name3, value3);
    builder.finish()
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn debug_struct_field4_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    name1: &str,
    value1: &dyn std::fmt::Debug,
    name2: &str,
    value2: &dyn std::fmt::Debug,
    name3: &str,
    value3: &dyn std::fmt::Debug,
    name4: &str,
    value4: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_struct(f, name);
    builder.field(name1, value1);
    builder.field(name2, value2);
    builder.field(name3, value3);
    builder.field(name4, value4);
    builder.finish()
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn debug_struct_field5_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    name1: &str,
    value1: &dyn std::fmt::Debug,
    name2: &str,
    value2: &dyn std::fmt::Debug,
    name3: &str,
    value3: &dyn std::fmt::Debug,
    name4: &str,
    value4: &dyn std::fmt::Debug,
    name5: &str,
    value5: &dyn std::fmt::Debug,
) -> std::fmt::Result {
    let mut builder = std::fmt::Formatter::debug_struct(f, name);
    builder.field(name1, value1);
    builder.field(name2, value2);
    builder.field(name3, value3);
    builder.field(name4, value4);
    builder.field(name5, value5);
    builder.finish()
}

pub(crate) fn debug_struct_fields_finish(
    f: &mut std::fmt::Formatter<'_>,
    name: &str,
    names: &[&str],
    values: &[&dyn std::fmt::Debug],
) -> std::fmt::Result {
    assert_eq!(names.len(), values.len());
    let mut builder = std::fmt::Formatter::debug_struct(f, name);
    for (name, value) in std::iter::zip(names, values) {
        builder.field(name, value);
    }
    builder.finish()
}
