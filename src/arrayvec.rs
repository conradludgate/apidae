use std::mem;
use std::mem::MaybeUninit;
use std::ptr;
use std::slice;

/// A vector with a fixed capacity.
///
/// The `ArrayVec` is a vector backed by a fixed size array. It's your responsibility
/// to keep track of the number of initialized elements. The `ArrayVec<T, CAP>` is parameterized
/// by `T` for the element type and `CAP` for the maximum capacity.
///
/// `CAP` is of type `usize` but is range limited to `u32::MAX`; attempting to create larger
/// arrayvecs with larger capacity will panic.
///
/// The vector is a contiguous value (storing the elements inline) that you can store directly on
/// the stack if needed.
///
/// It offers a simple API but also dereferences to a slice, so that the full slice API is
/// available. The ArrayVec can be converted into a by value iterator.
#[repr(C)]
pub struct DetachedArrayVec<T, const CAP: usize> {
    #[cfg(debug_assertions)]
    len: usize,

    // the `len` first elements of the array are initialized
    xs: [MaybeUninit<T>; CAP],
}

macro_rules! panic_oob {
    ($method_name:expr, $index:expr, $len:expr) => {
        panic!(
            concat!(
                "ArrayVec::",
                $method_name,
                ": index {} is out of bounds in vector of length {}"
            ),
            $index, $len
        )
    };
}

impl<T, const CAP: usize> DetachedArrayVec<T, CAP> {
    /// Capacity
    const CAPACITY: usize = CAP;

    /// Create a new empty `ArrayVec`.
    ///
    /// The maximum capacity is given by the generic parameter `CAP`.
    #[inline]
    #[track_caller]
    pub const fn new() -> DetachedArrayVec<T, CAP> {
        // assert_capacity_limit!(CAP);
        unsafe {
            DetachedArrayVec {
                #[cfg(debug_assertions)]
                len: 0,
                xs: MaybeUninit::uninit().assume_init(),
            }
        }
    }

    /// Get pointer to where element at `index` would be
    unsafe fn get_unchecked_ptr(&mut self, index: usize) -> *mut T {
        debug_assert!(index <= self.len);
        unsafe { self.as_mut_ptr().add(index) }
    }

    /// Insert `element` at position `index`.
    ///
    /// Shift up all elements after `index`.
    ///
    /// It is an error if the index is greater than the length or if the
    /// arrayvec is full.
    #[track_caller]
    pub unsafe fn insert(&mut self, len: usize, index: usize, element: T) {
        if cfg!(debug_assertions) {
            if index > len {
                panic_oob!("try_insert", index, len)
            }
            if len == CAP {
                panic_oob!("try_insert", len, CAP)
            }
        }

        #[cfg(debug_assertions)]
        {
            assert_eq!(len, self.len);
            self.len += 1;
        }

        // follows is just like Vec<T>
        unsafe {
            // infallible
            // The spot to put the new value
            {
                let p: *mut _ = self.get_unchecked_ptr(index);
                // Shift everything over to make space. (Duplicating the
                // `index`th element into two consecutive places.)
                ptr::copy(p, p.offset(1), len - index);
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(p, element);
            }
        }
    }

    /// Remove the element at `index` and shift down the following elements.
    ///
    /// # Safety
    /// * len <= CAP.
    /// * len elements must be init.
    /// * index < len
    pub unsafe fn remove(&mut self, len: usize, index: usize) -> T {
        debug_assert!(index < len);
        debug_assert!(len <= CAP);

        #[cfg(debug_assertions)]
        {
            assert_eq!(len, self.len);
            self.len -= 1;
        }

        let this = self.as_mut_ptr();

        // SAFETY: index is in bounds of the array
        let elem = unsafe { ptr::read(this.add(index)) };

        let to_shift = len - index - 1;

        // SAFETY: overlapping copy of the (index+1)..len init elements to
        // the range index..(len-1)
        unsafe {
            ptr::copy(this.add(index + 1), this.add(index), to_shift);
        }

        elem
    }

    // /// Create a draining iterator that removes the specified range in the vector
    // /// and yields the removed items from start to end. The element range is
    // /// removed even if the iterator is not consumed until the end.
    // ///
    // /// Note: It is unspecified how many elements are removed from the vector,
    // /// if the `Drain` value is leaked.
    // pub unsafe fn drain<R>(&mut self, len: usize, range: R) -> Drain<T, CAP>
    // where
    //     R: RangeBounds<usize>,
    // {
    //     // Memory safety
    //     //
    //     // When the Drain is first created, it shortens the length of
    //     // the source vector to make sure no uninitialized or moved-from elements
    //     // are accessible at all if the Drain's destructor never gets to run.
    //     //
    //     // Drain will ptr::read out the values to remove.
    //     // When finished, remaining tail of the vec is copied back to cover
    //     // the hole, and the vector length is restored to the new length.
    //     //
    //     let start = match range.start_bound() {
    //         Bound::Unbounded => 0,
    //         Bound::Included(&i) => i,
    //         Bound::Excluded(&i) => i.saturating_add(1),
    //     };
    //     let end = match range.end_bound() {
    //         Bound::Excluded(&j) => j,
    //         Bound::Included(&j) => j.saturating_add(1),
    //         Bound::Unbounded => len,
    //     };
    //     self.drain_range(len, start, end)
    // }

    // unsafe fn drain_range(&mut self, len: usize, start: usize, end: usize) -> Drain<T, CAP> {
    //     if cfg!(debug_assertions) {
    //         if start > end {
    //             panic_oob!("drain", start, end)
    //         }
    //         if end > len {
    //             panic_oob!("drain", end, len)
    //         }
    //         if len > CAP {
    //             panic_oob!("drain", len, CAP)
    //         }
    //     }

    //     let range_slice: *const _ =
    //         std::ptr::slice_from_raw_parts(unsafe { self.as_ptr().add(start) }, end - start);

    //     unsafe {
    //         Drain {
    //             len: start,
    //             tail_start: end,
    //             tail_len: len - end,
    //             iter: (*range_slice).iter(),
    //             vec: self as *mut _,
    //         }
    //     }
    // }

    pub unsafe fn split_off(&mut self, len: usize, at: usize) -> Self {
        let other_len = len - at;
        let mut other = Self::new();

        debug_assert_eq!(self.len, len);
        #[cfg(debug_assertions)]
        {
            self.len = at;
            other.len = other_len;
        }

        unsafe {
            ptr::copy_nonoverlapping(self.as_ptr().add(at), other.as_mut_ptr(), other_len);
        }
        other
    }

    /// Returns the ArrayVec, replacing the original with a new empty ArrayVec.
    pub fn take(&mut self) -> Self {
        mem::replace(self, Self::new())
    }

    /// Return a slice containing all elements of the vector.
    pub unsafe fn as_slice(&self, len: usize) -> &[T] {
        debug_assert_eq!(self.len, len);
        debug_assert!(len <= Self::CAPACITY);
        unsafe { slice::from_raw_parts(self.as_ptr(), len) }
    }

    /// Return a mutable slice containing all elements of the vector.
    pub unsafe fn as_mut_slice(&mut self, len: usize) -> &mut [T] {
        debug_assert_eq!(self.len, len);
        debug_assert!(len <= Self::CAPACITY);
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), len) }
    }

    fn as_ptr(&self) -> *const T {
        self.xs.as_ptr() as _
    }

    fn as_mut_ptr(&mut self) -> *mut T {
        self.xs.as_mut_ptr() as _
    }

    pub unsafe fn push(&mut self, len: usize, element: T) {
        debug_assert_eq!(self.len, len);
        debug_assert!(len < Self::CAPACITY);

        #[cfg(debug_assertions)]
        {
            self.len += 1;
        }

        unsafe {
            ptr::write(self.as_mut_ptr().add(len), element);
        }
    }

    pub unsafe fn pop(&mut self, len: usize) -> T {
        debug_assert_eq!(self.len, len);
        debug_assert!(len <= Self::CAPACITY);
        debug_assert_ne!(len, 0);

        let new_len = len - 1;
        #[cfg(debug_assertions)]
        {
            self.len = new_len;
        }

        unsafe { ptr::read(self.as_ptr().add(new_len)) }
    }

    pub unsafe fn clear(&mut self, len: usize) {
        unsafe { self.truncate(len, 0) }
    }

    pub unsafe fn truncate(&mut self, old_len: usize, new_len: usize) {
        debug_assert_eq!(self.len, old_len);

        unsafe {
            if new_len < old_len {
                #[cfg(debug_assertions)]
                {
                    self.len = new_len;
                }

                let tail =
                    slice::from_raw_parts_mut(self.as_mut_ptr().add(new_len), old_len - new_len);
                ptr::drop_in_place(tail);
            }
        }
    }

    pub unsafe fn into_iter(self, len: usize) -> IntoIter<T, CAP> {
        debug_assert_eq!(len, self.len);

        IntoIter {
            index: 0,
            len,
            v: self,
        }
    }
}

/// By-value iterator for `ArrayVec`.
pub struct IntoIter<T, const CAP: usize> {
    index: usize,
    len: usize,
    v: DetachedArrayVec<T, CAP>,
}

impl<T, const CAP: usize> Iterator for IntoIter<T, CAP> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.len {
            None
        } else {
            unsafe {
                let index = self.index;
                self.index = index + 1;
                Some(ptr::read(self.v.get_unchecked_ptr(index)))
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len - self.index;
        (len, Some(len))
    }
}

impl<T, const CAP: usize> DoubleEndedIterator for IntoIter<T, CAP> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index == self.len {
            None
        } else {
            unsafe {
                let new_len = self.len - 1;
                self.len -= 1;
                Some(ptr::read(self.v.get_unchecked_ptr(new_len)))
            }
        }
    }
}

impl<T, const CAP: usize> ExactSizeIterator for IntoIter<T, CAP> {}

impl<T, const CAP: usize> Drop for IntoIter<T, CAP> {
    fn drop(&mut self) {
        // panic safety: Set length to 0 before dropping elements.
        let index = self.index;
        let len = self.len;
        unsafe {
            let elements = slice::from_raw_parts_mut(self.v.get_unchecked_ptr(index), len - index);
            ptr::drop_in_place(elements);
        }
    }
}

// /// A draining iterator for `ArrayVec`.
// pub struct Drain<'a, T: 'a, const CAP: usize> {
//     len: usize,
//     /// Index of tail to preserve
//     tail_start: usize,
//     /// Length of tail
//     tail_len: usize,
//     /// Current remaining range to remove
//     iter: slice::Iter<'a, T>,
//     vec: *mut DetachedArrayVec<T, CAP>,
// }

// unsafe impl<'a, T: Sync, const CAP: usize> Sync for Drain<'a, T, CAP> {}
// unsafe impl<'a, T: Send, const CAP: usize> Send for Drain<'a, T, CAP> {}

// impl<'a, T: 'a, const CAP: usize> Iterator for Drain<'a, T, CAP> {
//     type Item = T;

//     fn next(&mut self) -> Option<Self::Item> {
//         self.iter
//             .next()
//             .map(|elt| unsafe { ptr::read(elt as *const _) })
//     }

//     fn size_hint(&self) -> (usize, Option<usize>) {
//         self.iter.size_hint()
//     }
// }

// impl<'a, T: 'a, const CAP: usize> DoubleEndedIterator for Drain<'a, T, CAP> {
//     fn next_back(&mut self) -> Option<Self::Item> {
//         self.iter
//             .next_back()
//             .map(|elt| unsafe { ptr::read(elt as *const _) })
//     }
// }

// impl<'a, T: 'a, const CAP: usize> ExactSizeIterator for Drain<'a, T, CAP> {}

// impl<'a, T: 'a, const CAP: usize> Drop for Drain<'a, T, CAP> {
//     fn drop(&mut self) {
//         // len is currently 0 so panicking while dropping will not cause a double drop.

//         // exhaust self first
//         while let Some(_) = self.next() {}

//         if self.tail_len > 0 {
//             unsafe {
//                 let source_vec = &mut *self.vec;
//                 // memmove back untouched tail, update to new length
//                 let start = self.len;
//                 let tail = self.tail_start;
//                 let ptr = source_vec.as_mut_ptr();
//                 ptr::copy(ptr.add(tail), ptr.add(start), self.tail_len);
//             }
//         }
//     }
// }
