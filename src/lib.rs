use std::cmp::max;
use std::mem::{forget, replace, size_of};
use std::slice;

/// A bit vector that can store small values inline.
///
/// `SmallBitVec` is exactly one word wide. If the rightmost bit is set, this word
/// stores a pointer to a heap allocation.  Otherwise, the data is stored inline
/// in the other bits.
pub struct SmallBitVec {
    data: usize,
}

/// Total number of bits per word.
fn inline_bits() -> u32 {
    size_of::<usize>() as u32 * 8
}

/// For an inline vector, all bits except two can be used as storage capacity:
///
/// - The rightmost bit is set to zero to signal an inline vector.
/// - The position of the rightmost nonzero bit encodes the length.
fn inline_capacity() -> u32 {
    inline_bits() - 2
}

/// The position of the nth bit of storage in an inline vector.
fn inline_index(n: u32) -> usize {
    debug_assert!(n <= inline_capacity());
    // The storage starts at the leftmost bit.
    1 << (inline_bits() - 1 - n)
}

/// If the rightmost bit of `data` is set, then the remaining bits of `data`
/// are a pointer to a heap allocation.
const HEAP_FLAG: usize = 1;

/// The allocation will contain a `Header` followed by a [Storage] buffer.
type Storage = u32;

/// The number of bits in one `Storage`.
fn bits_per_storage() -> u32 {
    size_of::<Storage>() as u32 * 8
}

/// Data stored at the start of the heap allocation.
///
/// `Header` must have the same alignment as `Storage`.
struct Header {
    /// The number of bits in this bit vector.
    len: Storage,

    /// The number of elements in the [u32] buffer that follows this header.
    buffer_len: Storage,
}

impl Header {
    /// Create a heap allocation with enough space for a header,
    /// plus a buffer of at least `cap` bits.
    fn with_capacity(cap: u32) -> *mut Header {
        let buffer_len = buffer_len(cap);
        let alloc_len = header_len() + buffer_len;

        let v: Vec<Storage> = vec![0; alloc_len];
        let header_ptr = v.as_ptr() as *mut Header;
        forget(v);

        unsafe {
            (*header_ptr).buffer_len = buffer_len as u32;
        }
        header_ptr
    }
}

/// The number of `Storage` elements to allocate to hold a header.
fn header_len() -> usize {
    size_of::<Header>() / size_of::<Storage>()
}

/// The minimum number of `Storage` elements to hold at least `cap` bits.
fn buffer_len(cap: u32) -> usize {
    ((cap + bits_per_storage() - 1) / bits_per_storage()) as usize
}

impl SmallBitVec {
    // Create an empty vector.
    #[inline]
    pub fn new() -> SmallBitVec {
        SmallBitVec {
            data: inline_index(0)
        }
    }

    // Create a vector with at least `cap` bits of storage.
    pub fn with_capacity(cap: u32) -> SmallBitVec {
        // Use inline storage if possible.
        if cap <= inline_capacity() {
            return SmallBitVec::new()
        }

        // Otherwise, allocate on the heap.
        let header_ptr = Header::with_capacity(cap);
        SmallBitVec {
            data: (header_ptr as usize) | HEAP_FLAG
        }
    }

    /// The number of bits stored in this bit vector.
    #[inline]
    pub fn len(&self) -> u32 {
        if self.is_inline() {
            // The rightmost nonzero bit is a sentinel.  All bits to the left of
            // the sentinel bit are the elements of the bit vector.
            inline_bits() - self.data.trailing_zeros() - 1
        } else {
            self.header().len
        }
    }

    /// Returns `true` if this vector contains no bits.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The number of bits that can be stored in this bit vector without re-allocating.
    #[inline]
    pub fn capacity(&self) -> u32 {
        if self.is_inline() {
            inline_capacity()
        } else {
            self.header().buffer_len * bits_per_storage()
        }
    }

    /// Get the nth bit in this bit vector.
    #[inline]
    pub fn get(&self, n: u32) -> bool {
        assert!(n < self.len(), "Index {} out of bounds", n);

        if self.is_inline() {
            self.data & inline_index(n) != 0
        } else {
            let buffer = self.buffer();
            let i = (n / bits_per_storage()) as usize;
            let offset = n % bits_per_storage();
            buffer[i] & (1 << offset) != 0
        }
    }

    /// Set the nth bit in this bit vector to `val`.
    pub fn set(&mut self, n: u32, val: bool) {
        assert!(n < self.len(), "Index {} out of bounds", n);

        if self.is_inline() {
            if val {
                self.data |= inline_index(n);
            } else {
                self.data &= !inline_index(n);
            }
        } else {
            let buffer = self.buffer_mut();
            let i = (n / bits_per_storage()) as usize;
            let offset = n % bits_per_storage();
            if val {
                buffer[i] |= 1 << offset;
            } else {
                buffer[i] &= !(1 << offset);
            }
        }
    }

    /// Append a bit to the end of the vector.
    ///
    /// ```
    /// use smallbitvec::SmallBitVec;
    /// let mut v = SmallBitVec::new();
    /// v.push(true);
    ///
    /// assert_eq!(v.len(), 1);
    /// assert_eq!(v.get(0), true);
    /// ```
    #[inline]
    pub fn push(&mut self, val: bool) {
        let idx = self.len();
        if idx == self.capacity() {
            self.reserve(1);
        }
        unsafe {
            self.set_len(idx + 1);
        }
        self.set(idx, val);
    }

    /// Remove the last bit from the vector and return it, if there is one.
    ///
    /// ```
    /// use smallbitvec::SmallBitVec;
    /// let mut v = SmallBitVec::new();
    /// v.push(false);
    ///
    /// assert_eq!(v.pop(), Some(false));
    /// assert_eq!(v.len(), 0);
    /// assert_eq!(v.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<bool> {
        let old_len = self.len();
        if old_len == 0 {
            return None
        }
        let val = self.get(old_len - 1);
        unsafe {
            self.set_len(old_len - 1);
        }
        Some(val)
    }

    /// Reserve capacity for at least `additional` more elements to be inserted.
    ///
    /// May reserve more space than requested, to avoid frequent reallocations.
    ///
    /// Panics if the new capacity overflows `u32`.
    ///
    /// Re-allocates only if `self.capacity() < self.len() + additional`.
    pub fn reserve(&mut self, additional: u32) {
        let old_cap = self.capacity();
        let new_cap = self.len().checked_add(additional).expect("capacity overflow");
        if new_cap <= old_cap {
            return
        }
        // Ensure the new capacity is at least double, to guarantee exponential growth.
        let double_cap = old_cap.saturating_mul(2);
        self.reallocate(max(new_cap, double_cap));
    }

    /// Set the length of the vector. The length must not exceed the capacity.
    ///
    /// If this makes the vector longer, then the values of its new elements
    /// are not specified.
    unsafe fn set_len(&mut self, len: u32) {
        debug_assert!(len <= self.capacity());
        if self.is_inline() {
            let sentinel = inline_index(len);
            let mask = !(sentinel - 1);
            self.data |= sentinel;
            self.data &= mask;
        } else {
            self.header_mut().len = len;
        }
    }

    /// Returns true if all the bits in the vec are set to zero/false.
    pub fn all_false(&self) -> bool {
        let mut len = self.len();
        if len == 0 {
            return true
        }

        if self.is_inline() {
            let mask = !(inline_index(len - 1) - 1);
            self.data & mask == 0
        } else {
            for &storage in self.buffer() {
                if len >= bits_per_storage() {
                    if storage != 0 {
                        return false
                    }
                    len -= bits_per_storage();
                } else {
                    let mask = (1 << len) - 1;
                    if storage & mask != 0 {
                        return false
                    }
                    break
                }
            }
            true
        }
    }

    /// Returns true if all the bits in the vec are set to one/true.
    pub fn all_true(&self) -> bool {
        let mut len = self.len();
        if len == 0 {
            return true
        }

        if self.is_inline() {
            let mask = !(inline_index(len - 1) - 1);
            self.data & mask == mask
        } else {
            for &storage in self.buffer() {
                if len >= bits_per_storage() {
                    if storage != !0 {
                        return false
                    }
                    len -= bits_per_storage();
                } else {
                    let mask = (1 << len) - 1;
                    if storage & mask != mask {
                        return false
                    }
                    break
                }
            }
            true
        }
    }

    /// Resize the vector to have capacity for at least `cap` bits.
    ///
    /// `cap` must be at least as large as the length of the vector.
    fn reallocate(&mut self, cap: u32) {
        let old_cap = self.capacity();
        if cap <= old_cap {
            return
        }
        assert!(self.len() <= cap);

        if self.is_heap() {
            let old_buffer_len = self.header().buffer_len as usize;
            let new_buffer_len = buffer_len(cap);

            let old_alloc_len = header_len() + old_buffer_len;
            let new_alloc_len = header_len() + new_buffer_len;

            let old_ptr = self.header_raw() as *mut Storage;
            let mut v = unsafe {
                Vec::from_raw_parts(old_ptr, old_alloc_len, old_alloc_len)
            };
            v.resize(new_alloc_len, 0);
            v.shrink_to_fit();
            self.data = v.as_ptr() as usize | HEAP_FLAG;
            forget(v);

            self.header_mut().buffer_len = new_buffer_len as u32;
        } else {
            let old_self = replace(self, SmallBitVec::with_capacity(cap));
            unsafe {
                self.set_len(old_self.len());
            }
            for i in 0..old_self.len() {
                self.set(i, old_self.get(i));
            }
        }
    }

    /// If the rightmost bit is set, then we treat it as inline storage.
    fn is_inline(&self) -> bool {
        self.data & 1 == 0
    }

    /// Otherwise, `data` is a pointer to a heap allocation.
    fn is_heap(&self) -> bool {
        !self.is_inline()
    }

    /// Get the header of a heap-allocated vector.
    fn header_raw(&self) -> *mut Header {
        assert!(self.is_heap());
        (self.data & !HEAP_FLAG) as *mut Header
    }

    fn header_mut(&mut self) -> &mut Header {
        unsafe { &mut *self.header_raw() }
    }

    fn header(&self) -> &Header {
        unsafe { &*self.header_raw() }
    }

    /// Get the buffer of a heap-allocated vector.
    fn buffer_raw(&self) -> *mut [Storage] {
        unsafe {
            let header_ptr = self.header_raw();
            let buffer_len = (*header_ptr).buffer_len as usize;
            let buffer_ptr = (header_ptr as *mut Storage)
                .offset((size_of::<Header>() / size_of::<Storage>()) as isize);
            slice::from_raw_parts_mut(buffer_ptr, buffer_len)
        }
    }

    fn buffer_mut(&self) -> &mut [Storage] {
        unsafe { &mut *self.buffer_raw() }
    }

    fn buffer(&self) -> &[Storage] {
        unsafe { &*self.buffer_raw() }
    }
}

impl Clone for SmallBitVec {
    fn clone(&self) -> Self {
        if self.is_inline() {
            return SmallBitVec { data: self.data }
        }

        let buffer_len = self.header().buffer_len as usize;
        let alloc_len = header_len() + buffer_len;
        let ptr = self.header_raw() as *mut Storage;
        let raw_allocation = unsafe {
            slice::from_raw_parts(ptr, alloc_len)
        };

        let v = raw_allocation.to_vec();
        let header_ptr = v.as_ptr() as *mut Header;
        forget(v);
        SmallBitVec {
            data: (header_ptr as usize) | HEAP_FLAG
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_pointer_width = "32")]
    #[test]
    fn test_inline_capacity() {
        assert_eq!(inline_capacity(), 30);
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn test_inline_capacity() {
        assert_eq!(inline_capacity(), 62);
    }

    #[test]
    fn new() {
        let v = SmallBitVec::new();
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), inline_capacity());
        assert!(v.is_empty());
        assert!(v.is_inline());
    }

    #[test]
    fn with_capacity_inline() {
        for cap in 0..(inline_capacity() + 1) {
            let v = SmallBitVec::with_capacity(cap);
            assert_eq!(v.len(), 0);
            assert_eq!(v.capacity(), inline_capacity());
            assert!(v.is_inline());
        }
    }

    #[test]
    fn with_capacity_heap() {
        let cap = inline_capacity() + 1;
        let v = SmallBitVec::with_capacity(cap);
        assert_eq!(v.len(), 0);
        assert!(v.capacity() > inline_capacity());
        assert!(v.is_heap());
    }

    #[test]
    fn set_len_inline() {
        let mut v = SmallBitVec::new();
        for i in 0..(inline_capacity() + 1) {
            unsafe { v.set_len(i); }
            assert_eq!(v.len(), i);
        }
        for i in (0..(inline_capacity() + 1)).rev() {
            unsafe { v.set_len(i); }
            assert_eq!(v.len(), i);
        }
    }

    #[test]
    fn set_len_heap() {
        let mut v = SmallBitVec::with_capacity(500);
        unsafe { v.set_len(30); }
        assert_eq!(v.len(), 30);
    }

    #[test]
    fn push_many() {
        let mut v = SmallBitVec::new();
        for i in 0..500 {
            v.push(i % 3 == 0);
        }
        assert_eq!(v.len(), 500);

        for i in 0..500 {
            assert_eq!(v.get(i), (i % 3 == 0), "{}", i);
        }
    }

    #[test]
    #[should_panic]
    fn get_out_of_bounds() {
        let v = SmallBitVec::new();
        v.get(0);
    }

    #[test]
    #[should_panic]
    fn set_out_of_bounds() {
        let mut v = SmallBitVec::new();
        v.set(2, false);
    }

    #[test]
    fn all_false() {
        let mut v = SmallBitVec::new();
        assert!(v.all_false());
        for _ in 0..100 {
            v.push(false);
            assert!(v.all_false());

            let mut v2 = v.clone();
            v2.push(true);
            assert!(!v2.all_false());
        }
    }

    #[test]
    fn all_true() {
        let mut v = SmallBitVec::new();
        assert!(v.all_true());
        for _ in 0..100 {
            v.push(true);
            assert!(v.all_true());

            let mut v2 = v.clone();
            v2.push(false);
            assert!(!v2.all_true());
        }
    }
}
