use std::mem::size_of;
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

/// The rightmost non-zero bit in an inline vector of length `len`.
fn inline_sentinel(len: u32) -> usize {
    debug_assert!(len < inline_capacity());
    1 << (inline_bits() - 1 - len)
}

/// The position of the nth bit of storage in an inline vector.
fn inline_index(n: u32) -> usize {
    // The storage starts at the leftmost bit.
    1 << (inline_bits() - n)
}

/// If the rightmost bit of `data` is set, then the remaining bits of `data`
/// are a pointer to a heap allocation.
const HEAP_FLAG: usize = 1;

/// Data stored at the start of the heap allocation.
struct Header {
    /// The number of bits in this bit vector.
    len: u32,

    /// The number of elements in the [u32] buffer that follows this header.
    buffer_len: u32,
}

/// The allocation will contain a `Header` followed by a [u32] buffer.
type Storage = u32;

const BITS_PER_ELEM: u32 = 32;

impl SmallBitVec {
    // Create an empty vector.
    pub fn new() -> SmallBitVec {
        SmallBitVec {
            data: inline_sentinel(0)
        }
    }

    // Create a vector with at least `cap` bits of storage.
    pub fn with_capacity(cap: u32) -> SmallBitVec {
        // Use inline storage if possible.
        if cap <= inline_capacity() {
            return SmallBitVec::new()
        }

        // Otherwise, allocate on the heap.
        let header_len = size_of::<Header>() as u32 / BITS_PER_ELEM;
        let buffer_len = (cap + BITS_PER_ELEM - 1) / BITS_PER_ELEM;
        let v: Vec<Storage> = vec![0; header_len as usize + buffer_len as usize];

        let header_ptr = Box::into_raw(v.into_boxed_slice()) as *mut Header;
        unsafe {
            (*header_ptr).buffer_len = buffer_len;
        }
        
        SmallBitVec {
            data: (header_ptr as usize) | HEAP_FLAG
        }
    }

    /// The number of bits stored in this bit vector.
    #[inline]
    pub fn len(&self) -> u32 {
        if self.is_inline() {
            // The rightmost nonzero bit is a sentinal.  All bits to the left of
            // the sentinel bit are the elements of the bit vector.
            inline_bits() - self.data.trailing_zeros() - 1
        } else {
            self.header().len
        }
    }

    /// Returns `true` if this vector contains zero bits.
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
            self.header().buffer_len * BITS_PER_ELEM
        }
    }

    /// Get the nth bit in this bit vector.
    ///
    /// FIXME: Bounds checking.
    #[inline]
    pub fn get(&self, n: u32) -> bool {
        if self.is_inline() {
            self.data & inline_index(n) != 0
        } else {
            let buffer = self.buffer();
            let i = (n / BITS_PER_ELEM) as usize;
            let offset = n % BITS_PER_ELEM;
            buffer[i] & (1 << offset) != 0
        }
    }

    /// Set the nth bit in this bit vector to `val`.
    pub fn set(&mut self, n: u32, val: bool) {
        if self.is_inline() {
            if val {
                self.data |= inline_index(n);
            } else {
                self.data &= !inline_index(n);
            }
        } else {
            let buffer = self.buffer_mut();
            let i = (n / BITS_PER_ELEM) as usize;
            let offset = n % BITS_PER_ELEM;
            if val {
                buffer[i] |= (1 << offset);
            } else {
                buffer[i] &= !(1 << offset);
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
    fn with_capacity() {
        for cap in 0..(inline_capacity() + 1) {
            let v = SmallBitVec::with_capacity(cap);
            assert_eq!(v.len(), 0);
            assert_eq!(v.capacity(), inline_capacity());
            assert!(v.is_inline());
        }

        let cap = inline_capacity() + 1;
        let v = SmallBitVec::with_capacity(cap);
        assert_eq!(v.len(), 0);
        assert!(v.capacity() > inline_capacity());
        assert!(v.is_heap());
    }
}
