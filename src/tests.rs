// Copyright 2017 Matt Brubeck. See the COPYRIGHT file at the top-level
// directory of this distribution and at http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::*;

macro_rules! v {
    ($elem:expr; $n:expr) => ({
        SmallBitVec::from_elem($n, $elem)
    });
    ($($x:expr),*) => ({
        [$($x),*].iter().cloned().collect::<SmallBitVec>()
    });
}


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
        assert_eq!(v.get(i).unwrap(), (i % 3 == 0), "{}", i);
        assert_eq!(v[i as usize], v.get(i).unwrap());
    }
}

#[test]
#[should_panic]
fn index_out_of_bounds() {
    let v = SmallBitVec::new();
    v[0];
}

#[test]
#[should_panic]
fn index_u32_overflow() {
    let mut v = SmallBitVec::new();
    v.push(true);
    v[1 << 32];
}

#[test]
fn get_out_of_bounds() {
    let v = SmallBitVec::new();
    assert!(v.get(0).is_none());
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

#[test]
fn iter() {
    let mut v = SmallBitVec::new();
    v.push(true);
    v.push(false);
    v.push(false);

    let mut i = v.iter();
    assert_eq!(i.next(), Some(true));
    assert_eq!(i.next(), Some(false));
    assert_eq!(i.next(), Some(false));
    assert_eq!(i.next(), None);
}

#[test]
fn into_iter() {
    let mut v = SmallBitVec::new();
    v.push(true);
    v.push(false);
    v.push(false);

    let mut i = v.into_iter();
    assert_eq!(i.next(), Some(true));
    assert_eq!(i.next(), Some(false));
    assert_eq!(i.next(), Some(false));
    assert_eq!(i.next(), None);
}

#[test]
fn iter_back() {
    let mut v = SmallBitVec::new();
    v.push(true);
    v.push(false);
    v.push(false);

    let mut i = v.iter();
    assert_eq!(i.next_back(), Some(false));
    assert_eq!(i.next_back(), Some(false));
    assert_eq!(i.next_back(), Some(true));
    assert_eq!(i.next(), None);
}

#[test]
fn debug() {
    let mut v = SmallBitVec::new();
    v.push(true);
    v.push(false);
    v.push(false);

    assert_eq!(format!("{:?}", v), "[1, 0, 0]")
}

#[test]
fn from_elem() {
    for len in 0..100 {
        let ones = SmallBitVec::from_elem(len, true);
        assert_eq!(ones.len(), len);
        assert!(ones.all_true());

        let zeros = SmallBitVec::from_elem(len, false);
        assert_eq!(zeros.len(), len);
        assert!(zeros.all_false());
    }
}

#[test]
fn remove() {
    let mut v = SmallBitVec::new();
    v.push(false);
    v.push(true);
    v.push(false);
    v.push(false);
    v.push(true);

    v.remove(1);
    assert_eq!(format!("{:?}", v), "[0, 0, 0, 1]");
    v.remove(0);
    assert_eq!(format!("{:?}", v), "[0, 0, 1]");
    v.remove(2);
    assert_eq!(format!("{:?}", v), "[0, 0]");
    v.remove(1);
    assert_eq!(format!("{:?}", v), "[0]");
    v.remove(0);
    assert_eq!(format!("{:?}", v), "[]");
}

#[test]
fn remove_big() {
    let mut v = SmallBitVec::from_elem(256, false);
    v.set(100, true);
    v.set(255, true);
    v.remove(0);
    assert_eq!(v.len(), 255);
    assert_eq!(v.get(0).unwrap(), false);
    assert_eq!(v.get(99).unwrap(), true);
    assert_eq!(v.get(100).unwrap(), false);
    assert_eq!(v.get(253).unwrap(), false);
    assert_eq!(v.get(254).unwrap(), true);

    v.remove(254);
    assert_eq!(v.len(), 254);
    assert_eq!(v.get(0).unwrap(), false);
    assert_eq!(v.get(99).unwrap(), true);
    assert_eq!(v.get(100).unwrap(), false);
    assert_eq!(v.get(253).unwrap(), false);

    v.remove(99);
    assert_eq!(v, SmallBitVec::from_elem(253, false));
}

#[test]
fn eq() {
    assert_eq!(v![], v![]);
    assert_eq!(v![true], v![true]);
    assert_eq!(v![false], v![false]);

    assert_ne!(v![], v![false]);
    assert_ne!(v![true], v![]);
    assert_ne!(v![true], v![false]);
    assert_ne!(v![false], v![true]);

    assert_eq!(v![true, false], v![true, false]);
    assert_eq!(v![true; 400], v![true; 400]);
    assert_eq!(v![false; 400], v![false; 400]);

    assert_ne!(v![true, false], v![true, true]);
    assert_ne!(v![true; 400], v![true; 401]);
    assert_ne!(v![false; 401], v![false; 400]);
}
