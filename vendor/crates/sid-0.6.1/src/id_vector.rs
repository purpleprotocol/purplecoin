use {Identifier, FromUsize, ToUsize, IdRange};
use core::default::Default;
use core::slice;
use alloc::{vec, vec::Vec};
use core::marker::PhantomData;
use core::ops;
use core::iter::IntoIterator;
use num_traits::Zero;

/// Similar to Vec except that it is indexed using an Id rather than an usize index.
/// if the stored type implements Default, IdVec can also use the set(...) method which can
/// grow the vector to accomodate for the requested id.
pub struct IdVec<ID: Identifier, T> {
    data: Vec<T>,
    _idtype: PhantomData<ID>,
}

impl<ID: Identifier, T> IdVec<ID, T> {
    /// Create an empty IdVec
    #[inline]
    pub fn new() -> Self {
        IdVec {
            data: Vec::new(),
            _idtype: PhantomData,
        }
    }

    /// Create an IdVec with preallocated storage
    #[inline]
    pub fn with_capacity(size: ID::Handle) -> Self {
        IdVec {
            data: Vec::with_capacity(size.to_usize()),
            _idtype: PhantomData,
        }
    }

    /// Create an IdVec by recycling a Vec and its content.
    #[inline]
    pub fn from_vec(vec: Vec<T>) -> Self {
        IdVec {
            data: vec,
            _idtype: PhantomData,
        }
    }

    /// Consume the IdVec and create a Vec.
    #[inline]
    pub fn into_vec(self) -> Vec<T> {
        self.data
    }

    /// Exposes the internal Vec.
    #[inline]
    pub fn as_vec(&self) -> &Vec<T> {
        &self.data
    }

    /// Number of elements in the IdVec
    #[inline]
    pub fn len(&self) -> ID::Handle {
        FromUsize::from_usize(self.data.len())
    }

    /// Returns true if the vector contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Extracts a slice containing the entire vector.
    #[inline]
    pub fn as_slice(&self) -> IdSlice<ID, T> {
        IdSlice::new(self.data.as_slice())
    }

    /// Extracts a mutable slice containing the entire vector.
    #[inline]
    pub fn as_mut_slice(&mut self) -> MutIdSlice<ID, T> {
        MutIdSlice::new(self.data.as_mut_slice())
    }

    #[inline]
    pub fn range(&self, ids: IdRange<ID::Tag, ID::Handle>) -> IdSlice<ID, T> {
        IdSlice::new(&self.data[ids.start.to_usize()..ids.end.to_usize()])
    }

    #[inline]
    pub fn mut_range(&mut self, ids: IdRange<ID::Tag, ID::Handle>) -> MutIdSlice<ID, T> {
        MutIdSlice::new(&mut self.data[ids.start.to_usize()..ids.end.to_usize()])
    }

    #[inline]
    pub fn range_from(&self, id: ID) -> IdSlice<ID, T> {
        IdSlice::new(&self.data[id.to_usize()..])
    }

    #[inline]
    pub fn mut_range_from(&mut self, id: ID) -> MutIdSlice<ID, T> {
        MutIdSlice::new(&mut self.data[id.to_usize()..])
    }

    #[inline]
    pub fn range_to(&self, id: ID) -> IdSlice<ID, T> {
        IdSlice::new(&self.data[..id.to_usize()])
    }

    #[inline]
    pub fn mut_range_to(&mut self, id: ID) -> MutIdSlice<ID, T> {
        MutIdSlice::new(&mut self.data[..id.to_usize()])
    }

    #[inline]
    pub fn range_to_inclusive(&self, id: ID) -> IdSlice<ID, T> {
        IdSlice::new(&self.data[..(id.to_usize()+1)])
    }

    #[inline]
    pub fn mut_range_to_inclusive(&mut self, id: ID) -> MutIdSlice<ID, T> {
        MutIdSlice::new(&mut self.data[..(id.to_usize()+1)])
    }

    /// Return the nth element of the IdVec using an usize index rather than an Id (à la Vec).
    #[inline]
    pub fn nth(&self, idx: ID::Handle) -> &T {
        &self.data[idx.to_usize()]
    }

    /// Return the nth element of the IdVec using an usize index rather than an Id (à la Vec).
    #[inline]
    pub fn nth_mut(&mut self, idx: ID::Handle) -> &mut T {
        &mut self.data[idx.to_usize()]
    }

    /// Iterate over the elements of the IdVec
    #[inline]
    pub fn iter<'l>(&'l self) -> slice::Iter<'l, T> {
        self.data.iter()
    }

    /// Iterate over the elements of the IdVec
    #[inline]
    pub fn iter_mut<'l>(&'l mut self) -> slice::IterMut<'l, T> {
        self.data.iter_mut()
    }

    /// Add an element to the IdVec and return its Id.
    /// This method can cause the storage to be reallocated.
    #[inline]
    pub fn push(&mut self, elt: T) -> ID {
        let index = self.data.len();
        self.data.push(elt);
        return FromUsize::from_usize(index);
    }


    /// Inserts an element at position `id` within the vector, shifting all elements
    /// after it to the right.
    #[inline]
    pub fn insert(&mut self, id: ID, elt: T) {
        self.data.insert(id.to_usize(), elt);
    }

    /// Insert several elements by cloning them starting at position 'id` and shifting
    /// all elements after them to the right.
    pub fn insert_slice(&mut self, id: ID, elts: &[T]) where T: Clone {
        self.data.reserve(elts.len());
        let offset = id.to_usize();
        for (i, elt) in elts.iter().enumerate() {
            self.data.insert(offset + i, elt.clone());
        }
    }
    /// Insert several elements by cloning them starting at position 'id` and shifting
    /// all elements after them to the right.
    pub fn insert_id_slice(&mut self, id: ID, elts: IdSlice<ID, T>) where T: Clone {
        self.insert_slice(id, elts.untyped());
    }

    /// Clones and appends all elements in a slice to the vector.
    pub fn extend_from_slice(&mut self, elts: &[T]) where T: Clone {
        self.data.extend_from_slice(elts);
    }

    /// Clones and appends all elements in a slice to the vector.
    pub fn extend_from_id_slice(&mut self, elts: IdSlice<ID, T>) where T: Clone {
        self.data.extend_from_slice(elts.untyped());
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given vector.
    #[inline]
    pub fn reserve(&mut self, additional: ID::Handle) {
        self.data.reserve(additional.to_usize());
    }

    /// Shrinks the capacity of the vector as much as possible.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit();
    }

    /// Drop all of the contained elements and clear the IdVec's storage.
    #[inline]
    pub fn clear(&mut self) {
        self.data.clear();
    }

    /// Removes and returns the element at position index within the vector,
    /// shifting all elements after it to the left.
    #[inline]
    pub fn remove(&mut self, index: ID) -> T {
        self.data.remove(index.to_usize())
    }

    /// Removes an element from the vector and returns it.
    /// The removed element is replaced by the last element of the vector.
    #[inline]
    pub fn swap_remove(&mut self, index: ID) -> T {
        self.data.swap_remove(index.to_usize())
    }

    #[inline]
    pub fn has_id(&self, id: ID) -> bool {
        id.to_usize() < self.data.len()
    }

    #[inline]
    pub fn first_id(&self) -> Option<ID> {
        return if self.data.len() > 0 {
            Some(ID::from_usize(0))
        } else {
            None
        };
    }

    #[inline]
    pub fn last_id(&self) -> Option<ID> {
        return if self.data.len() > 0 {
            Some(ID::from_usize(self.data.len() - 1))
        } else {
            None
        };
    }

    #[inline]
    pub fn ids(&self) -> IdRange<ID::Tag, ID::Handle> {
        IdRange::new(Zero::zero()..self.len())
    }
}

impl<ID: Identifier, T: Default> IdVec<ID, T> {
    /// Set the value for a certain Id, possibly adding default values if the Id's index is Greater
    /// than the size of the underlying vector.
    pub fn set(&mut self, id: ID, val: T) {
        while self.len().to_usize() < id.to_usize() {
            self.push(T::default());
        }
        if self.len().to_usize() == id.to_usize() {
            self.push(val);
        } else {
            self[id] = val;
        }
    }
}

impl<T: Default, ID: Identifier> IdVec<ID, T> {
    pub fn resize(&mut self, size: ID::Handle) {
        if size.to_usize() > self.data.len() {
            let d = size.to_usize() - self.data.len();
            self.data.reserve(d as usize);
            for _ in 0..d {
                self.data.push(Default::default());
            }
        } else {
            let d = self.data.len() - size.to_usize();
            for _ in 0..d {
                self.data.pop();
            }
        }
    }

    /// Creates an IdVec with an n elements initialized to `Default::default`.
    pub fn with_len(n: ID::Handle) -> Self {
        let mut result: IdVec<ID, T> = IdVec::with_capacity(n);
        result.resize(n);
        return result;
    }
}

impl<ID: Identifier, T> ops::Index<ID> for IdVec<ID, T> {
    type Output = T;
    fn index<'l>(&'l self, id: ID) -> &'l T {
        &self.data[id.to_usize()]
    }
}

impl<ID: Identifier, T> ops::IndexMut<ID> for IdVec<ID, T> {
    fn index_mut<'l>(&'l mut self, id: ID) -> &'l mut T {
        &mut self.data[id.to_usize()]
    }
}

impl<ID: Identifier, T> IntoIterator for IdVec<ID, T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;
    #[inline]
    fn into_iter(self) -> vec::IntoIter<T> {
        self.data.into_iter()
    }
}

impl<'l, ID: Identifier, T> IntoIterator for &'l IdVec<ID, T> {
    type Item = &'l T;
    type IntoIter = slice::Iter<'l, T>;
    #[inline]
    fn into_iter(self) -> slice::Iter<'l, T> {
        (&self.data).into_iter()
    }
}

impl<'l, ID: Identifier, T> IntoIterator for &'l mut IdVec<ID, T> {
    type Item = &'l mut T;
    type IntoIter = slice::IterMut<'l, T>;
    #[inline]
    fn into_iter(self) -> slice::IterMut<'l, T> {
        (&mut self.data).into_iter()
    }
}


impl<ID: Identifier, T: Clone> Clone for IdVec<ID, T> {
    fn clone(&self) -> Self {
        IdVec {
            data: self.data.clone(),
            _idtype: PhantomData,
        }
    }
}

pub struct IdSlice<'l, ID: Identifier, T>
where
    T: 'l,
{
    slice: &'l [T],
    _idtype: PhantomData<ID>,
}

impl<'l, T, ID: Identifier> Copy for IdSlice<'l, ID, T>
where
    T: 'l,
{
}

impl<'l, T, ID: Identifier> Clone for IdSlice<'l, ID, T>
where
    T: 'l,
{
    #[inline]
    fn clone(&self) -> IdSlice<'l, ID, T> {
        IdSlice {
            slice: self.slice,
            _idtype: PhantomData,
        }
    }
}

impl<'l, T, ID: Identifier> IdSlice<'l, ID, T>
where
    T: 'l,
{
    #[inline]
    pub fn new(slice: &'l [T]) -> IdSlice<'l, ID, T> {
        IdSlice {
            slice: slice,
            _idtype: PhantomData,
        }
    }

    #[inline]
    pub fn len(&self) -> ID::Handle {
        FromUsize::from_usize(self.slice.len())
    }

    #[inline]
    pub fn untyped<'a>(&'a self) -> &'a [T] {
        self.slice
    }

    #[inline]
    pub fn iter<'a>(&'a self) -> slice::Iter<'a, T> {
        self.slice.iter()
    }

    #[inline]
    pub fn ids(&self) -> IdRange<ID::Tag, ID::Handle> {
        IdRange::new(Zero::zero()..self.len())
    }

    #[inline]
    pub fn nth(&self, idx: ID::Handle) -> &T {
        &self.slice[idx.to_usize()]
    }

    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.slice.first()
    }

    #[inline]
    pub fn last(&self) -> Option<&T> {
        self.slice.last()
    }

    #[inline]
    pub fn first_id(&self) -> Option<ID> {
        return if self.slice.len() > 0 {
            Some(ID::from_usize(0))
        } else {
            None
        };
    }

    #[inline]
    pub fn last_id(&self) -> Option<ID> {
        return if self.slice.len() > 0 {
            Some(ID::from_usize(self.slice.len() - 1))
        } else {
            None
        };
    }

    #[inline]
    pub fn split_at(&self, id: ID) -> (Self, Self) {
        let (s1, s2) = self.slice.split_at(id.to_usize());
        (Self::new(s1), Self::new(s2))
    }

    #[inline]
    pub fn range(&self, ids: IdRange<ID::Tag, ID::Handle>) -> IdSlice<ID, T> {
        IdSlice::new(&self.slice[ids.start.to_usize()..ids.end.to_usize()])
    }

    #[inline]
    pub fn range_from(&self, id: ID) -> IdSlice<ID, T> {
        IdSlice::new(&self.slice[id.to_usize()..])
    }

    #[inline]
    pub fn range_to(&self, id: ID) -> IdSlice<ID, T> {
        IdSlice::new(&self.slice[..id.to_usize()])
    }

    #[inline]
    pub fn range_to_inclusive(&self, id: ID) -> IdSlice<ID, T> {
        IdSlice::new(&self.slice[..(id.to_usize()+1)])
    }
}

impl<'l, ID: Identifier, T> ops::Index<ID> for IdSlice<'l, ID, T>
where
    T: 'l,
{
    type Output = T;
    #[inline]
    fn index<'a>(&'a self, id: ID) -> &'a T {
        &self.slice[id.to_usize()]
    }
}



pub struct MutIdSlice<'l, ID: Identifier, T: 'l> {
    slice: &'l mut [T],
    _idtype: PhantomData<ID>,
}

impl<'l, ID: Identifier, T: 'l> MutIdSlice<'l, ID, T> {
    #[inline]
    pub fn new(slice: &'l mut [T]) -> MutIdSlice<'l, ID, T> {
        MutIdSlice {
            slice: slice,
            _idtype: PhantomData,
        }
    }

    #[inline]
    pub fn len(&self) -> ID::Handle {
        FromUsize::from_usize(self.slice.len())
    }

    #[inline]
    pub fn untyped(&mut self) -> &mut [T] {
        self.slice
    }

    #[inline]
    pub fn iter<'a>(&'a self) -> slice::Iter<'a, T> {
        self.slice.iter()
    }

    #[inline]
    pub fn iter_mut<'a>(&'a mut self) -> slice::IterMut<'a, T> {
        self.slice.iter_mut()
    }

    #[inline]
    pub fn ids(&self) -> IdRange<ID::Tag, ID::Handle> {
        IdRange::new(Zero::zero()..self.len())
    }

    #[inline]
    pub fn nth(&mut self, idx: ID::Handle) -> &mut T {
        &mut self.slice[idx.to_usize()]
    }

    #[inline]
    pub fn first(&mut self) -> Option<&mut T> {
        self.slice.first_mut()
    }

    #[inline]
    pub fn last(&mut self) -> Option<&mut T> {
        self.slice.last_mut()
    }

    #[inline]
    pub fn range(&mut self, ids: IdRange<ID::Tag, ID::Handle>) -> MutIdSlice<ID, T> {
        MutIdSlice::new(&mut self.slice[ids.start.to_usize()..ids.end.to_usize()])
    }

    #[inline]
    pub fn range_from(&mut self, id: ID) -> MutIdSlice<ID, T> {
        MutIdSlice::new(&mut self.slice[id.to_usize()..])
    }

    #[inline]
    pub fn range_to(&mut self, id: ID) -> MutIdSlice<ID, T> {
        MutIdSlice::new(&mut self.slice[..id.to_usize()])
    }

    #[inline]
    pub fn range_to_inclusive(&mut self, id: ID) -> MutIdSlice<ID, T> {
        MutIdSlice::new(&mut self.slice[..(id.to_usize()+1)])
    }
}

impl<'l, ID: Identifier, T: 'l> IntoIterator for IdSlice<'l, ID, T> {
    type Item = &'l T;
    type IntoIter = slice::Iter<'l, T>;
    #[inline]
    fn into_iter(self) -> slice::Iter<'l, T> {
        self.slice.iter()
    }
}

impl<'l, ID: Identifier, T: 'l> IntoIterator for MutIdSlice<'l, ID, T> {
    type Item = &'l mut T;
    type IntoIter = slice::IterMut<'l, T>;
    #[inline]
    fn into_iter(self) -> slice::IterMut<'l, T> {
        self.slice.iter_mut()
    }
}

impl<'l, ID: Identifier, T: 'l> ops::Index<ID> for MutIdSlice<'l, ID, T> {
    type Output = T;
    #[inline]
    fn index<'a>(&'a self, id: ID) -> &'a T {
        &self.slice[id.to_usize()]
    }
}

impl<'l, ID: Identifier, T: 'l> ops::IndexMut<ID> for MutIdSlice<'l, ID, T> {
    #[inline]
    fn index_mut<'a>(&'a mut self, id: ID) -> &'a mut T {
        &mut self.slice[id.to_usize()]
    }
}

#[test]
fn test_id_vector() {
    use super::*;

    #[derive(Debug)]
    struct T;

    fn id(i: u16) -> Id<T, u16> {
        Id::new(i)
    }

    let mut v = IdVec::new();
    let a = v.push(42 as u32);
    assert_eq!(v[a], 42);
    v.set(a, 0);
    assert_eq!(v[a], 0);

    v.set(id(10), 100);
    assert_eq!(v[id(10)], 100);

    v.set(id(5), 50);
    assert_eq!(v[id(5)], 50);

    v.set(id(20), 200);
    assert_eq!(v[id(20)], 200);
    assert_eq!(v.len(), 21);
}

#[test]
fn test_id_vector_u32() {
    let _: IdVec<u32, u32> = IdVec::new();
    let _: IdVec<i32, i32> = IdVec::new();
}

#[test]
fn test_into_iter() {
    use super::*;

    let mut v: IdVec<u16, u16> = IdVec::from_vec(vec![
        0, 1, 2, 3, 4, 5
    ]);

    let mut idx = 0;
    for elt in &v {
        assert_eq!(*elt, idx);
        idx += 1;
    }

    for elt in &mut v {
        *elt += 1;
    }

    let mut idx = 0;
    for elt in &v {
        assert_eq!(*elt, idx + 1);
        idx += 1;
    }
}
