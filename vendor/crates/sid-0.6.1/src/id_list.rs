use super::{Identifier, FromUsize};
use core::marker::PhantomData;
use core::ops;
use alloc::vec::Vec;

/// A trait that defines how to choose the null (or invalid) Id.
pub trait NullId<ID> {
    fn null_id() -> ID;
}

struct IdFreeListWrapper<ID, T> {
    payload: T,
    list_next: ID,
    list_prev: ID,
}

/// A linked list stored in contiguous memory allowing random access through ids.
pub struct IdFreeList<ID: Identifier, Data, C: NullId<ID>> {
    data: Vec<IdFreeListWrapper<ID, Data>>,
    first: ID,
    freelist: ID,
    _marker: PhantomData<C>,
}

impl<ID: Identifier, Data, C: NullId<ID>> IdFreeList<ID, Data, C> {
    /// Create an empty list.
    pub fn new() -> IdFreeList<ID, Data, C> {
        IdFreeList {
            data: Vec::new(),
            first: C::null_id(),
            freelist: C::null_id(),
            _marker: PhantomData,
        }
    }

    /// Create an empty list with a preallocated buffer.
    pub fn with_capacity(size: usize) -> IdFreeList<ID, Data, C> {
        IdFreeList {
            data: Vec::with_capacity(size as usize),
            first: C::null_id(),
            freelist: C::null_id(),
            _marker: PhantomData,
        }
    }

    /// Add an element to the list and return the id pointing to it
    pub fn add(&mut self, elt: Data) -> ID {
        let null_id = C::null_id();
        let first = self.first;
        if self.freelist == null_id {
            return self.push(elt);
        }

        let new_id = self.freelist;
        let freelist_next = self.data[new_id.to_usize()].list_next;
        self.data[new_id.to_usize()] = IdFreeListWrapper {
            payload: elt,
            list_next: first,
            list_prev: C::null_id(),
        };
        if freelist_next != null_id {
            self.data[freelist_next.to_usize()].list_prev = null_id;
        }
        self.freelist = freelist_next;

        if first != null_id {
            self.data[first.to_usize()].list_prev = new_id;
        }
        self.first = new_id;

        return new_id;
    }

    /// Add an element to the list at the end of the vector storage (without attempting
    /// to occupy a slot from the free-list).
    /// This means that repeated calls to push without calls to add or remove will produce
    /// contiguous indices.
    pub fn push(&mut self, elt: Data) -> ID {
        let null_id = C::null_id();
        let first = self.first;
        let new_id: ID = FromUsize::from_usize(self.data.len());
        self.data.push(IdFreeListWrapper {
            payload: elt,
            list_next: first,
            list_prev: null_id,
        });

        if first != null_id {
            self.data[first.to_usize()].list_prev = new_id;
        }
        self.first = new_id;

        return new_id;
    }

    /// Remove a given element from the list and place the slot in the free-list.
    /// Note that this does not attempt to drop the element.
    pub fn remove(&mut self, id: ID) {
        debug_assert!(self.has_id(id));
        let null_id = C::null_id();
        let prev = self.data[id.to_usize()].list_prev;
        let next = self.data[id.to_usize()].list_next;
        if prev != null_id {
            self.data[prev.to_usize()].list_next = next;
        } else {
            debug_assert!(id == self.first);
            self.first = self.data[id.to_usize()].list_next;
        }
        if next != null_id {
            self.data[next.to_usize()].list_prev = prev;
        }
        let elt = &mut self.data[id.to_usize()];
        elt.list_next = self.freelist;
        elt.list_prev = null_id;
        self.freelist = id;
    }

    /// Count the elements in O(N).
    pub fn count(&self) -> usize {
        let mut it = self.first_id();
        let mut i = 0;
        loop {
            match it {
                Some(current_id) => {
                    it = self.next_id(current_id);
                    i += 1;
                }
                None => {
                    return i;
                }
            }
        }
    }

    /// Return true if the id is found in the list in O(N).
    pub fn has_id(&self, id: ID) -> bool {
        if id.to_usize() >= self.data.len() {
            return false;
        }
        let mut it = self.first_id();
        loop {
            match it {
                Some(current_id) => {
                    if current_id == id {
                        return true;
                    }
                    it = self.next_id(current_id);
                }
                None => {
                    return false;
                }
            }
        }
    }

    /// Return true if there is no element in the list.
    pub fn is_empty(&self) -> bool {
        self.first == C::null_id()
    }

    /// Remove all elements from the list and clears the storage.
    /// Note that this will Drop the elements if Data implements Drop.
    pub fn clear(&mut self) {
        self.data.clear();
        self.first = C::null_id();
        self.freelist = C::null_id();
    }

    /// Return the next id in the list.
    pub fn next_id(&self, id: ID) -> Option<ID> {
        assert!(self.has_id(id));
        let next = self.data[id.to_usize()].list_next;
        return if next == C::null_id() {
            None
        } else {
            Some(next)
        };
    }

    /// Return the previous id in the list.
    pub fn previous_id(&self, id: ID) -> Option<ID> {
        assert!(self.has_id(id));
        let prev = self.data[id.to_usize()].list_prev;
        return if prev == C::null_id() {
            None
        } else {
            Some(prev)
        };
    }

    /// Return the first id in the list.
    pub fn first_id(&self) -> Option<ID> {
        return if self.first == C::null_id() {
            None
        } else {
            Some(self.first)
        };
    }
}

impl<ID: Identifier, Data, C: NullId<ID>> ops::Index<ID> for IdFreeList<ID, Data, C> {
    type Output = Data;
    fn index<'l>(&'l self, id: ID) -> &'l Data {
        // Enabling assertion is very expensive
        //debug_assert!(self.has_id(id));
        &self.data[id.to_usize()].payload
    }
}

impl<ID: Identifier, Data, C: NullId<ID>> ops::IndexMut<ID> for IdFreeList<ID, Data, C> {
    fn index_mut<'l>(&'l mut self, id: ID) -> &'l mut Data {
        // Enabling assertion is very expensive
        //debug_assert!(self.has_id(id));
        &mut self.data[id.to_usize()].payload
    }
}

/// Use this as the NullId type parameter of the freelist if the id type is an option,
/// to use `Option::None` as the null id value.
pub struct NoneAsNullId;

impl<T> NullId<Option<T>> for NoneAsNullId {
    fn null_id() -> Option<T> {
        None
    }
}


#[cfg(test)]
use super::Id;

#[cfg(test)]
type TestId = Id<u32, u32>;

#[cfg(test)]
struct MagicValue;

#[cfg(test)]
impl NullId<TestId> for MagicValue {
    fn null_id() -> TestId {
        return FromUsize::from_usize(::core::u32::MAX as usize);
    }
}

#[cfg(test)]
type TestIdFreeList = IdFreeList<TestId, u32, MagicValue>;

#[test]
fn vector_list() {
    let mut list: TestIdFreeList = TestIdFreeList::with_capacity(10);
    assert!(list.is_empty());
    assert_eq!(list.count(), 0);
    assert!(list.first_id().is_none());

    let a1 = list.add(1);
    let a2 = list.add(2);
    let a3 = list.add(3);

    assert_eq!(list[a1], 1);
    assert_eq!(list[a2], 2);
    assert_eq!(list[a3], 3);
    assert!(list.has_id(a1));
    assert!(list.has_id(a2));
    assert!(list.has_id(a3));
    assert!(!list.is_empty());
    assert_eq!(list.count(), 3);
    assert_eq!(list.first_id(), Some(a3));

    list.remove(a2);

    assert_eq!(list[a1], 1);
    assert_eq!(list[a3], 3);
    assert!(list.has_id(a1));
    assert!(list.has_id(a3));
    assert_eq!(list.count(), 2);
    assert_eq!(list.first_id(), Some(a3));

    list.remove(a1);

    assert_eq!(list[a3], 3);
    assert!(list.has_id(a3));
    assert_eq!(list.count(), 1);
    assert_eq!(list.first_id(), Some(a3));

    let a4 = list.add(4);

    assert_eq!(list[a3], 3);
    assert_eq!(list[a4], 4);
    assert!(list.has_id(a3));
    assert!(list.has_id(a4));
    assert_eq!(list.count(), 2);
    assert_eq!(list.first_id(), Some(a4));

    list.remove(a4);
    list.remove(a3);

    assert_eq!(list.count(), 0);
    assert!(!list.has_id(a1));
    assert!(!list.has_id(a2));
    assert!(!list.has_id(a3));
    assert!(!list.has_id(a4));
    assert!(list.is_empty());
    assert!(list.first_id().is_none());
}
