use {IdRange, IntegerHandle, Identifier, FromUsize, ToUsize};
use core::marker::PhantomData;
use core::fmt;
use core::ops::{Add, Sub};
use core::hash::{Hash, Hasher};
use num_traits::One;

#[repr(C)]
pub struct Id<Tag, Handle = u32> {
    pub handle: Handle,
    pub _marker: PhantomData<Tag>,
}

impl<T, H: fmt::Display> fmt::Debug for Id<T, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Id#{}", self.handle)
    }
}

impl<T, H: Copy> Copy for Id<T, H> {}

impl<T, H: Copy> Clone for Id<T, H> {
    #[inline]
    fn clone(&self) -> Id<T, H> {
        *self
    }
}

impl<T, H: PartialEq> PartialEq for Id<T, H> {
    #[inline]
    fn eq(&self, other: &Id<T, H>) -> bool {
        self.handle.eq(&other.handle)
    }
}

impl<T, H: Copy + Eq> Eq for Id<T, H> {}

impl<T, H: IntegerHandle> Id<T, H> {
    #[inline]
    pub fn new(idx: H) -> Id<T, H> {
        Id {
            handle: idx,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn as_range(&self) -> IdRange<T, H> {
        IdRange::new(self.handle..self.handle + One::one())
    }
}

impl<T, H: IntegerHandle> Identifier for Id<T, H> {
    type Handle = H;
    type Tag = T;
}

impl<T, H: ToUsize> ToUsize for Id<T, H> {
    #[inline]
    fn to_usize(&self) -> usize {
        self.handle.to_usize()
    }
}

impl<T, H: IntegerHandle> FromUsize for Id<T, H> {
    #[inline]
    fn from_usize(idx: usize) -> Id<T, H> {
        Id::new(FromUsize::from_usize(idx))
    }
}

impl<T, Handle: Hash> Hash for Id<T, Handle> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.handle.hash(state);
    }
}

impl<T, Handle: IntegerHandle> Add<Handle> for Id<T, Handle> {
    type Output = Self;
    #[inline]
    fn add(self, offset: Handle) -> Self {
        Id::new(self.handle + offset)
    }
}

impl<T, Handle: IntegerHandle> Sub<Handle> for Id<T, Handle> {
    type Output = Self;
    #[inline]
    fn sub(self, offset: Handle) -> Self {
        Id::new(self.handle - offset)
    }
}
