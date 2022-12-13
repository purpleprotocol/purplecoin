use {Id, IntegerHandle, FromUsize};
use core::marker::PhantomData;
use core::fmt;
use core::ops;
use core::cmp;
use num_traits::Zero;

pub struct IdRange<T, H = u32> {
    pub start: H,
    pub end: H,
    _marker: PhantomData<T>,
}

impl<T, H: fmt::Display> fmt::Debug for IdRange<T, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Id#[{}..{}]", self.start, self.end)
    }
}

impl<T, H: Copy> Copy for IdRange<T, H> {}

impl<T, H: Copy> Clone for IdRange<T, H> {
    fn clone(&self) -> IdRange<T, H> {
        *self
    }
}

impl<T, H: PartialEq> PartialEq for IdRange<T, H> {
    fn eq(&self, other: &IdRange<T, H>) -> bool {
        self.start.eq(&other.start) && self.end.eq(&other.end)
    }
}

impl<T, H: Copy + Eq> Eq for IdRange<T, H> {}

impl<T, H: IntegerHandle> IdRange<T, H> {
    #[inline]
    pub fn new(range: ops::Range<H>) -> Self {
        IdRange {
            start: range.start,
            end: range.end,
            _marker: PhantomData,
        }
    }

    #[inline]
    pub fn len(self) -> H {
        self.end - self.start
    }

    #[inline]
    pub fn empty() -> Self {
        IdRange::new(Zero::zero()..Zero::zero())
    }

    #[inline]
    pub fn is_empty(self) -> bool
    where
        H: Zero,
    {
        self.len() == Zero::zero()
    }

    #[inline]
    pub fn nth(self, i: H) -> Id<T, H> {
        debug_assert!(i < self.len());
        return Id {
            handle: self.start + i,
            _marker: PhantomData,
        };
    }

    #[inline]
    pub fn start(&self) -> Id<T, H> {
        Id::new(self.start)
    }

    #[inline]
    pub fn usize_start(&self) -> usize {
        self.start.to_usize()
    }

    #[inline]
    pub fn usize_end(&self) -> usize {
        self.end.to_usize()
    }

    #[inline]
    pub fn usize_range(&self) -> ops::Range<usize> {
        self.usize_start()..self.usize_end()
    }

    #[inline]
    pub fn untyped(&self) -> ops::Range<H> {
        self.start..self.end
    }

    #[inline]
    /// Return a range with the front element popped, or None if the range is empty.
    pub fn shrinked_left(self) -> Option<IdRange<T, H>> {
        if self.is_empty() {
            return None;
        }
        return Some(IdRange::new((self.start + H::one())..self.end));
    }

    #[inline]
    /// Return a range with the back element popped, or None if the range is empty.
    pub fn shrinked_right(self) -> Option<IdRange<T, H>> {
        if self.is_empty() {
            return None;
        }
        return Some(IdRange::new(
            self.start..FromUsize::from_usize(self.end.to_usize() - 1),
        ));
    }

    #[inline]
    pub fn intersection(&self, other: Self) -> Self {
        let start = cmp::max(self.start, other.start);
        let end = cmp::min(self.end, other.end);
        if end < start {
            return IdRange::empty();
        }
        return IdRange::new(start..end);
    }
}

impl<T, H: IntegerHandle> Iterator for IdRange<T, H> {
    type Item = Id<T, H>;
    fn next(&mut self) -> Option<Id<T, H>> {
        if let Some(new_range) = self.shrinked_left() {
            let first = self.start();
            *self = new_range;
            return Some(first);
        }
        return None;
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        return (self.len().to_usize(), Some(self.len().to_usize()));
    }

    fn count(self) -> usize {
        self.len().to_usize()
    }
}

pub struct ReverseIdRange<T, H> {
    range: IdRange<T, H>,
}

impl<T, H: fmt::Display> fmt::Debug for ReverseIdRange<T, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ReverseId#[{}..{}]", self.range.start, self.range.end)
    }
}

impl<T, H: Copy> Copy for ReverseIdRange<T, H> {}

impl<T, H: Copy> Clone for ReverseIdRange<T, H> {
    fn clone(&self) -> ReverseIdRange<T, H> {
        *self
    }
}

impl<T, H: PartialEq> PartialEq for ReverseIdRange<T, H> {
    fn eq(&self, other: &ReverseIdRange<T, H>) -> bool {
        self.range.eq(&other.range)
    }
}

impl<T, H: Copy + Eq> Eq for ReverseIdRange<T, H> {}

impl<T, H: IntegerHandle> ReverseIdRange<T, H> {
    pub fn new(range: IdRange<T, H>) -> ReverseIdRange<T, H> {
        ReverseIdRange { range: range }
    }

    pub fn len(&self) -> H {
        self.range.len()
    }

    pub fn is_empty(self) -> bool {
        self.len() == Zero::zero()
    }

    pub fn nth(self, i: H) -> Id<T, H> {
        self.range.nth(i)
    }
}

impl<T, H: IntegerHandle> Iterator for ReverseIdRange<T, H> {
    type Item = Id<T, H>;
    fn next(&mut self) -> Option<Id<T, H>> {
        if let Some(new_range) = self.range.shrinked_right() {
            self.range = new_range;
            return Some(Id::new(self.range.end));
        }
        return None;
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    fn count(self) -> usize {
        self.range.count()
    }
}
