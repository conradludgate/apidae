#![warn(unsafe_op_in_unsafe_fn)]

use std::{
    hint::unreachable_unchecked,
    mem::{self, MaybeUninit},
    num::NonZeroUsize,
};

use arrayvec::DetachedArrayVec;
use equivalent::Comparable;

mod arrayvec;

// const M: usize = 8;
const M: usize = 2;

impl<T, const M: usize> Children<T, M> {
    const fn new() -> Self {
        Self {
            head: MaybeUninit::uninit(),
            tail: DetachedArrayVec::new(),
        }
    }
}

struct NodeArray<T, const M: usize> {
    len: usize,
    pivots: DetachedArrayVec<T, M>,
    // empty if height = 0
    children: Children<T, M>,
}

impl<T, const M: usize> NodeArray<T, M> {
    /// # Safety
    /// height must be correct.
    unsafe fn drop_inner(&mut self, height: usize) {
        if std::mem::needs_drop::<T>() {
            // SAFETY: len pivots are init
            unsafe { self.pivots.clear(self.len) };
        }
        if height > 0 {
            debug_assert!(self.len > 0);
            // SAFETY: internal nodes must always have children
            unsafe { self.children.head.assume_init_read().drop_inner(height - 1) };

            let tail = self.children.tail.take();

            // SAFETY: len children are init in the tail.
            for mut c in unsafe { tail.into_iter(self.len) } {
                // SAFETY: height is correct and doesn't underflow.
                unsafe { c.drop_inner(height - 1) };
            }
        }
        self.len = 0;
    }
}

struct Children<T, const M: usize> {
    head: MaybeUninit<Box<NodeArray<T, M>>>,
    tail: DetachedArrayVec<Box<NodeArray<T, M>>, M>,
}

impl<T, const M: usize> Children<T, M> {
    fn get(&self, len: usize, index: usize) -> &NodeArray<T, M> {
        match index.checked_sub(1) {
            // SAFETY: head is always init when height > 0
            None => unsafe { self.head.assume_init_ref() },
            // SAFETY: tail len are init
            Some(index) => unsafe { &self.tail.as_slice(len)[index] },
        }
    }
    fn get_mut(&mut self, len: usize, index: usize) -> &mut NodeArray<T, M> {
        match index.checked_sub(1) {
            // SAFETY: head is always init when height > 0
            None => unsafe { self.head.assume_init_mut() },
            // SAFETY: tail len are init
            Some(index) => unsafe { &mut self.tail.as_mut_slice(len)[index] },
        }
    }
    unsafe fn push_front(&mut self, len: usize, t: Box<NodeArray<T, M>>) {
        unsafe {
            let head = mem::replace(self.head.assume_init_mut(), t);
            self.tail.insert(len, 0, head);
        }
    }
    unsafe fn pop_front(&mut self, len: usize) -> Box<NodeArray<T, M>> {
        unsafe { mem::replace(self.head.assume_init_mut(), self.tail.remove(len, 0)) }
    }
}

impl<T: Ord, const M: usize> NodeArray<T, M> {
    const __M_IS_GREATER_THAN_ONE: bool = {
        assert!(M > 1, "The fanout factor, M, must be greater than one");
        true
    };
    const __M_IS_EVEN: bool = {
        assert!(M % 2 == 0, "The fanout factor, M, must be even");
        true
    };

    #[cold]
    fn insert_split(
        &mut self,
        index: usize,
        value: T,
        child: Option<Box<NodeArray<T, M>>>,
    ) -> InsertResult<T, M> {
        debug_assert_eq!(self.len, M);
        debug_assert!(M >= 2);

        let m2 = M / 2;
        let m2m1 = m2 - 1;
        let m2p1 = m2 + 1;
        assert!(m2p1 <= M);
        assert!(m2 > 0);

        // we are creating a new node,
        // the values being split off from rhs will be written here.
        let mut new_node = NodeArray {
            len: 0,
            pivots: DetachedArrayVec::new(),
            children: Children::<T, M>::new(),
        };

        let mid = match usize::cmp(&index, &m2) {
            std::cmp::Ordering::Equal => unsafe {
                // SAFETY: M pivots are init. m2 < M.
                new_node.pivots = self.pivots.split_off(M, m2);

                if let Some(child) = child {
                    new_node.children.head.write(child);
                    // SAFETY: M children are init. m2 < M.
                    new_node.children.tail = self.children.tail.split_off(M, m2);
                }

                value
            },
            std::cmp::Ordering::Less => unsafe {
                new_node.pivots = self.pivots.split_off(M, m2);
                let mid = self.pivots.pop(m2);
                self.pivots.insert(m2m1, index, value);

                if let Some(child) = child {
                    new_node.children.tail = self.children.tail.split_off(M, m2);
                    new_node.children.head.write(self.children.tail.pop(m2));
                    self.children.tail.insert(m2m1, index, child);
                }

                mid
            },
            std::cmp::Ordering::Greater => unsafe {
                let index = index - m2p1;
                new_node.pivots = self.pivots.split_off(M, m2p1);
                let mid = self.pivots.pop(m2p1);
                new_node.pivots.insert(m2m1, index, value);

                if let Some(child) = child {
                    new_node.children.tail = self.children.tail.split_off(M, m2p1);
                    new_node.children.head.write(self.children.tail.pop(m2p1));
                    new_node.children.tail.insert(m2m1, index, child);
                }

                mid
            },
        };
        self.len = m2;
        new_node.len = m2;
        InsertResult::Propagate {
            pivot: mid,
            right: Box::new(new_node),
        }
    }

    fn insert(&mut self, mut value: T, height: usize) -> InsertResult<T, M> {
        assert!(Self::__M_IS_GREATER_THAN_ONE);
        assert!(Self::__M_IS_EVEN);

        // SAFETY: `len` pivots are init
        let pivots = unsafe { self.pivots.as_mut_slice(self.len) };

        let index = match Comp::from_comp(&value).binary_search(pivots, height) {
            Ok(index) => {
                pivots[index] = value;
                return InsertResult::Done;
            }
            Err(index) => index,
        };

        let mut new_child = None;
        // if this is an internal node, try and insert into the children
        if height > 0 {
            debug_assert!(self.len > 0, "non leaf nodes must have some children");

            let child = self.children.get_mut(self.len, index);

            match child.insert(value, height - 1) {
                InsertResult::Done => return InsertResult::Done,
                InsertResult::Propagate { pivot, right } => {
                    value = pivot;
                    new_child = Some(right);
                }
            }
        }

        if self.len == M {
            self.insert_split(index, value, new_child)
        } else {
            // SAFETY:
            // * len children and pivots are currently init
            // * len is less than cap.
            unsafe {
                self.pivots.insert(self.len, index, value);
                if let Some(child) = new_child {
                    self.children.tail.insert(self.len, index, child);
                }
                self.len += 1;
            }

            InsertResult::Done
        }
    }

    fn search<B: BinarySearch<T>>(&self, height: usize, b: &B) -> Option<&T> {
        assert!(Self::__M_IS_GREATER_THAN_ONE);
        assert!(Self::__M_IS_EVEN);

        // SAFETY: `len` pivots are init
        let pivots = unsafe { self.pivots.as_slice(self.len) };

        let index = match b.binary_search(pivots, height) {
            Ok(index) => return Some(&pivots[index]),
            Err(index) => index,
        };

        if height == 0 {
            return None;
        }

        debug_assert!(self.len > 0, "non leaf nodes must have some children");
        let child = self.children.get(self.len, index);

        child.search(height - 1, b)
    }

    // ok - no underflow
    // err - underflow
    fn remove<B: BinarySearch<T>>(&mut self, height: usize, b: &B) -> Option<RemoveResult<T>> {
        assert!(Self::__M_IS_GREATER_THAN_ONE);
        assert!(Self::__M_IS_EVEN);

        // SAFETY: `len` pivots are init
        let pivots = unsafe { self.pivots.as_mut_slice(self.len) };

        let binary_search = b.binary_search(pivots, height);

        // leaf node.
        if height == 0 {
            let index = b.binary_search(pivots, height).ok()?;

            let value = unsafe { self.pivots.remove(self.len, index) };
            self.len -= 1;

            if self.len < M / 2 {
                return Some(RemoveResult::Underflow(value));
            } else {
                return Some(RemoveResult::Done(value));
            }
        }

        let (Ok(index) | Err(index)) = binary_search;
        let child = self.children.get_mut(self.len, index);
        let value = match binary_search {
            Ok(_) => child
                .remove(height - 1, &Last)?
                .map(|v| std::mem::replace(&mut pivots[index], v)),
            Err(_) => child.remove(height - 1, b)?,
        };
        let value = match value {
            RemoveResult::Done(value) => return Some(RemoveResult::Done(value)),
            RemoveResult::Underflow(value) => value,
        };

        let index = match index.checked_sub(1) {
            // SAFETY: head is always init when height > 0
            None => unsafe {
                let child = self.children.head.assume_init_mut();
                let next_child = &mut self.children.tail.as_mut_slice(self.len)[0];
                let pivot = &mut pivots[0];

                if next_child.len > M / 2 {
                    Self::rotate_left(height, child, pivot, next_child);
                    return Some(RemoveResult::Done(value));
                }

                // we can only merge
                let child = std::mem::replace(child, self.children.tail.remove(self.len, 0));
                let pivot = self.pivots.remove(self.len, 0);
                self.len -= 1;

                let next_child = self.children.head.assume_init_mut();

                Self::merge_left(height, *child, pivot, next_child);

                if self.len < M / 2 {
                    return Some(RemoveResult::Underflow(value));
                } else {
                    return Some(RemoveResult::Done(value));
                }
            },
            Some(index) => index,
        };

        let pivots = unsafe { self.pivots.as_mut_slice(self.len) };
        // debug_assert_eq!(child.len, M / 2 - 1);

        // check the right sibling first
        if index + 1 < self.len {
            let children = unsafe { self.children.tail.as_mut_slice(self.len) };
            let [child, next_child] = &mut children[index..index + 2] else {
                unsafe { unreachable_unchecked() }
            };
            let pivot = &mut pivots[index + 1];

            if next_child.len > M / 2 {
                Self::rotate_left(height, child, pivot, next_child);
                return Some(RemoveResult::Done(value));
            }
        }

        let [prev_child, child] = {
            match index.checked_sub(1) {
                None => unsafe {
                    [
                        self.children.head.assume_init_mut(),
                        &mut self.children.tail.as_mut_slice(self.len)[0],
                    ]
                },
                Some(index) => unsafe {
                    let children = self.children.tail.as_mut_slice(self.len);
                    let x: &mut [_; 2] = (&mut children[index..index + 2])
                        .try_into()
                        .unwrap_unchecked();
                    x.each_mut()
                },
            }
        };
        let pivot = &mut pivots[index];

        if prev_child.len > M / 2 {
            Self::rotate_right(height, prev_child, pivot, child);
            return Some(RemoveResult::Done(value));
        }

        // we can only merge

        let child = unsafe { self.children.tail.remove(self.len, index) };
        let pivot = unsafe { self.pivots.remove(self.len, index) };
        self.len -= 1;

        let prev_child = self.children.get_mut(self.len, index);
        Self::merge_right(height, prev_child, pivot, *child);

        if self.len < M / 2 {
            Some(RemoveResult::Underflow(value))
        } else {
            Some(RemoveResult::Done(value))
        }
    }

    fn merge_right(height: usize, lhs: &mut NodeArray<T, M>, pivot: T, rhs: NodeArray<T, M>) {
        debug_assert_eq!(lhs.len + rhs.len + 1, M);
        unsafe {
            lhs.pivots.push(M / 2, pivot);
            for (i, pivot) in rhs.pivots.into_iter(M / 2 - 1).enumerate() {
                lhs.pivots.push(M / 2 + 1 + i, pivot);
            }
            if height > 1 {
                lhs.children
                    .tail
                    .push(M / 2, rhs.children.head.assume_init_read());
                for (i, child) in rhs.children.tail.into_iter(M / 2 - 1).enumerate() {
                    lhs.children.tail.push(M / 2 + 1 + i, child);
                }
            }
            lhs.len = M;
        }
    }

    fn merge_left(height: usize, lhs: NodeArray<T, M>, pivot: T, rhs: &mut NodeArray<T, M>) {
        debug_assert_eq!(lhs.len + rhs.len + 1, M);
        let x = std::mem::replace(rhs, lhs);
        let (lhs, rhs) = (rhs, x);

        unsafe {
            lhs.pivots.push(M / 2 - 1, pivot);
            for (i, pivot) in rhs.pivots.into_iter(M / 2).enumerate() {
                lhs.pivots.push(M / 2 + i, pivot);
            }
            if height > 1 {
                lhs.children
                    .tail
                    .push(M / 2 - 1, rhs.children.head.assume_init_read());
                for (i, child) in rhs.children.tail.into_iter(M / 2).enumerate() {
                    lhs.children.tail.push(M / 2 + i, child);
                }
            }
            lhs.len = M;
        }
    }

    fn rotate_right(
        height: usize,
        lhs: &mut NodeArray<T, M>,
        pivot: &mut T,
        rhs: &mut NodeArray<T, M>,
    ) {
        debug_assert!(height > 0);
        debug_assert!(lhs.len > M / 2);
        debug_assert_eq!(rhs.len, M / 2 - 1);

        if height == 1 {
            // lhs and rhs are leaf nodes
            unsafe {
                let new = match lhs.remove(height - 1, &Last) {
                    Some(RemoveResult::Done(p)) => p,
                    // SAFETY: lhs cannot underflow on removal.
                    _ => unreachable_unchecked(),
                };

                let old = std::mem::replace(pivot, new);
                rhs.pivots.insert(M / 2 - 1, 0, old);

                rhs.len += 1;
            }
        } else {
            // lhs and rhs are internal nodes
            unsafe {
                let child = lhs.children.tail.pop(lhs.len);
                let new = lhs.pivots.pop(lhs.len);
                lhs.len -= 1;

                let old = std::mem::replace(pivot, new);
                rhs.pivots.insert(M / 2 - 1, 0, old);
                rhs.children.push_front(M / 2 - 1, child);

                rhs.len += 1;
            }
        }
    }

    fn rotate_left(
        height: usize,
        lhs: &mut NodeArray<T, M>,
        pivot: &mut T,
        rhs: &mut NodeArray<T, M>,
    ) {
        debug_assert!(height > 0);
        debug_assert!(rhs.len > M / 2);
        debug_assert_eq!(lhs.len, M / 2 - 1);

        if height == 1 {
            // lhs and rhs are leaf nodes
            unsafe {
                let new = match rhs.remove(height - 1, &First) {
                    Some(RemoveResult::Done(p)) => p,
                    // SAFETY: rhs cannot underflow on removal.
                    _ => unreachable_unchecked(),
                };

                let old = std::mem::replace(pivot, new);
                lhs.pivots.push(M / 2 - 1, old);
                lhs.len += 1;
            }
        } else {
            // lhs and rhs are internal nodes
            unsafe {
                let child = rhs.children.pop_front(rhs.len);
                let new = rhs.pivots.remove(rhs.len, 0);
                rhs.len -= 1;

                let old = std::mem::replace(pivot, new);
                lhs.pivots.push(M / 2 - 1, old);
                lhs.children.tail.push(M / 2 - 1, child);
                lhs.len += 1;
            }
        }
    }
}

trait BinarySearch<K> {
    /// Compare self to `key` and return their ordering.
    fn binary_search(&self, pivots: &[K], height: usize) -> Result<usize, usize>;
}

impl<K, Q: Comparable<K>> BinarySearch<K> for Comp<Q> {
    fn binary_search(&self, pivots: &[K], _height: usize) -> Result<usize, usize> {
        pivots.binary_search_by(|pivot| self.0.compare(pivot).reverse())
    }
}

#[repr(transparent)]
struct Comp<Q>(Q);

impl<Q> Comp<Q> {
    fn from_comp(q: &Q) -> &Self {
        // SAFETY: transparent wrapper
        unsafe { std::mem::transmute(q) }
    }
}

struct Last;

impl<K> BinarySearch<K> for Last {
    fn binary_search(&self, pivots: &[K], height: usize) -> Result<usize, usize> {
        if height == 0 && !pivots.is_empty() {
            Ok(pivots.len() - 1)
        } else {
            Err(pivots.len())
        }
    }
}

struct First;

impl<K> BinarySearch<K> for First {
    fn binary_search(&self, pivots: &[K], height: usize) -> Result<usize, usize> {
        if height == 0 && !pivots.is_empty() {
            Ok(0)
        } else {
            Err(0)
        }
    }
}

pub struct OkBTree<T>(Option<BTreeInner<T>>);

pub struct BTreeInner<T> {
    depth: NonZeroUsize,
    node: Box<NodeArray<T, M>>,
}

impl<T: std::fmt::Debug> std::fmt::Debug for OkBTree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(node) = &self.0 {
            NodeArrayFmt {
                height: node.depth.get() - 1,
                array: &node.node,
            }
            .fmt(f)
        } else {
            f.debug_list().finish()
        }
    }
}

impl<T> Drop for OkBTree<T> {
    fn drop(&mut self) {
        if let Some(mut inner) = self.0.take() {
            // SAFETY: height is set correctly.
            unsafe { inner.node.drop_inner(inner.depth.get() - 1) }
        }
    }
}

struct NodeArrayFmt<'a, T, const M: usize> {
    height: usize,
    array: &'a NodeArray<T, M>,
}

impl<T: std::fmt::Debug, const M: usize> std::fmt::Debug for NodeArrayFmt<'_, T, M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();

        // SAFETY: len pivots are init
        let pivots = unsafe { self.array.pivots.as_slice(self.array.len) };

        if self.height == 0 {
            list.entries(pivots);
        } else {
            debug_assert_ne!(self.array.len, 0);

            list.entry(&NodeArrayFmt {
                height: self.height - 1,
                // SAFETY: head is always init when height > 0
                array: unsafe { self.array.children.head.assume_init_ref() },
            });

            // SAFETY: len children are init
            let tail = unsafe { self.array.children.tail.as_slice(self.array.len) };
            for (p, c) in std::iter::zip(pivots, tail) {
                list.entry(p);
                list.entry(&NodeArrayFmt {
                    height: self.height - 1,
                    array: c,
                });
            }
        }
        list.finish()
    }
}

enum InsertResult<T, const M: usize> {
    Propagate {
        pivot: T,
        right: Box<NodeArray<T, M>>,
    },
    Done,
}

enum RemoveResult<T> {
    Underflow(T),
    Done(T),
}

impl<T> RemoveResult<T> {
    fn map<U>(self, f: impl FnOnce(T) -> U) -> RemoveResult<U> {
        match self {
            RemoveResult::Underflow(value) => RemoveResult::Underflow(f(value)),
            RemoveResult::Done(value) => RemoveResult::Done(f(value)),
        }
    }
}

impl<T> OkBTree<T> {
    pub const fn new() -> Self {
        OkBTree(None)
    }
}

impl<T: Ord> OkBTree<T> {
    pub fn get<Q: Comparable<T>>(&self, q: &Q) -> Option<&T> {
        let inner = self.0.as_ref()?;
        inner.node.search(inner.depth.get() - 1, Comp::from_comp(q))
    }
    pub fn last(&self) -> Option<&T> {
        let inner = self.0.as_ref()?;
        inner.node.search(inner.depth.get() - 1, &Last)
    }
    pub fn first(&self) -> Option<&T> {
        let inner = self.0.as_ref()?;
        inner.node.search(inner.depth.get() - 1, &First)
    }

    fn remove_inner<B: BinarySearch<T>>(&mut self, b: &B) -> Option<T> {
        if let Some(inner) = &mut self.0 {
            if inner.node.len == 0 {
                return None;
            };
            match inner.node.remove(inner.depth.get() - 1, b)? {
                RemoveResult::Done(val) => Some(val),
                RemoveResult::Underflow(val) => {
                    if inner.node.len == 0 && inner.depth.get() > 1 {
                        inner.node = unsafe { inner.node.children.head.assume_init_read() };
                        inner.depth = NonZeroUsize::new(inner.depth.get() - 1).unwrap();
                    }

                    Some(val)
                }
            }
        } else {
            None
        }
    }

    pub fn remove_last(&mut self) -> Option<T> {
        self.remove_inner(&Last)
    }

    pub fn remove_first(&mut self) -> Option<T> {
        self.remove_inner(&First)
    }

    pub fn remove<Q: Comparable<T>>(&mut self, q: &Q) -> Option<T> {
        self.remove_inner(Comp::from_comp(q))
    }

    pub fn insert(&mut self, value: T) {
        if let Some(mut inner) = self.0.take() {
            match inner.node.insert(value, inner.depth.get() - 1) {
                InsertResult::Propagate { pivot, right } => {
                    let depth = inner.depth.checked_add(1).unwrap();
                    let mut node = NodeArray {
                        len: 1,
                        pivots: DetachedArrayVec::new(),
                        children: Children::new(),
                    };

                    // SAFETY:
                    // pivots and children are currently uninit.
                    // M > 1 so there is capacity available.
                    unsafe {
                        node.pivots.push(0, pivot);
                        node.children.head.write(inner.node);
                        node.children.tail.push(0, right);
                    }

                    self.0 = Some(BTreeInner {
                        depth,
                        node: Box::new(node),
                    })
                }
                InsertResult::Done => {
                    self.0 = Some(inner);
                }
            }
        } else {
            let mut pivots = DetachedArrayVec::new();
            // SAFETY:
            // pivots is currently uninit.
            // M > 1 so there is capacity available.
            unsafe { pivots.push(0, value) };
            self.0 = Some(BTreeInner {
                depth: NonZeroUsize::new(1).unwrap(),
                node: Box::new(NodeArray {
                    len: 1,
                    pivots,
                    children: Children::new(),
                }),
            });
        }
    }
}

impl<T> Default for OkBTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[inline(never)]
pub fn insert_i32(x: &mut OkBTree<i32>) {
    x.insert(1);
}

#[cfg(test)]
mod test {
    use crate::OkBTree;

    #[test]
    fn get() {
        let mut btree = OkBTree::new();
        for i in 50..100 {
            btree.insert(i);
        }

        for i in 50..100 {
            assert_eq!(btree.get(&i), Some(&i));
        }

        assert!(btree.get(&49).is_none());
        assert!(btree.get(&100).is_none());
        assert!(btree.get(&0).is_none());

        assert_eq!(btree.first(), Some(&50));
        assert_eq!(btree.last(), Some(&99));
    }

    #[test]
    fn remove_last() {
        let mut btree = OkBTree::new();
        for i in 0..100 {
            btree.insert(i);
        }

        for i in (0..100).rev() {
            assert_eq!(btree.remove_last(), Some(i));
        }
    }
    #[test]
    fn remove_first() {
        let mut btree = OkBTree::new();
        for i in 0..100 {
            btree.insert(i);
        }

        for i in 0..100 {
            assert_eq!(btree.remove_first(), Some(i));
        }
    }
    #[test]
    fn remove() {
        let mut btree = OkBTree::new();
        for i in 0..100 {
            btree.insert(i);
        }

        for i in 0..100 {
            assert_eq!(btree.remove(&i), Some(i));
        }
    }
}
