#![warn(unsafe_op_in_unsafe_fn)]

use std::{mem::MaybeUninit, num::NonZeroUsize};

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

        let index = match pivots.binary_search_by(|pivot| pivot.cmp(&value)) {
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
    fn remove_last(&mut self, height: usize) -> Result<T, T> {
        assert!(Self::__M_IS_GREATER_THAN_ONE);
        assert!(Self::__M_IS_EVEN);

        if height == 0 {
            let value = unsafe { self.pivots.pop(self.len) };
            self.len -= 1;
            if self.len < M / 2 {
                Err(value)
            } else {
                Ok(value)
            }
        } else {
            let children = unsafe { self.children.tail.as_mut_slice(self.len) };
            match children.last_mut().unwrap().remove_last(height - 1) {
                Ok(last) => Ok(last),
                Err(last) => {
                    let mut last_child = unsafe { self.children.tail.pop(self.len) };
                    let last_pivot = unsafe { self.pivots.pop(self.len) };
                    self.len -= 1;

                    debug_assert_eq!(last_child.len, M / 2 - 1);

                    let prev_child = self.children.get_mut(self.len, self.len);
                    // we can merge
                    if prev_child.len == M / 2 {
                        debug_assert_eq!(prev_child.len + last_child.len + 1, M);
                        unsafe {
                            prev_child.pivots.push(M / 2, last_pivot);
                            for (i, pivot) in last_child.pivots.into_iter(M / 2 - 1).enumerate() {
                                prev_child.pivots.push(M / 2 + 1 + i, pivot);
                            }
                            if height > 1 {
                                prev_child
                                    .children
                                    .tail
                                    .push(M / 2, last_child.children.head.assume_init_read());
                                for (i, child) in
                                    last_child.children.tail.into_iter(M / 2 - 1).enumerate()
                                {
                                    prev_child.children.tail.push(M / 2 + 1 + i, child);
                                }
                            }
                            prev_child.len = M;
                        }

                        if self.len < M / 2 {
                            Err(last)
                        } else {
                            Ok(last)
                        }
                    } else {
                        unsafe {
                            // prev_child cannot underflow on removal.
                            let new_pivot = prev_child.remove_last(height - 1).unwrap_unchecked();

                            last_child.pivots.insert(M / 2 - 1, 0, last_pivot);

                            self.children.tail.push(self.len, last_child);
                            self.pivots.push(self.len, new_pivot);

                            self.len += 1;
                        }
                        Ok(last)
                    }
                }
            }
        }
    }

    // fn remove<Q: Comparable<T>>(&mut self, height: usize, q: &Q) -> RemoveResult<T> {
    //     assert!(Self::__M_IS_GREATER_THAN_ONE);
    //     assert!(Self::__M_IS_EVEN);

    //     // SAFETY: `len` pivots are init
    //     let pivots = unsafe { self.pivots.as_slice(self.len) };

    //     let index = match pivots.binary_search_by(|pivot| q.compare(pivot).reverse()) {
    //         Ok(index) => {
    //             if height == 0 {
    //                 let value = unsafe { self.pivots.remove(self.len, index) };
    //                 self.len -= 1;
    //                 if self.len < M / 2 {
    //                     return RemoveResult::Underflow(value);
    //                 } else {
    //                     return RemoveResult::Done(value);
    //                 }
    //             } else {
    //             }
    //         }
    //         Err(index) => index,
    //     };

    //     if height == 0 {
    //         return RemoveResult::None;
    //     }

    //     debug_assert!(self.len > 0, "non leaf nodes must have some children");
    //     let child = match index.checked_sub(1) {
    //         // SAFETY: head is always init when height > 0
    //         None => unsafe { self.children.head.assume_init_ref() },
    //         // SAFETY: len children are init
    //         Some(index) => unsafe { &self.children.tail.as_slice(self.len)[index] },
    //     };

    //     child.search(height - 1, q)
    // }
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
    None,
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

    pub fn remove_last(&mut self) -> Option<T> {
        if let Some(inner) = &mut self.0 {
            if inner.node.len == 0 {
                return None;
            };
            match inner.node.remove_last(inner.depth.get() - 1) {
                Ok(val) => Some(val),
                Err(val) => {
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
    fn insert() {
        let mut btree = OkBTree::new();
        btree.insert(1);
        dbg!(&btree);
        btree.insert(2);
        dbg!(&btree);
        btree.insert(3);
        dbg!(&btree);
        btree.insert(4);
        dbg!(&btree);
        btree.insert(5);
        dbg!(&btree);
        btree.insert(6);
        dbg!(&btree);
        btree.insert(7);
        dbg!(&btree);
        btree.insert(8);
        dbg!(&btree);
        btree.insert(9);
        dbg!(&btree);
        btree.insert(10);
        dbg!(&btree);
        btree.insert(11);
        dbg!(&btree);

        assert!(btree.get(&8).is_some());
        assert!(btree.get(&12).is_none());
        assert!(btree.get(&0).is_none());

        dbg!(btree.first());
        dbg!(btree.last());

        for _ in 1..=11 {
            dbg!(btree.remove_last());
            dbg!(&btree);
        }
    }
}
