use std::{mem::MaybeUninit, num::NonZeroUsize};

use arrayvec::DetachedArrayVec;

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
    unsafe fn drop_inner(&mut self, height: usize) {
        if std::mem::needs_drop::<T>() {
            self.pivots.clear(self.len);
        }
        if height > 0 {
            debug_assert!(self.len > 0);
            self.children.head.assume_init_read().drop_inner(height - 1);

            for mut c in self.children.tail.drain(self.len, 0..self.len) {
                c.drop_inner(height - 1);
            }
        }
        self.len = 0;
    }
}

struct Children<T, const M: usize> {
    head: MaybeUninit<Box<NodeArray<T, M>>>,
    tail: DetachedArrayVec<Box<NodeArray<T, M>>, M>,
}

impl<T: Ord, const M: usize> NodeArray<T, M> {
    #[cold]
    fn rotate(
        &mut self,
        index: usize,
        value: T,
        child: Option<Box<NodeArray<T, M>>>,
    ) -> InsertResult2<T, M> {
        debug_assert_eq!(self.len, M);

        // we are creating a new node,
        // the values being split off from rhs will be written here.
        let mut new_node = NodeArray {
            len: 0,
            pivots: DetachedArrayVec::new(),
            children: Children::<T, M>::new(),
        };

        let mid = match usize::cmp(&index, &(M / 2)) {
            std::cmp::Ordering::Equal => unsafe {
                new_node.pivots = self.pivots.split_off(M, M / 2);

                if let Some(child) = child {
                    new_node.children.head.write(child);
                    new_node.children.tail = self.children.tail.split_off(M, M / 2);
                }

                value
            },
            std::cmp::Ordering::Less => unsafe {
                new_node.pivots = self.pivots.split_off(M, M / 2);
                let mid = self.pivots.pop(M / 2);
                self.pivots.insert(M / 2 - 1, index, value);

                if let Some(child) = child {
                    new_node.children.tail = self.children.tail.split_off(M, M / 2);
                    new_node.children.head.write(self.children.tail.pop(M / 2));
                    self.children.tail.insert(M / 2 - 1, index, child);
                }

                mid
            },
            std::cmp::Ordering::Greater => unsafe {
                let index = index - M / 2 - 1;
                new_node.pivots = self.pivots.split_off(M, M / 2 + 1);
                let mid = self.pivots.pop(M / 2 + 1);
                new_node.pivots.insert(M / 2 - 1, index, value);

                if let Some(child) = child {
                    new_node.children.tail = self.children.tail.split_off(M, M / 2 + 1);
                    new_node
                        .children
                        .head
                        .write(self.children.tail.pop(M / 2 + 1));
                    new_node.children.tail.insert(M / 2 - 1, index, child);
                }

                mid
            },
        };
        self.len = M / 2;
        new_node.len = M / 2;
        InsertResult2::Propagate {
            pivot: mid,
            right: Box::new(new_node),
        }
    }

    fn insert(&mut self, value: T, height: usize) -> InsertResult2<T, M> {
        // SAFETY: `len` pivots are init
        let pivots = unsafe { self.pivots.as_mut_slice(self.len) };

        let index = match pivots.binary_search_by(|pivot| pivot.cmp(&value)) {
            Ok(index) => {
                pivots[index] = value;
                return InsertResult2::Done;
            }
            Err(index) => index,
        };

        if height == 0 {
            // leaf node
            if self.len == M {
                self.rotate(index, value, None)
            } else {
                unsafe {
                    self.pivots.insert(self.len, index, value);
                    self.len += 1;
                }

                InsertResult2::Done
            }
        } else {
            debug_assert!(self.len > 0, "non leaf nodes must have some children");

            let child = match index.checked_sub(1) {
                None => unsafe { self.children.head.assume_init_mut() },
                Some(index) => unsafe { &mut self.children.tail.as_mut_slice(self.len)[index] },
            };

            match child.insert(value, height - 1) {
                InsertResult2::Propagate { pivot, right } => {
                    if self.len == M {
                        self.rotate(index, pivot, Some(right))
                    } else {
                        unsafe {
                            self.pivots.insert(self.len, index, pivot);
                            self.children.tail.insert(self.len, index, right);
                            self.len += 1;
                        }

                        InsertResult2::Done
                    }
                }
                InsertResult2::Done => InsertResult2::Done,
            }
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

        let pivots = unsafe { self.array.pivots.as_slice(self.array.len) };

        if self.height == 0 {
            list.entries(pivots);
        } else if self.array.len > 0 {
            list.entry(&NodeArrayFmt {
                height: self.height - 1,
                array: unsafe { self.array.children.head.assume_init_ref() },
            });

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

enum InsertResult2<T, const M: usize> {
    Propagate {
        pivot: T,
        right: Box<NodeArray<T, M>>,
    },
    Done,
}

impl<T> OkBTree<T> {
    pub const fn new() -> Self {
        OkBTree(None)
    }
}

impl<T: Ord> OkBTree<T> {
    pub fn insert(&mut self, value: T) {
        if let Some(mut inner) = self.0.take() {
            match inner.node.insert(value, inner.depth.get() - 1) {
                InsertResult2::Propagate { pivot, right } => {
                    let depth = inner.depth.checked_add(1).unwrap();
                    dbg!(depth);
                    let mut node = NodeArray {
                        len: 1,
                        pivots: DetachedArrayVec::new(),
                        children: Children::new(),
                    };

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
                InsertResult2::Done => {
                    self.0 = Some(inner);
                }
            }
        } else {
            let mut pivots = DetachedArrayVec::new();
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
    }
}
