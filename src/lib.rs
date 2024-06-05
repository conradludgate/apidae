use std::{mem::MaybeUninit, num::NonZeroUsize};

// const M: usize = 8;
const M: usize = 2;

fn uninit_array<T, const N: usize>() -> [MaybeUninit<T>; N] {
    // Safety: uninit arrays are allowed to be assumed init
    unsafe { MaybeUninit::uninit().assume_init() }
}

unsafe fn slice_assume_init_mut<T>(slice: &mut [MaybeUninit<T>]) -> &mut [T] {
    // SAFETY: similar to safety notes for `slice_get_ref`, but we have a
    // mutable reference which is also guaranteed to be valid for writes.
    unsafe { &mut *(slice as *mut [MaybeUninit<T>] as *mut [T]) }
}

unsafe fn slice_assume_init<T>(slice: &[MaybeUninit<T>]) -> &[T] {
    unsafe { &*(slice as *const [MaybeUninit<T>] as *const [T]) }
}

impl<T, const M: usize> Children<T, M> {
    fn uninit() -> Self {
        Self {
            head: MaybeUninit::uninit(),
            tail: uninit_array(),
        }
    }
}

struct NodeArray<T, const M: usize> {
    len: usize,
    pivots: [MaybeUninit<T>; M],
    // empty if height = 0
    children: Children<T, M>,
}

impl<T, const M: usize> NodeArray<T, M> {
    fn drop_inner(&mut self, height: usize) {
        if std::mem::needs_drop::<T>() {
            for p in &mut self.pivots[..self.len] {
                unsafe { p.assume_init_drop() }
            }
        }
        if height > 0 {
            let mut head = *unsafe { self.children.head.assume_init_read() };
            head.drop_inner(height - 1);

            for c in &mut self.children.tail[..self.len] {
                let mut head = *unsafe { c.assume_init_read() };
                head.drop_inner(height - 1);
            }
        }
    }
}

// #[repr(C)]
struct Children<T, const M: usize> {
    head: MaybeUninit<Box<NodeArray<T, M>>>,
    tail: [MaybeUninit<Box<NodeArray<T, M>>>; M],
}

/// # Safety
/// slice is a valid &[MaybeUninit<T>]
/// * index <= len
/// * len < slice.len()
/// * slice[..len] is init.
unsafe fn insert<T>(mut slice: *mut T, len: usize, i: usize, value: T) {
    unsafe {
        // let (_lhs, rhs) = pivots.split_at(index);
        // rhs.len() == len-index;
        let rhs = slice.add(i);

        // slice = _lhs || value || rhs.
        slice = slice.add(i);
        rhs.copy_to_nonoverlapping(slice.add(1), len - i);
        slice.write(value);
    }
}

impl<T: Ord, const M: usize> NodeArray<T, M> {
    #[cold]
    fn rotate(
        &mut self,
        index: usize,
        value: T,
        child: Option<NodeArray<T, M>>,
    ) -> InsertResult2<T, M> {
        // we have a full pivots: [T; M]
        // which we can split as lhs: [T; M/2], rhs: [T; M/2].
        let mut lhs = self.pivots.as_mut_ptr().cast::<T>();
        let rhs = unsafe { self.pivots.as_ptr().add(M / 2).cast::<T>() };

        // // children is a full [Box<NodeArray<T, M>>; M+1]
        // // iff child is not none.
        // let children = &mut self.children as *mut _ as *mut Box<NodeArray<T, M>>;

        // we are creating a new node,
        // the values being split off from rhs will be written here.
        let mut new_node = NodeArray {
            len: 0,
            pivots: uninit_array::<T, M>(),
            children: Children::<T, M>::uninit(),
        };

        let mut out_p = new_node.pivots.as_mut_ptr().cast::<T>();
        // let mut out_c = &mut new_node.children as *mut _ as *mut Box<NodeArray<T, M>>;

        let mid = match usize::cmp(&index, &(M / 2)) {
            std::cmp::Ordering::Equal => {
                // in this case, lhs < value < rhs
                // write rhs to out.
                unsafe { rhs.copy_to_nonoverlapping(out_p, M / 2) }

                if let Some(child) = child {
                    unsafe {
                        new_node.children.head.write(Box::new(child));
                        let out = new_node.children.tail.as_mut_ptr();
                        let inp = self.children.tail.as_mut_ptr().add(M / 2);
                        inp.copy_to_nonoverlapping(out, M / 2);
                    }
                }

                value
            }
            std::cmp::Ordering::Less => {
                // in this case, value < rhs
                // write rhs to out.
                unsafe { rhs.copy_to_nonoverlapping(out_p, M / 2) }

                if child.is_some() {
                    unsafe {
                        let inp = self.children.tail.as_mut_ptr().add(M / 2);

                        new_node
                            .children
                            .head
                            .write(inp.sub(1).read().assume_init());
                        let out = new_node.children.tail.as_mut_ptr();
                        inp.copy_to_nonoverlapping(out, M / 2);
                    }
                }

                // let (lhs1, lhs2) = lhs.split_at(index);
                // lhs1.len() == index;
                // lhs2.len() == M/2-index;
                // let lhs1 = lhs;
                let lhs2 = unsafe { lhs.add(index) };

                // last value of lhs2 is the midpoint
                // let (mid, lhs2) = lhs2.split_last();
                // lhs2.len() == M/2 - index - 1;
                let mid = unsafe { lhs2.read() };
                // let lhs2 = unsafe { lhs2.add(M / 2 - index - 1) };

                // lhs = lhs1 || value || lhs2.
                unsafe {
                    lhs = lhs.add(index);
                    lhs2.copy_to(lhs.add(1), M / 2 - index - 1);
                    lhs.write(value);
                }

                if let Some(child) = child {
                    // [Box<NodeArray<T, M>>; M/2 - 1]
                    let mut lhs = self.children.tail.as_mut_ptr() as *mut Box<NodeArray<T, M>>;

                    // let (lhs1, lhs2) = lhs.split_at(index);
                    // lhs1.len() == index;
                    // lhs2.len() == M/2 - index - 1;
                    // let lhs1 = lhs;
                    let lhs2 = unsafe { lhs.add(index) };

                    // lhs = lhs1 || child || lhs2.
                    unsafe {
                        lhs = lhs.add(index);
                        lhs2.copy_to(lhs.add(1), M / 2 - index - 1);
                        lhs.write(Box::new(child));
                    }
                }

                mid
            }
            std::cmp::Ordering::Greater => {
                // in this case, lhs < value, so leave lhs untouched.
                let index = index - M / 2;

                // let (rhs1, rhs2) = rhs.split_at(index);
                // rhs1.len() == index;
                // rhs2.len() == M/2-index;
                let rhs1 = rhs;
                let rhs2 = unsafe { rhs.add(index) };

                // first value of rhs1 is the midpoint
                // let (mid, rhs1) = rhs1.split_first();
                // rhs1.len() == index - 1;
                let mid = unsafe { rhs1.read() };
                let rhs1 = unsafe { rhs1.add(1) };

                // out = rhs1 || value || rhs2
                unsafe {
                    rhs1.copy_to_nonoverlapping(out_p, index - 1);
                    out_p = out_p.add(index - 1);

                    out_p.write(value);
                    out_p = out_p.add(1);

                    rhs2.copy_to_nonoverlapping(out_p, M / 2 - index);
                }

                if let Some(child) = child {
                    // new_node.children.tail: [Box<NodeArray<T, M>>; M]
                    let tail = self.children.tail.as_mut_ptr() as *mut Box<NodeArray<T, M>>;
                    // rhs: [Box<NodeArray<T, M>>; M/2]
                    let rhs = unsafe { tail.add(M / 2) };

                    // let (rhs1, rhs2) = rhs.split_at(index);
                    // rhs1.len() == index;
                    // rhs2.len() == M/2-index;
                    let rhs1 = rhs;
                    let rhs2 = unsafe { rhs.add(index) };

                    // first value of rhs1 is the head
                    // let (head, rhs1) = rhs1.split_first();
                    // rhs1.len() == index - 1;
                    let head = unsafe { rhs1.read() };
                    let rhs1 = unsafe { rhs1.add(1) };

                    // out = rhs1 || child || rhs2
                    let mut out_p =
                        new_node.children.tail.as_mut_ptr() as *mut Box<NodeArray<T, M>>;
                    unsafe {
                        new_node.children.head.write(head);

                        rhs1.copy_to_nonoverlapping(out_p, index - 1);
                        out_p = out_p.add(index - 1);

                        out_p.write(Box::new(child));
                        out_p = out_p.add(1);

                        rhs2.copy_to_nonoverlapping(out_p, M / 2 - index);
                    }
                }

                mid
            }
        };
        self.len = M / 2;
        new_node.len = M / 2;
        InsertResult2::Propagate {
            pivot: mid,
            right: new_node,
        }
    }

    fn insert(&mut self, value: T, height: usize) -> InsertResult2<T, M> {
        // SAFETY: `len` pivots are init
        let pivots = unsafe { slice_assume_init_mut(&mut self.pivots[..self.len]) };

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
                // pivots: [T; self.len]
                let pivots = self.pivots.as_mut_ptr().cast::<T>();
                unsafe { insert(pivots, self.len, index, value) }

                self.len += 1;
                InsertResult2::Done
            }
        } else {
            let child = match index.checked_sub(1) {
                None => unsafe { self.children.head.assume_init_mut() },
                Some(index) => unsafe { self.children.tail[index].assume_init_mut() },
            };

            match child.insert(value, height - 1) {
                InsertResult2::Propagate { pivot, right } => {
                    if self.len == M {
                        self.rotate(index, pivot, Some(right))
                    } else {
                        // pivots: [T; self.len]
                        let pivots = self.pivots.as_mut_ptr().cast::<T>();
                        // children: [Box<NodeArray<T, M>>; self.len]
                        let children = self
                            .children
                            .tail
                            .as_mut_ptr()
                            .cast::<Box<NodeArray<T, M>>>();

                        unsafe {
                            insert(pivots, self.len, index, pivot);
                            insert(children, self.len, index, Box::new(right));
                        };

                        self.len += 1;

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
            inner.node.drop_inner(inner.depth.get() - 1)
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

        let pivots = unsafe { slice_assume_init(&self.array.pivots[..self.array.len]) };

        if self.height == 0 {
            list.entries(pivots);
        } else if self.array.len > 0 {
            list.entry(&NodeArrayFmt {
                height: self.height - 1,
                array: unsafe { self.array.children.head.assume_init_ref() },
            });

            let tail = unsafe { slice_assume_init(&self.array.children.tail[..self.array.len]) };
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
    Propagate { pivot: T, right: NodeArray<T, M> },
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
                    let mut node = NodeArray {
                        len: 1,
                        pivots: uninit_array(),
                        children: Children::uninit(),
                    };

                    node.pivots[0].write(pivot);
                    node.children.head.write(inner.node);
                    node.children.tail[0].write(Box::new(right));

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
            let mut pivots = uninit_array();
            pivots[0].write(value);
            self.0 = Some(BTreeInner {
                depth: NonZeroUsize::new(1).unwrap(),
                node: Box::new(NodeArray {
                    len: 1,
                    pivots,
                    children: Children::uninit(),
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
