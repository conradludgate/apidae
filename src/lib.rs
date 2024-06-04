use std::mem::MaybeUninit;

// const M: usize = 8;
const M: usize = 2;

#[repr(C)]
struct ArrayPlusOne<T, const M: usize> {
    head: MaybeUninit<T>,
    tail: [MaybeUninit<T>; M],
}

fn uninit_array<T, const N: usize>() -> [MaybeUninit<T>; N] {
    // Safety: uninit arrays are allowed to be assumed init
    unsafe { MaybeUninit::uninit().assume_init() }
}

unsafe fn slice_assume_init_mut<T>(slice: &mut [MaybeUninit<T>]) -> &mut [T] {
    // SAFETY: similar to safety notes for `slice_get_ref`, but we have a
    // mutable reference which is also guaranteed to be valid for writes.
    unsafe { &mut *(slice as *mut [MaybeUninit<T>] as *mut [T]) }
}

impl<T, const M: usize> ArrayPlusOne<T, M> {
    fn uninit() -> Self {
        Self {
            head: MaybeUninit::uninit(),
            tail: uninit_array(),
        }
    }
}
impl<T, const M: usize> std::ops::Deref for ArrayPlusOne<T, M> {
    type Target = [MaybeUninit<T>];

    fn deref(&self) -> &Self::Target {
        unsafe {
            &*std::ptr::slice_from_raw_parts(self as *const _ as *const MaybeUninit<T>, M + 1)
        }
    }
}
impl<T, const M: usize> std::ops::DerefMut for ArrayPlusOne<T, M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            &mut *std::ptr::slice_from_raw_parts_mut(self as *mut _ as *mut MaybeUninit<T>, M + 1)
        }
    }
}

struct NodeArray<T, const M: usize> {
    len: usize,
    pivots: [MaybeUninit<T>; M],
    // empty if height = 0
    children: ArrayPlusOne<Box<NodeArray<T, M>>, M>,
}

impl<T: Ord, const M: usize> NodeArray<T, M> {
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
                // we have a full pivots: [T; M]
                // which we can split as lhs: [T; M/2], rhs: [T; M/2].
                let mut lhs = self.pivots.as_mut_ptr().cast::<T>();
                let rhs = unsafe { self.pivots.as_ptr().add(M / 2).cast::<T>() };

                // we are creating a new leaf node,
                // the values being split off from rhs will be written here.
                let mut pivots = uninit_array::<T, M>();
                let mut out = pivots[..M / 2].as_mut_ptr().cast::<T>();

                let mid = match usize::cmp(&index, &(M / 2)) {
                    std::cmp::Ordering::Equal => {
                        // in this case, lhs < value < rhs
                        // write rhs to out.
                        unsafe { rhs.copy_to_nonoverlapping(out, M / 2) }
                        value
                    }
                    std::cmp::Ordering::Less => {
                        // in this case, value < rhs
                        // write rhs to out.
                        unsafe { rhs.copy_to_nonoverlapping(out, M / 2) }

                        // let (lhs1, lhs2) = lhs.split_at(index);
                        // lhs1.len() == index;
                        // lhs2.len() == M/2-index;
                        // let lhs1 = lhs;
                        let lhs2 = unsafe { lhs.add(index) };

                        // last value of lhs2 is the midpoint
                        // let (mid, lhs2) = lhs2.split_last();
                        // lhs2.len() == M/2 - index - 1;
                        let mid = unsafe { lhs2.read() };
                        let lhs2 = unsafe { lhs2.add(M / 2 - index - 1) };

                        // lhs = lhs1 || value || lhs2.
                        unsafe {
                            lhs = lhs.add(index);
                            lhs2.copy_to_nonoverlapping(lhs.add(1), M / 2 - index - 1);
                            lhs.write(value);
                        }

                        mid
                    }
                    std::cmp::Ordering::Greater => {
                        // in this case, lhs < value, so leave lhs untouched.

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
                            rhs1.copy_to_nonoverlapping(out, index - 1);
                            out = out.add(index - 1);

                            out.write(value);
                            out = out.add(1);

                            rhs2.copy_to_nonoverlapping(out, M / 2 - index);
                        }

                        mid
                    }
                };
                self.len = M / 2;
                InsertResult2::Propagate {
                    pivot: mid,
                    right: NodeArray {
                        len: M / 2,
                        pivots,
                        // new leaf has no children
                        children: ArrayPlusOne::uninit(),
                    },
                }
            } else {
                // pivots: [T; self.len]
                let mut pivots = self.pivots.as_mut_ptr().cast::<T>();

                // let (lhs, rhs) = pivots.split_at(index);
                // lhs.len() == index;
                // rhs.len() == self.len-index;
                // let lhs = pivots;
                let rhs = unsafe { pivots.add(index) };

                // pivots = lhs || value || rhs.
                unsafe {
                    pivots = pivots.add(index);
                    rhs.copy_to_nonoverlapping(pivots.add(1), self.len - index);
                    pivots.write(value);
                }

                InsertResult2::Done
            }
        } else {
            // SAFETY: `len+1` children are init
            let children = unsafe { slice_assume_init_mut(&mut self.children[..self.len + 1]) };

            match children[index].insert(value, height - 1) {
                InsertResult2::Propagate { pivot, right } => {
                    // self.pivots.insert(index, pivot);
                    // self.children.insert(index + 1, right);

                    // if self.pivots.len() > M {
                    //     let rhs = self.pivots.split_off(M / 2 + 1);
                    //     let mid = self.pivots.pop().unwrap();
                    //     let lhs = std::mem::take(&mut self.pivots);

                    //     let rhs_c = self.children.split_off(M / 2 + 1);
                    //     let lhs_c = std::mem::take(&mut self.children);

                    //     self.pivots = vec![mid];
                    //     self.children.push(Node::Internal(InternalNode {
                    //         pivots: lhs,
                    //         children: lhs_c,
                    //     }));
                    //     self.children.push(Node::Internal(InternalNode {
                    //         pivots: rhs,
                    //         children: rhs_c,
                    //     }));
                    // }

                    todo!()
                }
                InsertResult2::Done => InsertResult2::Done,
            }
        }
    }
}

pub struct BadBTree<T> {
    depth: usize,
    node: Option<Box<NodeArray<T, M>>>,
}

struct RootNode<T> {
    pivots: Vec<T>,
    children: Vec<Node<T>>,
}

impl<T: std::fmt::Debug> std::fmt::Debug for RootNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        if self.children.is_empty() {
            list.entries(&self.pivots);
        } else {
            for (i, p) in self.pivots.iter().enumerate() {
                list.entry(&self.children[i]);
                list.entry(p);
            }
            list.entry(self.children.last().unwrap());
        }
        list.finish()
    }
}

enum InsertResult<T> {
    Propagate { pivot: T, right: Node<T> },
    Done,
}

enum InsertResult2<T, const M: usize> {
    Propagate { pivot: T, right: NodeArray<T, M> },
    Done,
}

impl<T> RootNode<T> {
    fn check_invariants(&self) -> bool {
        // each node should not have more than M children
        if self.children.len() > M + 1 {
            return false;
        }
        if !self.children.is_empty() && self.pivots.len() + 1 != self.children.len() {
            return false;
        }

        self.children.iter().all(|x| x.check_invariants())
    }
}

impl<T: Ord> RootNode<T> {
    fn insert_inner(&mut self, value: T) {
        match self.pivots.binary_search_by(|pivot| pivot.cmp(&value)) {
            Ok(index) => {
                self.pivots[index] = value;
            }
            Err(index) => {
                // key = 4
                // pivots
                //  = [1,2,3,5,6]
                // index =   ^

                if self.children.is_empty() {
                    // leaf node
                    self.pivots.insert(index, value);
                    if self.pivots.len() > M {
                        let rhs = self.pivots.split_off(M / 2 + 1);
                        let mid = self.pivots.pop().unwrap();
                        let lhs = std::mem::take(&mut self.pivots);
                        self.pivots = vec![mid];
                        self.children.push(Node::Leaf(LeafNode { pivots: lhs }));
                        self.children.push(Node::Leaf(LeafNode { pivots: rhs }));
                    }
                } else {
                    match self.children[index].insert_inner(value) {
                        InsertResult::Propagate { pivot, right } => {
                            self.pivots.insert(index, pivot);
                            self.children.insert(index + 1, right);

                            if self.pivots.len() > M {
                                let rhs = self.pivots.split_off(M / 2 + 1);
                                let mid = self.pivots.pop().unwrap();
                                let lhs = std::mem::take(&mut self.pivots);

                                let rhs_c = self.children.split_off(M / 2 + 1);
                                let lhs_c = std::mem::take(&mut self.children);

                                self.pivots = vec![mid];
                                self.children.push(Node::Internal(InternalNode {
                                    pivots: lhs,
                                    children: lhs_c,
                                }));
                                self.children.push(Node::Internal(InternalNode {
                                    pivots: rhs,
                                    children: rhs_c,
                                }));
                            }
                        }
                        InsertResult::Done => {}
                    }
                }
            }
        }
    }
}

impl<T> InternalNode<T> {
    fn check_invariants(&self) -> bool {
        if self.children.len() > M + 1 || self.children.len() < (M + 1) / 2 {
            return false;
        }
        if self.pivots.len() + 1 != self.children.len() {
            return false;
        }

        self.children.iter().all(|x| x.check_invariants())
    }
}

impl<T: Ord> InternalNode<T> {
    fn insert_inner(&mut self, value: T) -> InsertResult<T> {
        match self.pivots.binary_search_by(|pivot| pivot.cmp(&value)) {
            Ok(index) => {
                self.pivots[index] = value;
                InsertResult::Done
            }
            Err(index) => {
                // key = 4
                // pivots
                //  = [1,2,3,5,6]
                // index =   ^

                match self.children[index].insert_inner(value) {
                    InsertResult::Propagate { pivot, right } => {
                        self.pivots.insert(index, pivot);
                        self.children.insert(index + 1, right);

                        if self.pivots.len() > M {
                            let rhs = self.pivots.split_off(M / 2 + 1);
                            let mid = self.pivots.pop().unwrap();
                            let rhs_c = self.children.split_off(M / 2 + 1);

                            InsertResult::Propagate {
                                pivot: mid,
                                right: Node::Internal(InternalNode {
                                    pivots: rhs,
                                    children: rhs_c,
                                }),
                            }
                        } else {
                            InsertResult::Done
                        }
                    }
                    InsertResult::Done => InsertResult::Done,
                }
            }
        }
    }
}

impl<T> LeafNode<T> {
    fn check_invariants(&self) -> bool {
        self.pivots.len() <= M
    }
}

impl<T: Ord> LeafNode<T> {
    fn insert_inner(&mut self, value: T) -> InsertResult<T> {
        match self.pivots.binary_search_by(|pivot| pivot.cmp(&value)) {
            Ok(index) => {
                self.pivots[index] = value;
                InsertResult::Done
            }
            Err(index) => {
                // key = 4
                // pivots
                //  = [1,2,3,5,6]
                // index =   ^

                self.pivots.insert(index, value);
                if self.pivots.len() > M {
                    let rhs = self.pivots.split_off(M / 2 + 1);
                    let mid = self.pivots.pop().unwrap();
                    InsertResult::Propagate {
                        pivot: mid,
                        right: Node::Leaf(LeafNode { pivots: rhs }),
                    }
                } else {
                    InsertResult::Done
                }
            }
        }
    }
}

impl<T> Node<T> {
    fn check_invariants(&self) -> bool {
        match self {
            Node::Internal(this) => this.check_invariants(),
            Node::Leaf(this) => this.check_invariants(),
        }
    }
}

impl<T: Ord> Node<T> {
    fn insert_inner(&mut self, value: T) -> InsertResult<T> {
        match self {
            Node::Internal(x) => x.insert_inner(value),
            Node::Leaf(x) => x.insert_inner(value),
        }
    }
}

enum Node<T> {
    Internal(InternalNode<T>),
    Leaf(LeafNode<T>),
}

impl<T: std::fmt::Debug> std::fmt::Debug for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Internal(arg0) => arg0.fmt(f),
            Self::Leaf(arg0) => arg0.fmt(f),
        }
    }
}

struct InternalNode<T> {
    pivots: Vec<T>,
    children: Vec<Node<T>>,
}

impl<T: std::fmt::Debug> std::fmt::Debug for InternalNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();

        for (i, p) in self.pivots.iter().enumerate() {
            list.entry(&self.children[i]);
            list.entry(p);
        }
        list.entry(self.children.last().unwrap());

        list.finish()
    }
}

struct LeafNode<T> {
    pivots: Vec<T>,
}

impl<T: std::fmt::Debug> std::fmt::Debug for LeafNode<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        list.entries(&self.pivots);
        list.finish()
    }
}

impl<T> BadBTree<T> {
    pub const fn new() -> Self {
        BadBTree {
            depth: 0,
            node: None,
        }
    }
}

impl<T: Ord> BadBTree<T> {
    pub fn insert(&mut self, value: T) {
        if self.depth == 0 {
            self.depth = 1;
            let mut pivots = uninit_array();
            pivots[0].write(value);
            self.node = Some(Box::new(NodeArray {
                len: 1,
                pivots,
                children: ArrayPlusOne::uninit(),
            }));
        } else {
        }
    }
}

impl<T> Default for BadBTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use crate::BadBTree;

    #[test]
    fn insert() {
        let mut btree = BadBTree::new();
        btree.insert(1);
        dbg!(&btree.root);
        btree.insert(2);
        dbg!(&btree.root);
        btree.insert(3);
        dbg!(&btree.root);
        btree.insert(4);
        dbg!(&btree.root);
        btree.insert(5);
        dbg!(&btree.root);
        btree.insert(6);
        dbg!(&btree.root);
        btree.insert(7);
        dbg!(&btree.root);
        btree.insert(8);
        dbg!(&btree.root);
        btree.insert(9);
        dbg!(&btree.root);
        btree.insert(10);
        dbg!(&btree.root);
        btree.insert(11);
        dbg!(&btree.root);
    }
}
