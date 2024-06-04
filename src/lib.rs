// const M: usize = 8;
const M: usize = 2;

pub struct BadBTree<T> {
    root: Box<RootNode<T>>,
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
    pub fn new() -> Self {
        BadBTree {
            root: Box::new(RootNode {
                pivots: vec![],
                children: vec![],
            }),
        }
    }
}

impl<T: Ord> BadBTree<T> {
    pub fn insert(&mut self, value: T) {
        self.root.insert_inner(value);
        debug_assert!(self.root.check_invariants());
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
