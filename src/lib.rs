// const M: usize = 8;
const M: usize = 2;

pub struct BadBTreeMap<K, V> {
    root: Box<RootNode<K, V>>,
}

#[derive(Debug)]
struct RootNode<K, V> {
    pivots: Vec<(K, V)>,
    children: Vec<Node<K, V>>,
}

enum InsertResult<K, V> {
    Propagate { pivot: (K, V), right: Node<K, V> },
    Done,
}

impl<K, V> RootNode<K, V> {
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

impl<K: Ord, V> RootNode<K, V> {
    fn insert_inner(&mut self, key: K, value: V) {
        match self.pivots.binary_search_by(|pivot| pivot.0.cmp(&key)) {
            Ok(index) => {
                self.pivots[index].1 = value;
            }
            Err(index) => {
                // key = 4
                // pivots
                //  = [1,2,3,5,6]
                // index =   ^

                if self.children.is_empty() {
                    // leaf node
                    self.pivots.insert(index, (key, value));
                    if self.pivots.len() > M {
                        let rhs = self.pivots.split_off(M / 2 + 1);
                        let mid = self.pivots.pop().unwrap();
                        let lhs = std::mem::take(&mut self.pivots);
                        self.pivots = vec![mid];
                        self.children.push(Node::Leaf(LeafNode { pivots: lhs }));
                        self.children.push(Node::Leaf(LeafNode { pivots: rhs }));
                    }
                } else {
                    match self.children[index].insert_inner(key, value) {
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

impl<K, V> InternalNode<K, V> {
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

impl<K: Ord, V> InternalNode<K, V> {
    fn insert_inner(&mut self, key: K, value: V) -> InsertResult<K, V> {
        match self.pivots.binary_search_by(|pivot| pivot.0.cmp(&key)) {
            Ok(index) => {
                self.pivots[index].1 = value;
                InsertResult::Done
            }
            Err(index) => {
                // key = 4
                // pivots
                //  = [1,2,3,5,6]
                // index =   ^

                match self.children[index].insert_inner(key, value) {
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

impl<K, V> LeafNode<K, V> {
    fn check_invariants(&self) -> bool {
        self.pivots.len() <= M
    }
}

impl<K: Ord, V> LeafNode<K, V> {
    fn insert_inner(&mut self, key: K, value: V) -> InsertResult<K, V> {
        match self.pivots.binary_search_by(|pivot| pivot.0.cmp(&key)) {
            Ok(index) => {
                self.pivots[index].1 = value;
                InsertResult::Done
            }
            Err(index) => {
                // key = 4
                // pivots
                //  = [1,2,3,5,6]
                // index =   ^

                self.pivots.insert(index, (key, value));
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

impl<K, V> Node<K, V> {
    fn check_invariants(&self) -> bool {
        match self {
            Node::Internal(this) => this.check_invariants(),
            Node::Leaf(this) => this.check_invariants(),
        }
    }
}

impl<K: Ord, V> Node<K, V> {
    fn insert_inner(&mut self, key: K, value: V) -> InsertResult<K, V> {
        match self {
            Node::Internal(x) => x.insert_inner(key, value),
            Node::Leaf(x) => x.insert_inner(key, value),
        }
    }
}

#[derive(Debug)]
enum Node<K, V> {
    Internal(InternalNode<K, V>),
    Leaf(LeafNode<K, V>),
}

#[derive(Debug)]
struct InternalNode<K, V> {
    pivots: Vec<(K, V)>,
    children: Vec<Node<K, V>>,
}

#[derive(Debug)]
struct LeafNode<K, V> {
    pivots: Vec<(K, V)>,
}

impl<K, V> BadBTreeMap<K, V> {
    pub fn new() -> Self {
        BadBTreeMap {
            root: Box::new(RootNode {
                pivots: vec![],
                children: vec![],
            }),
        }
    }
}

impl<K: Ord, V> BadBTreeMap<K, V> {
    pub fn insert(&mut self, key: K, value: V) {
        self.root.insert_inner(key, value);
        debug_assert!(self.root.check_invariants());
    }
}

impl<K, V> Default for BadBTreeMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use crate::BadBTreeMap;

    #[test]
    fn insert() {
        let mut btree = BadBTreeMap::new();
        btree.insert(1, 1);
        dbg!(&btree.root);
        btree.insert(2, 2);
        dbg!(&btree.root);
        btree.insert(3, 3);
        dbg!(&btree.root);
        btree.insert(4, 4);
        dbg!(&btree.root);
        btree.insert(5, 5);
        dbg!(&btree.root);
        btree.insert(6, 6);
        dbg!(&btree.root);
        btree.insert(7, 7);
        dbg!(&btree.root);
        btree.insert(8, 8);
        dbg!(&btree.root);
        btree.insert(9, 9);
        dbg!(&btree.root);
        btree.insert(10, 10);
        dbg!(&btree.root);
        btree.insert(11, 11);
        dbg!(&btree.root);
    }
}
