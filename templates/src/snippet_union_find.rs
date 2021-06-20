use crate::standard_io::{NodeIndex0Based, Quantity};

macro_rules! swap {
    ($v1:expr, $v2:expr) => {
        let buf = $v1;
        $v1 = $v2;
        $v2 = buf;
    };
}

pub mod union_find {
    //! UnionFind
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_union_find.rs

    use super::{NodeIndex0Based, Quantity};
    use std::fmt::Debug;

    pub trait UnionFind<T>: Debug {
        fn get_root_of(&self, node: T) -> Option<T>;
        fn get_size_of(&self, node: T) -> Option<Quantity>;
        fn connect_between(&mut self, a: T, b: T) -> Option<bool>;
        fn get_roots(&self) -> Vec<T>;

        #[inline]
        fn union(&mut self, a: T, b: T) -> Option<bool> {
            self.connect_between(a, b)
        }
        #[inline]
        fn find(&self, node: T) -> Option<T> {
            self.get_root_of(node)
        }
    }

    pub fn new(n: Quantity) -> Box<dyn UnionFind<NodeIndex0Based>> {
        Box::new(plain::UnionFindPlain::new(n))
    }

    mod plain {
        use super::super::{NodeIndex0Based, Quantity};
        use super::UnionFind;

        #[derive(Copy, Clone, Debug)]
        enum Node {
            RootWithSize(Quantity),
            ChildrenWithParent(NodeIndex0Based),
        }

        #[derive(Debug)]
        pub struct UnionFindPlain {
            nodes: Vec<Node>,
        }

        impl UnionFindPlain {
            pub fn new(n: Quantity) -> Self {
                UnionFindPlain {
                    nodes: vec![Node::RootWithSize(1); n],
                }
            }
        }

        impl UnionFind<NodeIndex0Based> for UnionFindPlain {
            /// O( log(N) )
            /// Due to its immutability, it can't be O( α(N) ) by path compression
            fn get_root_of(&self, i: NodeIndex0Based) -> Option<NodeIndex0Based> {
                match self.nodes.get(i)? {
                    Node::RootWithSize(_) => i.into(),
                    Node::ChildrenWithParent(parent) => self.get_root_of(*parent),
                }
            }

            fn get_size_of(&self, i: NodeIndex0Based) -> Option<Quantity> {
                match self.nodes[self.get_root_of(i)?] {
                    Node::RootWithSize(size) => size.into(),
                    _ => panic!("Illegal condition"),
                }
            }

            /// O( log(N) )
            fn connect_between(&mut self, a: NodeIndex0Based, b: NodeIndex0Based) -> Option<bool> {
                let mut a = self.get_root_of(a)?;
                let mut b = self.get_root_of(b)?;
                if a == b {
                    // already in the same union
                    return Some(false);
                }

                // Nodes with `a` and `b` must exist assured by ? op

                if self.get_size_of(a) < self.get_size_of(b) {
                    swap!(a, b);
                }

                self.nodes[a] = match self.nodes[a] {
                    Node::RootWithSize(size) => {
                        Node::RootWithSize(size + self.get_size_of(b).unwrap())
                    }
                    _ => panic!("Illegal condition"),
                };
                self.nodes[b] = Node::ChildrenWithParent(a);

                return Some(true);
            }

            fn get_roots(&self) -> Vec<NodeIndex0Based> {
                self.nodes
                    .iter()
                    .enumerate()
                    .filter_map(|(i, node)| match *node {
                        Node::RootWithSize(_) => Some(i),
                        Node::ChildrenWithParent(_) => None,
                    })
                    .collect()
            }
        }
    }
}
