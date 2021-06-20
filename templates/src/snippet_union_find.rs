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
    use std::collections::HashSet;
    use std::fmt::Debug;
    use std::hash::Hash;

    pub trait UnionFind<T>: Debug {
        fn get_root_of(&self, node: T) -> Option<T>;
        fn get_size_of(&self, node: T) -> Option<Quantity>;
        fn connect_between(&mut self, a: T, b: T) -> Option<bool>;
        fn get_roots(&self) -> Vec<T>; // FIXME Iter

        #[inline]
        fn union(&mut self, a: T, b: T) -> Option<bool> {
            self.connect_between(a, b)
        }
        #[inline]
        fn find(&self, node: T) -> Option<T> {
            self.get_root_of(node)
        }
    }

    pub fn new_with_indices(n: Quantity) -> impl UnionFind<NodeIndex0Based> {
        plain::UnionFindPlain::new(n)
    }

    pub fn new_from_set<T: Hash + Eq + Debug + Copy /* FIXME */>(
        set: &HashSet<T>,
    ) -> impl UnionFind<T> {
        mapped::UnionFindMapped::new(set)
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

    mod mapped {
        use super::super::NodeIndex0Based;
        use super::plain::UnionFindPlain;
        use super::UnionFind;
        use crate::standard_io::Quantity;
        use std::collections::{HashMap, HashSet};
        use std::fmt::{Debug, Formatter};
        use std::hash::Hash;
        use std::iter::FromIterator;

        pub struct UnionFindMapped<T> {
            core: UnionFindPlain,
            map: HashMap<T, NodeIndex0Based>,
            r_map: HashMap<NodeIndex0Based, T>,
        }

        impl<T: Hash + Eq + Debug + Copy /* FIXME */> UnionFindMapped<T> {
            pub fn new(set: &HashSet<T>) -> Self {
                let labelled_values = set.iter().enumerate();
                UnionFindMapped {
                    core: UnionFindPlain::new(set.len()),
                    map: HashMap::from_iter(labelled_values.clone().map(|(i, &x)| (x, i))),
                    r_map: HashMap::from_iter(labelled_values.map(|(i, &x)| (i, x))),
                }
            }
        }

        impl<T: Hash + Eq + Debug> Debug for UnionFindMapped<T> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                writeln!(f, "UnionFindMapped {{")?;
                writeln!(f, "  map: {:?}", self.map)?;
                writeln!(f, "  r_map: {:?}", self.r_map)?;
                writeln!(f, "  core: {:?}", self.core)?;
                writeln!(f, "}}")
            }
        }

        impl<T: Hash + Eq + Debug + Copy /* FIXME*/> UnionFind<T> for UnionFindMapped<T> {
            fn get_root_of(&self, node: T) -> Option<T> {
                let core_node = *self.map.get(&node)?;
                let core_root = self.core.get_root_of(core_node)?;
                Some(self.r_map[&core_root])
            }

            fn get_size_of(&self, node: T) -> Option<Quantity> {
                let core_node = *self.map.get(&node)?;
                self.core.get_size_of(core_node)
            }

            fn connect_between(&mut self, a: T, b: T) -> Option<bool> {
                let core_a = *self.map.get(&a)?;
                let core_b = *self.map.get(&b)?;
                self.core.connect_between(core_a, core_b)
            }

            fn get_roots(&self) -> Vec<T> {
                self.core
                    .get_roots()
                    .iter()
                    .map(|core_root| self.r_map[core_root])
                    .collect()
            }
        }
    }
}
