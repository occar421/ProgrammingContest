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

    pub trait UnionFind<'i, N: 'i + Hash + Eq>: Debug {
        fn get_root_of(&self, node: impl Into<&'i N>) -> Option<&N>;
        fn get_size_of(&self, node: impl Into<&'i N>) -> Option<Quantity>;
        fn connect_between(&mut self, a: impl Into<&'i N>, b: impl Into<&'i N>) -> Option<bool>;
        fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &N> + 'a>;

        #[inline]
        fn union(&mut self, a: impl Into<&'i N>, b: impl Into<&'i N>) -> Option<bool> {
            self.connect_between(a, b)
        }
        #[inline]
        fn find(&self, node: impl Into<&'i N>) -> Option<&N> {
            self.get_root_of(node)
        }
    }

    pub fn new_with_indices<'a>(n: Quantity) -> impl UnionFind<'a, NodeIndex0Based> {
        plain::UnionFindPlain::new(n)
    }

    pub fn new_from_set<'a, N: Hash + Eq + Debug>(set: &'a HashSet<N>) -> impl UnionFind<N> + 'a {
        mapped::UnionFindMapped::new(set)
    }

    mod plain {
        use super::super::{NodeIndex0Based, Quantity};
        use super::UnionFind;

        #[derive(Debug)]
        enum Node {
            Root {
                size: Quantity,
                index: NodeIndex0Based,
            },
            Children {
                parent: NodeIndex0Based,
            },
        }

        #[derive(Debug)]
        pub struct UnionFindPlain {
            nodes: Vec<Node>,
        }

        impl UnionFindPlain {
            pub fn new(n: Quantity) -> Self {
                UnionFindPlain {
                    nodes: (0..n).map(|i| Node::Root { size: 1, index: i }).collect(),
                }
            }
        }

        impl<'i> UnionFind<'i, NodeIndex0Based> for UnionFindPlain {
            /// O( log(N) )
            /// Due to its immutability, it can't be O( α(N) ) by path compression
            fn get_root_of(&self, i: impl Into<&'i NodeIndex0Based>) -> Option<&NodeIndex0Based> {
                match self.nodes.get(*i.into())? {
                    Node::Root { index, .. } => Some(index),
                    Node::Children { parent } => self.get_root_of(parent),
                }
            }

            fn get_size_of(&self, i: impl Into<&'i NodeIndex0Based>) -> Option<Quantity> {
                match self.nodes[*self.get_root_of(i)?] {
                    Node::Root { size, .. } => size.into(),
                    _ => panic!("Illegal condition"),
                }
            }

            /// O( log(N) )
            fn connect_between(
                &mut self,
                a: impl Into<&'i NodeIndex0Based>,
                b: impl Into<&'i NodeIndex0Based>,
            ) -> Option<bool> {
                let mut a = *self.get_root_of(a)?;
                let mut b = *self.get_root_of(b)?;
                if a == b {
                    // already in the same union
                    return Some(false);
                }

                // Nodes with `a` and `b` must exist assured by ? op

                if self.get_size_of(&a) < self.get_size_of(&b) {
                    swap!(a, b);
                }

                self.nodes[a] = match self.nodes[a] {
                    Node::Root { size, index } => Node::Root {
                        size: size + self.get_size_of(&b).unwrap(),
                        index,
                    },
                    _ => panic!("Illegal condition"),
                };
                self.nodes[b] = Node::Children { parent: a };

                return Some(true);
            }

            fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &NodeIndex0Based> + 'a> {
                Box::new(self.nodes.iter().filter_map(|node| match node {
                    Node::Root { index, .. } => Some(index),
                    Node::Children { .. } => None,
                }))
            }
        }
    }

    mod mapped {
        use super::super::{NodeIndex0Based, Quantity};
        use super::plain::UnionFindPlain;
        use super::UnionFind;
        use std::collections::{HashMap, HashSet};
        use std::fmt::{Debug, Formatter};
        use std::hash::Hash;
        use std::iter::FromIterator;

        pub struct UnionFindMapped<'a, N> {
            core: UnionFindPlain,
            map: HashMap<&'a N, NodeIndex0Based>,
            r_map: HashMap<NodeIndex0Based, &'a N>,
        }

        impl<'a, N: Hash + Eq + Debug> UnionFindMapped<'a, N> {
            pub fn new(set: &'a HashSet<N>) -> Self {
                let labelled_values = set.iter().enumerate();

                UnionFindMapped {
                    core: UnionFindPlain::new(set.len()),
                    map: HashMap::from_iter(labelled_values.clone().map(|(i, x)| (x, i))),
                    r_map: HashMap::from_iter(labelled_values),
                }
            }
        }

        impl<N: Hash + Eq + Debug> Debug for UnionFindMapped<'_, N> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                writeln!(f, "UnionFindMapped {{")?;
                writeln!(f, "  map: {:?}", self.map)?;
                writeln!(f, "  r_map: {:?}", self.r_map)?;
                writeln!(f, "  core: {:?}", self.core)?;
                writeln!(f, "}}")
            }
        }

        impl<'i, N: 'i + Hash + Eq + Debug> UnionFind<'i, N> for UnionFindMapped<'_, N> {
            fn get_root_of(&self, node: impl Into<&'i N>) -> Option<&N> {
                let core_node = *self.map.get(node.into())?;
                let core_root = self.core.get_root_of(&core_node)?;
                Some(&self.r_map[core_root])
            }

            fn get_size_of(&self, node: impl Into<&'i N>) -> Option<Quantity> {
                let core_node = *self.map.get(node.into())?;
                self.core.get_size_of(&core_node)
            }

            fn connect_between(
                &mut self,
                a: impl Into<&'i N>,
                b: impl Into<&'i N>,
            ) -> Option<bool> {
                let core_a = *self.map.get(a.into())?;
                let core_b = *self.map.get(b.into())?;
                self.core.connect_between(&core_a, &core_b)
            }

            fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &N> + 'a> {
                Box::new(
                    self.core
                        .get_roots()
                        .map(move |core_root| self.r_map[core_root]),
                )
            }
        }
    }
}
