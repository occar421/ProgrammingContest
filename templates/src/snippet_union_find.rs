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

    pub use self::wrapped::UnionFindMap;

    mod core {
        #[derive(Debug)]
        enum Node {
            Root { size: usize, index: usize },
            Children { parent: usize },
        }

        #[derive(Debug)]
        pub struct UnionFind {
            nodes: Vec<Node>,
        }

        impl UnionFind {
            pub fn new(n: usize) -> Self {
                UnionFind {
                    nodes: (0..n).map(|i| Node::Root { size: 1, index: i }).collect(),
                }
            }

            /// O( log(N) )
            /// Due to its immutability, it can't be O( α(N) ) by path compression
            pub fn get_root_of(&self, i: usize) -> Option<usize> {
                match self.nodes.get(i)? {
                    &Node::Root { index, .. } => Some(index),
                    &Node::Children { parent } => self.get_root_of(parent),
                }
            }

            pub fn get_size_of(&self, i: usize) -> Option<usize> {
                match self.nodes[self.get_root_of(i)?] {
                    Node::Root { size, .. } => size.into(),
                    _ => panic!("Illegal condition"),
                }
            }

            /// O( log(N) )
            pub fn connect_between(&mut self, a: usize, b: usize) -> Option<bool> {
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
                    Node::Root { size, index } => Node::Root {
                        size: size + self.get_size_of(b).unwrap(),
                        index,
                    },
                    _ => panic!("Illegal condition"),
                };
                self.nodes[b] = Node::Children { parent: a };

                return Some(true);
            }

            pub fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &usize> + 'a> {
                Box::new(self.nodes.iter().filter_map(|node| match node {
                    Node::Root { index, .. } => Some(index),
                    Node::Children { .. } => None,
                }))
            }
        }
    }

    mod wrapped {
        use super::core::UnionFind as UnionFindCore;
        use std::borrow::Borrow;
        use std::collections::{HashMap, HashSet};
        use std::fmt::{Debug, Formatter};
        use std::hash::Hash;
        use std::iter::FromIterator;

        pub struct UnionFindMap<'s, N> {
            core: UnionFindCore,
            encode_map: HashMap<&'s N, usize>,
            decode_map: HashMap<usize, &'s N>,
        }

        impl<'s, N: Hash + Eq + Debug> UnionFindMap<'s, N> {
            pub fn from_set(set: &'s HashSet<N>) -> Self {
                let labelled_values = set.iter().enumerate();

                Self {
                    core: UnionFindCore::new(set.len()),
                    encode_map: HashMap::from_iter(labelled_values.clone().map(|(i, x)| (x, i))),
                    decode_map: HashMap::from_iter(labelled_values),
                }
            }

            /// O( log(N) )
            pub fn get_root_of(&self, node: impl Borrow<N>) -> Option<&N> {
                let core_node = *self.encode_map.get(node.borrow())?;
                let core_root = self.core.get_root_of(core_node)?;
                Some(self.decode_map[&core_root])
            }

            pub fn get_size_of(&self, node: impl Borrow<N>) -> Option<usize> {
                let core_node = *self.encode_map.get(node.borrow())?;
                self.core.get_size_of(core_node)
            }

            /// O( log(N) )
            pub fn connect_between(
                &mut self,
                a: impl Borrow<N>,
                b: impl Borrow<N>,
            ) -> Option<bool> {
                let core_a = *self.encode_map.get(a.borrow())?;
                let core_b = *self.encode_map.get(b.borrow())?;
                self.core.connect_between(core_a, core_b)
            }

            pub fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &N> + 'a> {
                Box::new(
                    self.core
                        .get_roots()
                        .map(move |core_root| self.decode_map[core_root]),
                )
            }

            #[inline]
            #[allow(dead_code)]
            pub fn union(&mut self, a: impl Borrow<N>, b: impl Borrow<N>) -> Option<bool> {
                self.connect_between(a, b)
            }
            #[inline]
            #[allow(dead_code)]
            pub fn find(&self, node: impl Borrow<N>) -> Option<&N> {
                self.get_root_of(node)
            }
        }

        impl<N: Hash + Eq + Debug> Debug for UnionFindMap<'_, N> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                writeln!(f, "UnionFindMapped {{")?;
                writeln!(f, "  encode_map: {:?}", self.encode_map)?;
                writeln!(f, "  decode_map: {:?}", self.decode_map)?;
                writeln!(f, "  core: {:?}", self.core)?;
                writeln!(f, "}}")
            }
        }
    }
}
