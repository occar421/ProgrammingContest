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

    pub use mapped::UnionFindMapped as UnionFind;

    mod core {
        use super::super::{NodeIndex0Based, Quantity};

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
        pub struct UnionFindCore {
            nodes: Vec<Node>,
        }

        impl UnionFindCore {
            pub fn new(n: Quantity) -> Self {
                UnionFindCore {
                    nodes: (0..n).map(|i| Node::Root { size: 1, index: i }).collect(),
                }
            }

            /// O( log(N) )
            /// Due to its immutability, it can't be O( α(N) ) by path compression
            pub fn get_root_of(&self, i: NodeIndex0Based) -> Option<NodeIndex0Based> {
                match self.nodes.get(i)? {
                    &Node::Root { index, .. } => Some(index),
                    &Node::Children { parent } => self.get_root_of(parent),
                }
            }

            pub fn get_size_of(&self, i: NodeIndex0Based) -> Option<Quantity> {
                match self.nodes[self.get_root_of(i)?] {
                    Node::Root { size, .. } => size.into(),
                    _ => panic!("Illegal condition"),
                }
            }

            /// O( log(N) )
            pub fn connect_between(
                &mut self,
                a: NodeIndex0Based,
                b: NodeIndex0Based,
            ) -> Option<bool> {
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

            pub fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &NodeIndex0Based> + 'a> {
                Box::new(self.nodes.iter().filter_map(|node| match node {
                    Node::Root { index, .. } => Some(index),
                    Node::Children { .. } => None,
                }))
            }
        }
    }

    mod mapped {
        use super::super::{NodeIndex0Based, Quantity};
        use super::core::UnionFindCore;
        use std::borrow::Borrow;
        use std::collections::{HashMap, HashSet};
        use std::fmt::{Debug, Formatter};
        use std::hash::{Hash, Hasher};
        use std::iter::FromIterator;

        enum ReferenceKind<'s, N> {
            Ref(&'s N),
            Box(Box<N>),
        }

        impl<N> ReferenceKind<'_, N> {
            #[inline]
            fn unwrap(&self) -> &N {
                match self {
                    &ReferenceKind::Ref(r) => r,
                    ReferenceKind::Box(b) => b,
                }
            }
        }

        impl<'s, N: PartialEq> Eq for ReferenceKind<'s, N> {}
        impl<'s, N: PartialEq> PartialEq for ReferenceKind<'s, N> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                self.unwrap() == other.unwrap()
            }
        }

        impl<'s, N: Hash> Hash for ReferenceKind<'s, N> {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.unwrap().hash(state)
            }
        }

        impl<'s, N: Debug> Debug for ReferenceKind<'s, N> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                writeln!(f, "{:?}", self.unwrap())
            }
        }

        pub struct UnionFindMapped<'s, N: PartialEq + Hash + Debug> {
            core: UnionFindCore,
            map: HashMap<ReferenceKind<'s, N>, NodeIndex0Based>,
            r_map: HashMap<NodeIndex0Based, ReferenceKind<'s, N>>,
        }

        impl UnionFindMapped<'_, NodeIndex0Based> {
            pub fn new(n: Quantity) -> Self {
                Self {
                    core: UnionFindCore::new(n),
                    map: HashMap::from_iter((0..n).map(|i| (ReferenceKind::Box(i.into()), i))),
                    r_map: HashMap::from_iter((0..n).map(|i| (i, ReferenceKind::Box(i.into())))),
                }
            }
        }

        impl<'s, N: Hash + Eq + Debug> UnionFindMapped<'s, N> {
            pub fn from_set(set: &'s HashSet<N>) -> Self {
                let labelled_values = set.iter().enumerate();

                Self {
                    core: UnionFindCore::new(set.len()),
                    map: HashMap::from_iter(
                        labelled_values
                            .clone()
                            .map(|(i, x)| (ReferenceKind::Ref(x), i)),
                    ),
                    r_map: HashMap::from_iter(
                        labelled_values
                            .clone()
                            .map(|(i, x)| (i, ReferenceKind::Ref(x))),
                    ),
                }
            }

            /// O( log(N) )
            pub fn get_root_of(&self, node: impl Borrow<N>) -> Option<&N> {
                let core_node = *self.map.get(&ReferenceKind::Ref(node.borrow()))?;
                let core_root = self.core.get_root_of(core_node)?;
                Some(&self.r_map[&core_root].unwrap())
            }

            pub fn get_size_of(&self, node: impl Borrow<N>) -> Option<Quantity> {
                let core_node = *self.map.get(&ReferenceKind::Ref(node.borrow()))?;
                self.core.get_size_of(core_node)
            }

            /// O( log(N) )
            pub fn connect_between(
                &mut self,
                a: impl Borrow<N>,
                b: impl Borrow<N>,
            ) -> Option<bool> {
                let core_a = *self.map.get(&ReferenceKind::Ref(a.borrow()))?;
                let core_b = *self.map.get(&ReferenceKind::Ref(b.borrow()))?;
                self.core.connect_between(core_a, core_b)
            }

            pub fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &N> + 'a> {
                Box::new(
                    self.core
                        .get_roots()
                        .map(move |core_root| self.r_map[core_root].unwrap()),
                )
            }

            #[inline]
            #[allow(dead_code)]
            fn union(&mut self, a: impl Borrow<N>, b: impl Borrow<N>) -> Option<bool> {
                self.connect_between(a, b)
            }
            #[inline]
            #[allow(dead_code)]
            fn find(&self, node: impl Borrow<N>) -> Option<&N> {
                self.get_root_of(node)
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
    }
}
