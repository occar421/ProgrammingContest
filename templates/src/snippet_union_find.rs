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
    pub use self::wrapped::UnionFindSet;

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
        use std::collections::HashMap;
        use std::fmt::{Debug, Formatter};
        use std::hash::Hash;
        use std::iter::FromIterator;

        pub struct UnionFindMap<N, V> {
            core: UnionFindCore,
            encode_map: HashMap<N, usize>,
            decode_map: Vec<N>,
            // only keeps root values
            data_map: HashMap<usize, V>,
        }

        impl<N: Hash + Eq, V: Clone> UnionFindMap<N, V> {
            /// O( log(N) )
            pub fn get_root_of(&self, node: impl Borrow<N>) -> Option<(&N, &V)> {
                let core_node = *self.encode_map.get(node.borrow())?;
                let core_root = self.core.get_root_of(core_node)?;
                Some((
                    self.decode_map.get(core_root)?,
                    self.data_map.get(&core_root)?,
                ))
            }

            pub fn get_size_of(&self, node: impl Borrow<N>) -> Option<usize> {
                let core_node = *self.encode_map.get(node.borrow())?;
                self.core.get_size_of(core_node)
            }

            /// O( log(N) )
            pub fn connect_between<F>(
                &mut self,
                a: impl Borrow<N>,
                b: impl Borrow<N>,
                merger: F,
            ) -> Option<bool>
            where
                F: Fn(V, V) -> V,
            {
                let core_a = *self.encode_map.get(a.borrow())?;
                let root_a = self.core.get_root_of(core_a)?;
                let core_b = *self.encode_map.get(b.borrow())?;
                let root_b = self.core.get_root_of(core_b)?;

                let connected = self.core.connect_between(core_a, core_b)?;
                if connected {
                    let common = self.core.get_root_of(core_a).unwrap();
                    let data_a = self.data_map.remove(&root_a).unwrap();
                    let data_b = self.data_map.remove(&root_b).unwrap();
                    self.data_map.insert(common, merger(data_a, data_b));
                }

                Some(connected)
            }

            pub fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = (&N, &V)> + 'a> {
                Box::new(self.core.get_roots().map(move |&core_root| {
                    (&self.decode_map[core_root], &self.data_map[&core_root])
                }))
            }

            #[inline]
            #[allow(dead_code)]
            pub fn union<F>(
                &mut self,
                a: impl Borrow<N>,
                b: impl Borrow<N>,
                merger: F,
            ) -> Option<bool>
            where
                F: Fn(V, V) -> V,
            {
                self.connect_between(a, b, merger)
            }

            #[inline]
            #[allow(dead_code)]
            pub fn find(&self, node: impl Borrow<N>) -> Option<(&N, &V)> {
                self.get_root_of(node)
            }
        }

        impl<N: Hash + Eq + Clone, V: Clone> FromIterator<(N, V)> for UnionFindMap<N, V> {
            fn from_iter<T: IntoIterator<Item = (N, V)>>(iter: T) -> Self {
                let mut length = 0;
                let mut encode_map = HashMap::new();
                let mut decode_map = vec![];
                let mut data_map = HashMap::new();
                for (i, (n, v)) in iter.into_iter().enumerate() {
                    length += 1;
                    encode_map.insert(n.clone(), i);
                    decode_map.push(n);
                    data_map.insert(i, v);
                }

                Self {
                    core: UnionFindCore::new(length),
                    encode_map,
                    decode_map,
                    data_map,
                }
            }
        }

        impl<N: Hash + Eq + Debug, V: Debug> Debug for UnionFindMap<N, V> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                writeln!(f, "{{")?;
                writeln!(f, "  encode_map: {:?}", self.encode_map)?;
                writeln!(f, "  decode_map: {:?}", self.decode_map)?;
                writeln!(f, "  data_map: {:?}", self.data_map)?;
                writeln!(f, "  core: {:?}", self.core)?;
                writeln!(f, "}}")
            }
        }

        pub struct UnionFindSet<N> {
            map: UnionFindMap<N, ()>,
        }

        impl<N: Hash + Eq + Clone> FromIterator<N> for UnionFindSet<N> {
            #[inline]
            fn from_iter<T: IntoIterator<Item = N>>(iter: T) -> Self {
                Self {
                    map: UnionFindMap::from_iter(iter.into_iter().map(|x| (x, ()))),
                }
            }
        }

        impl<N: Hash + Eq> UnionFindSet<N> {
            /// O( log(N) )
            #[inline]
            pub fn get_root_of(&self, node: impl Borrow<N>) -> Option<&N> {
                self.map.get_root_of(node).map(|(k, _)| k)
            }

            #[inline]
            pub fn get_size_of(&self, node: impl Borrow<N>) -> Option<usize> {
                self.map.get_size_of(node)
            }

            /// O( log(N) )
            #[inline]
            pub fn connect_between(
                &mut self,
                a: impl Borrow<N>,
                b: impl Borrow<N>,
            ) -> Option<bool> {
                self.map.connect_between(a, b, Self::noop)
            }

            #[inline]
            fn noop(_: (), _: ()) -> () {}

            #[inline]
            pub fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &N> + 'a> {
                Box::new(self.map.get_roots().map(|(k, _)| k))
            }

            #[inline]
            #[allow(dead_code)]
            pub fn union<F>(&mut self, a: impl Borrow<N>, b: impl Borrow<N>) -> Option<bool> {
                self.connect_between(a, b)
            }

            #[inline]
            #[allow(dead_code)]
            pub fn find(&self, node: impl Borrow<N>) -> Option<&N> {
                self.get_root_of(node)
            }
        }

        impl<N: Hash + Eq + Debug> Debug for UnionFindSet<N> {
            #[inline]
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                writeln!(f, "{:?}", self.map)
            }
        }
    }
}
