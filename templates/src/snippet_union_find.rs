use crate::swap;
use crate::standard_io::{NodeIndex0Based, Quantity};

// UnionFind
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_union_find.rs

#[derive(Copy, Clone)]
enum UnionFindNode {
    RootWithSize(Quantity),
    ChildrenWithParent(NodeIndex0Based),
}

pub struct UnionFind {
    nodes: Vec<UnionFindNode>,
}

impl UnionFind {
    pub fn new(n: Quantity) -> Self {
        UnionFind {
            nodes: vec![UnionFindNode::RootWithSize(1); n],
        }
    }

    /// Find
    pub fn get_root_of(&self, i: NodeIndex0Based) -> NodeIndex0Based {
        match self.nodes[i] {
            UnionFindNode::RootWithSize(_) => i,
            UnionFindNode::ChildrenWithParent(parent) => self.get_root_of(parent),
        }
    }

    pub fn get_size_of(&self, i: NodeIndex0Based) -> Quantity {
        match self.nodes[self.get_root_of(i)] {
            UnionFindNode::RootWithSize(size) => size,
            _ => panic!("Illegal condition"),
        }
    }

    /// Union
    pub fn connect_between(&mut self, a: NodeIndex0Based, b: NodeIndex0Based) -> bool {
        let mut a = self.get_root_of(a);
        let mut b = self.get_root_of(b);
        if a == b {
            // already in the same union
            return false;
        }

        if self.get_size_of(a) < self.get_size_of(b) {
            swap!(a, b);
        }

        self.nodes[a] = match self.nodes[a] {
            UnionFindNode::RootWithSize(size) => {
                UnionFindNode::RootWithSize(size + self.get_size_of(b))
            }
            _ => panic!("Illegal condition"),
        };
        self.nodes[b] = UnionFindNode::ChildrenWithParent(a);

        return true;
    }

    pub fn get_roots(&self) -> Vec<NodeIndex0Based> {
        self.nodes
            .iter()
            .enumerate()
            .filter_map(|(i, node)| match *node {
                UnionFindNode::RootWithSize(_) => Some(i),
                UnionFindNode::ChildrenWithParent(_) => None,
            })
            .collect()
    }
}
