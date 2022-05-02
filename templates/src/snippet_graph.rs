use crate::standard_io::GenericInteger;

pub mod graph {
    //! Graph
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_graph.rs

    use super::GenericInteger;
    use std::collections::HashMap;
    use std::hash::Hash;
    use std::ops::Add;

    pub trait Graph {
        type Node;
        type Cost;

        // TODO: use Iterator instead of Vec
        fn edges_of(&self, node: &Self::Node) -> Option<&Vec<(Self::Node, Self::Cost)>>;
    }

    pub struct StandardGraph<'a, Node, Cost> {
        edges: &'a HashMap<Node, Vec<(Node, Cost)>>,
    }

    impl<'a, Node, Cost> Graph for StandardGraph<'a, Node, Cost>
    where
        Node: Hash + Eq,
    {
        type Node = Node;
        type Cost = Cost;

        fn edges_of(&self, node: &Self::Node) -> Option<&Vec<(Self::Node, Self::Cost)>> {
            self.edges.get(node)
        }
    }

    impl<'a, Node, Cost> StandardGraph<'a, Node, Cost> {
        pub fn new(edges: &'a HashMap<Node, Vec<(Node, Cost)>>) -> Self {
            Self { edges }
        }

        /// Dijkstra
        /// O( (E+V) logV )
        pub fn dijkstra(&self, start_node: Node, initial_cost: Cost) -> dijkstra::Result<Self>
        where
            Node: Clone + Hash + Eq,
            Cost: Clone + Ord + Add<Cost, Output = Cost>,
        {
            let mut result = dijkstra::Result::new(self);
            result.run(start_node, initial_cost);
            result
        }

        /// 01-BFS
        /// O(E+V)
        pub fn x01bfs(&self, start_node: Node) -> x01bfs::Result<Node, Cost>
        where
            Node: Clone + Hash + Eq,
            Cost: GenericInteger,
        {
            let mut result = x01bfs::Result::new(self);
            result.run(start_node);
            result
        }
    }

    pub struct VisitedNodeInfo<Node, Cost> {
        cost: Cost,
        previous_node: Option<Node>,
    }

    pub trait SearchResult<Node, Cost>
    where
        Node: Clone + Hash + Eq,
        Cost: Clone,
    {
        fn visited_nodes(&self) -> &HashMap<Node, VisitedNodeInfo<Node, Cost>>;

        fn cost_to(&self, node: Node) -> Option<Cost> {
            let info = self.visited_nodes().get(&node)?;
            info.cost.clone().into()
        }

        fn path_to(&self, node: Node) -> Option<Vec<Node>> {
            let mut info = self.visited_nodes().get(&node)?;

            let mut v = vec![node.clone()];
            while let Some(prev) = info.previous_node.clone() {
                v.push(prev.clone());
                info = &self.visited_nodes()[&prev]
            }

            v.reverse();
            v.into()
        }
    }

    mod dijkstra {
        use super::{SearchResult, VisitedNodeInfo};
        use std::cmp::Ordering;
        use std::collections::{BinaryHeap, HashMap};
        use std::hash::Hash;
        use std::ops::Add;

        pub struct Result<'a, Graph>
        where
            Graph: super::Graph,
        {
            heap: BinaryHeap<Query<Graph::Node, Graph::Cost>>,
            visited_nodes: HashMap<Graph::Node, VisitedNodeInfo<Graph::Node, Graph::Cost>>,
            graph: &'a Graph,
        }

        impl<'a, Graph> Result<'a, Graph>
        where
            Graph: super::Graph,
            Graph::Node: Clone + Hash + Eq,
            Graph::Cost: Clone + Ord + Add<Graph::Cost, Output = Graph::Cost>,
        {
            pub fn new(graph: &'a Graph) -> Self {
                Self {
                    heap: BinaryHeap::new(),
                    visited_nodes: HashMap::new(),
                    graph,
                }
            }

            pub fn run(&mut self, start_node: Graph::Node, initial_cost: Graph::Cost) {
                self.heap.push(Query {
                    cost: initial_cost,
                    node: start_node,
                    previous_node: None,
                });

                while let Some(Query {
                    cost,
                    node,
                    previous_node,
                }) = self.heap.pop()
                {
                    if self.visited_nodes.contains_key(&node) {
                        continue;
                    }
                    self.visited_nodes.insert(
                        node.clone(),
                        VisitedNodeInfo {
                            cost: cost.clone(),
                            previous_node,
                        },
                    );

                    if let Some(edges) = self.graph.edges_of(&node) {
                        for (dest, move_cost) in edges.iter() {
                            self.heap.push(Query {
                                cost: cost.clone() + move_cost.clone(),
                                node: dest.clone(),
                                previous_node: node.clone().into(),
                            });
                        }
                    }
                }
            }
        }

        impl<'a, Graph> SearchResult<Graph::Node, Graph::Cost> for Result<'a, Graph>
        where
            Graph: super::Graph,
            Graph::Node: Clone + Hash + Eq,
            Graph::Cost: Clone,
        {
            fn visited_nodes(
                &self,
            ) -> &HashMap<Graph::Node, VisitedNodeInfo<Graph::Node, Graph::Cost>> {
                &self.visited_nodes
            }
        }

        pub struct Query<Node, Cost> {
            cost: Cost,
            node: Node,
            previous_node: Option<Node>,
        }

        impl<Node, Cost> PartialEq for Query<Node, Cost>
        where
            Cost: PartialEq,
        {
            fn eq(&self, other: &Self) -> bool {
                self.cost.eq(&other.cost)
            }
        }

        impl<Node, Cost> PartialOrd for Query<Node, Cost>
        where
            Cost: Ord + PartialEq,
        {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.cmp(&other).into()
            }
        }

        impl<Node, Cost> Eq for Query<Node, Cost> where Cost: PartialEq {}

        impl<Node, Cost> Ord for Query<Node, Cost>
        where
            Cost: Ord + PartialEq,
        {
            fn cmp(&self, other: &Self) -> Ordering {
                self.cost.cmp(&other.cost).reverse() // ascending
            }
        }
    }

    mod x01bfs {
        use super::super::GenericInteger;
        use super::{SearchResult, StandardGraph, VisitedNodeInfo};
        use std::collections::{HashMap, VecDeque};
        use std::hash::Hash;

        pub struct Result<'a, Node, Cost> {
            deque: VecDeque<Query<Node, Cost>>,
            visited_nodes: HashMap<Node, VisitedNodeInfo<Node, Cost>>,
            graph: &'a StandardGraph<'a, Node, Cost>,
        }

        impl<'a, Node, Cost> Result<'a, Node, Cost>
        where
            Node: Clone + Hash + Eq,
            Cost: GenericInteger,
        {
            pub fn new(graph: &'a StandardGraph<'a, Node, Cost>) -> Self {
                Self {
                    deque: VecDeque::new(),
                    visited_nodes: HashMap::new(),
                    graph,
                }
            }

            pub fn run(&mut self, start_node: Node) {
                self.deque.push_front(Query {
                    cost: Cost::zero(),
                    node: start_node,
                    previous_node: None,
                });

                while let Some(Query {
                    cost,
                    node,
                    previous_node,
                }) = self.deque.pop_front()
                {
                    if self.visited_nodes.contains_key(&node) {
                        continue;
                    }
                    self.visited_nodes.insert(
                        node.clone(),
                        VisitedNodeInfo {
                            cost,
                            previous_node,
                        },
                    );

                    if let Some(edges) = self.graph.edges.get(&node) {
                        for (dest, move_cost) in edges.iter() {
                            if *move_cost == Cost::zero() {
                                self.deque.push_front(Query {
                                    cost,
                                    node: dest.clone(),
                                    previous_node: node.clone().into(),
                                });
                            } else if *move_cost == Cost::one() {
                                self.deque.push_back(Query {
                                    cost: cost + Cost::one(),
                                    node: dest.clone(),
                                    previous_node: node.clone().into(),
                                });
                            } else {
                                panic!("Non 0/1 cost found.");
                            }
                        }
                    }
                }
            }
        }

        impl<'a, Node, Cost> SearchResult<Node, Cost> for Result<'a, Node, Cost>
        where
            Node: Clone + Hash + Eq,
            Cost: Clone,
        {
            fn visited_nodes(&self) -> &HashMap<Node, VisitedNodeInfo<Node, Cost>> {
                &self.visited_nodes
            }
        }

        pub struct Query<Node, Cost> {
            cost: Cost,
            node: Node,
            previous_node: Option<Node>,
        }
    }
}
