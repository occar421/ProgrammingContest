pub mod graph {
    //! Graph
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_graph.rs

    use std::collections::{HashMap, HashSet};
    use std::hash::Hash;
    use std::ops::Add;

    pub struct Graph<'a, Node, Cost> {
        nodes: &'a HashSet<Node>,
        edges: &'a HashMap<Node, Vec<(Node, Cost)>>,
    }

    impl<'a, Node, Cost> Graph<'a, Node, Cost> {
        pub fn new(nodes: &'a HashSet<Node>, edges: &'a HashMap<Node, Vec<(Node, Cost)>>) -> Self {
            Self { nodes, edges }
        }

        pub fn dijkstra(
            &self,
            start_node: Node,
            initial_cost: Cost,
        ) -> dijkstra::Dijkstra<Node, Cost>
        where
            Node: Clone + Hash + Eq,
            Cost: Clone + Ord + Add<Cost, Output = Cost>,
        {
            let mut memo = dijkstra::Dijkstra::new(self);
            memo.run(start_node, initial_cost);
            memo
        }
    }

    mod dijkstra {
        use super::Graph;
        use std::cmp::Ordering;
        use std::collections::{BinaryHeap, HashMap};
        use std::hash::Hash;
        use std::ops::Add;

        struct VisitedNodeInfo<Node, Cost> {
            cost: Cost,
            previous_node: Option<Node>,
        }

        pub struct Dijkstra<'a, Node, Cost> {
            heap: BinaryHeap<DijkstraQuery<Node, Cost>>,
            visited_nodes: HashMap<Node, VisitedNodeInfo<Node, Cost>>,
            graph: &'a Graph<'a, Node, Cost>,
        }

        impl<'a, Node, Cost> Dijkstra<'a, Node, Cost>
        where
            Node: Clone + Hash + Eq,
            Cost: Clone + Ord + Add<Cost, Output = Cost>,
        {
            pub fn new(graph: &'a Graph<'a, Node, Cost>) -> Self {
                Self {
                    heap: BinaryHeap::new(),
                    visited_nodes: HashMap::new(),
                    graph,
                }
            }

            pub fn run(&mut self, start_node: Node, initial_cost: Cost) {
                self.heap.push(DijkstraQuery {
                    cost: initial_cost,
                    node: start_node,
                    previous_node: None,
                });

                while let Some(DijkstraQuery {
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

                    if let Some(edges) = self.graph.edges.get(&node) {
                        for (dest, move_cost) in edges.iter() {
                            self.heap.push(DijkstraQuery {
                                cost: cost.clone() + move_cost.clone(),
                                node: dest.clone(),
                                previous_node: node.clone().into(),
                            });
                        }
                    }
                }
            }

            pub fn cost_to(&self, node: Node) -> Option<Cost> {
                let info = self.visited_nodes.get(&node)?;
                info.cost.clone().into()
            }

            pub fn path_to(&self, node: Node) -> Option<Vec<Node>> {
                let mut info = self.visited_nodes.get(&node)?;

                let mut v = vec![node.clone()];
                while let Some(prev) = info.previous_node.clone() {
                    v.push(prev.clone());
                    info = &self.visited_nodes[&prev]
                }

                v.reverse();
                v.into()
            }
        }

        pub struct DijkstraQuery<Node, Cost> {
            cost: Cost,
            node: Node,
            previous_node: Option<Node>,
        }

        impl<Node, Cost> PartialEq for DijkstraQuery<Node, Cost>
        where
            Cost: PartialEq,
        {
            fn eq(&self, other: &Self) -> bool {
                self.cost.eq(&other.cost)
            }
        }

        impl<Node, Cost> PartialOrd for DijkstraQuery<Node, Cost>
        where
            Cost: Ord,
        {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.cmp(&other).into()
            }
        }

        impl<Node, Cost> Eq for DijkstraQuery<Node, Cost> where Cost: PartialEq {}

        impl<Node, Cost> Ord for DijkstraQuery<Node, Cost>
        where
            Cost: Ord,
        {
            fn cmp(&self, other: &Self) -> Ordering {
                self.cost.cmp(&other.cost).reverse() // ascending
            }
        }
    }
}
