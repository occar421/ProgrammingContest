#[cfg(test)]
mod tests {

    mod dijkstra {
        use std::collections::{HashMap, HashSet};
        use std::iter::FromIterator;
        use templates::snippet_graph::graph::Graph;

        #[test]
        fn int() {
            let nodes = HashSet::from_iter(vec![0, 1, 2]);
            let mut edges = HashMap::new();
            edges.entry(0).or_insert(vec![]).push((1, 2));

            let graph = Graph::new(&nodes, &edges);
            let d = graph.dijkstra(0, 0);
            assert_eq!(d.cost_to(0), Some(0));
            assert_eq!(d.cost_to(1), Some(2));
            assert_eq!(d.cost_to(2), None);
        }

        #[test]
        fn tuple() {
            let nodes = HashSet::from_iter(vec![(0, 'a'), (0, 'b'), (1, 'a')]);
            let mut edges = HashMap::new();
            edges.entry((0, 'a')).or_insert(vec![]).push(((0, 'b'), 2));

            let graph = Graph::new(&nodes, &edges);
            let d = graph.dijkstra((0, 'a'), 0);
            assert_eq!(d.cost_to((0, 'a')), Some(0));
            assert_eq!(d.cost_to((0, 'b')), Some(2));
            assert_eq!(d.cost_to((1, 'a')), None);
        }

        // TODO struct

        // TODO complex
    }
}
