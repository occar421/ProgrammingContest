#[cfg(test)]
mod tests {

    mod dijkstra {
        use std::collections::{HashMap, HashSet};
        use std::iter::FromIterator;
        use templates::snippet_graph::graph::Graph;

        #[test]
        fn cost_int() {
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

        #[test]
        fn user_defined_struct() {
            #[derive(Eq, PartialEq, Hash, Clone)]
            struct P {
                n: usize,
                c: char,
            }
            fn p(n: usize, c: char) -> P {
                P { n, c }
            }

            let nodes = HashSet::from_iter(vec![p(0, 'a'), p(0, 'b'), p(1, 'a')]);
            let mut edges = HashMap::new();
            edges
                .entry(p(0, 'a'))
                .or_insert(vec![])
                .push((p(0, 'b'), 2));

            let graph = Graph::new(&nodes, &edges);
            let d = graph.dijkstra(p(0, 'a'), 0);
            assert_eq!(d.cost_to(p(0, 'a')), Some(0));
            assert_eq!(d.cost_to(p(0, 'b')), Some(2));
            assert_eq!(d.cost_to(p(1, 'a')), None);
        }

        #[test]
        fn user_defined_struct_ref() {
            #[derive(Eq, PartialEq, Hash, Clone)]
            struct P {
                n: usize,
                c: char,
            }

            let p_0a = P { n: 0, c: 'a' };
            let p_0b = P { n: 0, c: 'b' };
            let p_1a = P { n: 1, c: 'a' };
            let nodes = HashSet::from_iter(vec![&p_0a, &p_0b, &p_1a]);
            let mut edges = HashMap::new();
            edges.entry(&p_0a).or_insert(vec![]).push((&p_0b, 2));

            let graph = Graph::new(&nodes, &edges);
            let d = graph.dijkstra(&p_0a, 0);
            assert_eq!(d.cost_to(&p_0a), Some(0));
            assert_eq!(d.cost_to(&p_0b), Some(2));
            assert_eq!(d.cost_to(&p_1a), None);
        }

        #[test]
        fn path_int() {
            let nodes = HashSet::from_iter(vec![0, 1, 2]);
            let mut edges = HashMap::new();
            edges.entry(0).or_insert(vec![]).push((1, 2));

            let graph = Graph::new(&nodes, &edges);
            let d = graph.dijkstra(0, 0);
            assert_eq!(d.path_to(0).unwrap()[0], 0);
            assert_eq!(d.path_to(1).unwrap()[0], 0);
            assert_eq!(d.path_to(1).unwrap()[1], 1);
            assert_eq!(d.path_to(2), None);
        }
    }
}
