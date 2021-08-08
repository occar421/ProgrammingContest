#[cfg(test)]
mod tests {

    mod dijkstra {
        use std::collections::HashMap;
        use templates::snippet_graph::graph::{Graph, SearchResult};

        #[test]
        fn cost_int() {
            let mut edges = HashMap::new();
            edges.entry(0).or_insert(vec![]).push((1, 2));

            let graph = Graph::new(&edges);
            let d = graph.dijkstra(0, 0);
            assert_eq!(d.cost_to(0), Some(0));
            assert_eq!(d.cost_to(1), Some(2));
            assert_eq!(d.cost_to(2), None);
        }

        #[test]
        fn tuple() {
            let mut edges = HashMap::new();
            edges.entry((0, 'a')).or_insert(vec![]).push(((0, 'b'), 2));

            let graph = Graph::new(&edges);
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

            let mut edges = HashMap::new();
            edges
                .entry(p(0, 'a'))
                .or_insert(vec![])
                .push((p(0, 'b'), 2));

            let graph = Graph::new(&edges);
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
            let mut edges = HashMap::new();
            edges.entry(&p_0a).or_insert(vec![]).push((&p_0b, 2));

            let graph = Graph::new(&edges);
            let d = graph.dijkstra(&p_0a, 0);
            assert_eq!(d.cost_to(&p_0a), Some(0));
            assert_eq!(d.cost_to(&p_0b), Some(2));
            assert_eq!(d.cost_to(&p_1a), None);
        }

        #[test]
        fn path_int() {
            let mut edges = HashMap::new();
            edges.entry(0).or_insert(vec![]).push((1, 2));

            let graph = Graph::new(&edges);
            let d = graph.dijkstra(0, 0);
            assert_eq!(d.path_to(0).unwrap()[0], 0);
            assert_eq!(d.path_to(1).unwrap()[0], 0);
            assert_eq!(d.path_to(1).unwrap()[1], 1);
            assert_eq!(d.path_to(2), None);
        }
    }

    mod x01bfs {
        use std::collections::HashMap;
        use templates::snippet_graph::graph::{Graph, SearchResult};

        #[test]
        fn cost_int() {
            let mut edges = HashMap::new();
            edges.entry(0).or_insert(vec![]).push((1, 1));

            let graph = Graph::new(&edges);
            let d = graph.x01bfs(0);
            assert_eq!(d.cost_to(0), Some(0));
            assert_eq!(d.cost_to(1), Some(1));
            assert_eq!(d.cost_to(2), None);
        }

        #[test]
        fn tuple() {
            let mut edges = HashMap::new();
            edges.entry((0, 'a')).or_insert(vec![]).push(((0, 'b'), 1));

            let graph = Graph::new(&edges);
            let d = graph.x01bfs((0, 'a'));
            assert_eq!(d.cost_to((0, 'a')), Some(0));
            assert_eq!(d.cost_to((0, 'b')), Some(1));
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

            let mut edges = HashMap::new();
            edges
                .entry(p(0, 'a'))
                .or_insert(vec![])
                .push((p(0, 'b'), 1));

            let graph = Graph::new(&edges);
            let d = graph.x01bfs(p(0, 'a'));
            assert_eq!(d.cost_to(p(0, 'a')), Some(0));
            assert_eq!(d.cost_to(p(0, 'b')), Some(1));
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
            let mut edges = HashMap::new();
            edges.entry(&p_0a).or_insert(vec![]).push((&p_0b, 1));

            let graph = Graph::new(&edges);
            let d = graph.x01bfs(&p_0a);
            assert_eq!(d.cost_to(&p_0a), Some(0));
            assert_eq!(d.cost_to(&p_0b), Some(1));
            assert_eq!(d.cost_to(&p_1a), None);
        }

        #[test]
        fn path_int() {
            let mut edges = HashMap::new();
            edges.entry(0).or_insert(vec![]).push((1, 1));

            let graph = Graph::new(&edges);
            let d = graph.x01bfs(0);
            assert_eq!(d.path_to(0).unwrap()[0], 0);
            assert_eq!(d.path_to(1).unwrap()[0], 0);
            assert_eq!(d.path_to(1).unwrap()[1], 1);
            assert_eq!(d.path_to(2), None);
        }
    }
}
