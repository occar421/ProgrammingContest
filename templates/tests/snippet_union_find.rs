#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::iter::FromIterator;
    use templates::snippet_union_find::union_find::UnionFind;
    use test_case::test_case;
    
    #[test_case(vec ! [0])]
    #[test_case(vec ! [0, 1])]
    #[test_case(vec ! [0, 1, 2, 3, 4])]
    fn check_initial(values: Vec<usize>) {
        let set = HashSet::from_iter(values);
        let uf = UnionFind::from_set(&set);
        let ac_set = HashSet::from_iter(uf.get_roots().copied());

        assert_eq!(set, ac_set);
    }

    #[test]
    fn connect_isize() {
        let data = HashSet::from_iter(vec![-4, -2, 0, 1, 3]);
        let mut uf = UnionFind::from_set(&data);
        uf.connect_between(-4, -2);
        uf.connect_between(0, &1);
        uf.connect_between(&-4, &3);

        assert_eq!(uf.get_root_of(-4), uf.get_root_of(-2));
        assert_eq!(uf.get_root_of(0), uf.get_root_of(1));
        assert_eq!(uf.get_root_of(&-4), uf.get_root_of(&3));
        assert_eq!(uf.get_root_of(&-2), uf.get_root_of(&3));

        assert_ne!(uf.get_root_of(-4), uf.get_root_of(0));
        assert_ne!(uf.get_root_of(&1), uf.get_root_of(&3));
    }

    #[test]
    fn connect_string() {
        // let data = HashSet::from_iter(
        //     vec!["foo", "bar", "baz", "qux", "quux"]
        //         .iter()
        //         .map(|s| s.to_string()),
        // );
        let data = HashSet::from_iter(vec!["foo", "bar", "baz", "qux", "quux"]);

        let mut uf = UnionFind::from_set(&data);
        uf.connect_between("foo", "bar");
        uf.connect_between("baz", &"qux");
        uf.connect_between(&"foo", &"quux");

        assert_eq!(uf.get_root_of("foo"), uf.get_root_of("bar"));
        assert_eq!(uf.get_root_of("baz"), uf.get_root_of("qux"));
        assert_eq!(uf.get_root_of(&"foo"), uf.get_root_of(&"quux"));
        assert_eq!(uf.get_root_of(&"bar"), uf.get_root_of(&"quux"));

        assert_ne!(uf.get_root_of("foo"), uf.get_root_of("baz"));
        assert_ne!(uf.get_root_of(&"qux"), uf.get_root_of(&"quux"));
    }

    #[allow(dead_code)]
    fn compiles_with_debug() {
        let set = HashSet::from_iter(0..5);
        let uf = UnionFind::from_set(&set);
        dbg!(uf);

        let set = HashSet::from_iter(vec!["a"]);
        let uf = UnionFind::from_set(&set);
        dbg!(uf);
    }
}
