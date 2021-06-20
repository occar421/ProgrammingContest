#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::iter::FromIterator;
    use templates::snippet_union_find::union_find;
    use test_case::test_case;

    #[test_case(1 => vec![0])]
    #[test_case(2 => vec![0, 1])]
    #[test_case(5 => vec![0, 1, 2, 3, 4])]
    fn plain_check_initial(size: usize) -> Vec<usize> {
        let uf = union_find::new(size);
        uf.get_roots()
    }

    #[test]
    fn plain_connect() {
        let mut uf = union_find::new(5);
        uf.connect_between(0, 1);
        uf.connect_between(2, 3);
        uf.connect_between(0, 4);

        assert_eq!(uf.get_root_of(0), uf.get_root_of(1));
        assert_eq!(uf.get_root_of(2), uf.get_root_of(3));
        assert_eq!(uf.get_root_of(0), uf.get_root_of(4));
        assert_eq!(uf.get_root_of(1), uf.get_root_of(4));

        assert_ne!(uf.get_root_of(0), uf.get_root_of(2));
        assert_ne!(uf.get_root_of(3), uf.get_root_of(4));
    }

    #[test_case(vec![0])]
    #[test_case(vec![0, 1])]
    #[test_case(vec![0, 1, 2, 3, 4])]
    fn mapped_check_initial(values: Vec<usize>) {
        let set = HashSet::from_iter(values);
        let uf = union_find::new_from_set(&set);
        dbg!(&set, &uf);
        let ac_set = HashSet::from_iter(uf.get_roots());

        assert_eq!(set, ac_set);
    }

    #[test]
    fn mapped_connect() {
        let data = HashSet::from_iter(vec![-4, -2, 0, 1, 3]);
        let mut uf = union_find::new_from_set(&data);
        uf.connect_between(-4, -2);
        uf.connect_between(0, 1);
        uf.connect_between(-4, 3);

        assert_eq!(uf.get_root_of(-4), uf.get_root_of(-2));
        assert_eq!(uf.get_root_of(0), uf.get_root_of(1));
        assert_eq!(uf.get_root_of(-4), uf.get_root_of(3));
        assert_eq!(uf.get_root_of(-2), uf.get_root_of(3));

        assert_ne!(uf.get_root_of(-4), uf.get_root_of(0));
        assert_ne!(uf.get_root_of(1), uf.get_root_of(3));
    }

    // TODO mapped + &str

    #[allow(dead_code)]
    fn compiles_with_debug() {
        let uf = union_find::new(5);
        dbg!(uf);

        let set = HashSet::from_iter(vec!["a"]);
        let uf = union_find::new_from_set(&set);
        dbg!(uf);
    }
}
