#[cfg(test)]
mod tests {
    use templates::snippet_union_find::union_find;
    use test_case::test_case;

    #[test_case(1 => vec![0])]
    #[test_case(2 => vec![0, 1])]
    #[test_case(5 => vec![0, 1, 2, 3, 4])]
    fn check_initial(size: usize) -> Vec<usize> {
        let uf = union_find::new(size);
        uf.get_roots()
    }

    #[test]
    fn connect() {
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

    #[allow(dead_code)]
    fn compiles_with_debug() {
        let uf = union_find::new(5);

        dbg!(uf);
    }
}
