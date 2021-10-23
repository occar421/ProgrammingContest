#[cfg(test)]
mod tests {
    mod map {
        use std::iter::FromIterator;
        use templates::snippet_union_find::union_find::UnionFindMap;

        #[test]
        fn connect_usize_multiple() {
            let mut ufm =
                UnionFindMap::from_iter(vec![2usize, 3, 5, 7, 11].iter().map(|&x| (x, x)));

            assert_eq!(ufm.get_root_of(2).unwrap().1, &2);
            assert_eq!(ufm.get_root_of(3).unwrap().1, &3);
            assert_eq!(ufm.get_root_of(5).unwrap().1, &5);
            assert_eq!(ufm.get_root_of(7).unwrap().1, &7);
            assert_eq!(ufm.get_root_of(11).unwrap().1, &11);

            ufm.connect_between(2, 3, |a, b| a * b);

            assert_eq!(ufm.get_root_of(2).unwrap().1, &6);
            assert_eq!(ufm.get_root_of(3).unwrap().1, &6);
            assert_eq!(ufm.get_root_of(5).unwrap().1, &5);
            assert_eq!(ufm.get_root_of(7).unwrap().1, &7);
            assert_eq!(ufm.get_root_of(11).unwrap().1, &11);

            ufm.connect_between(5, &7, |a, b| a * b);

            assert_eq!(ufm.get_root_of(2).unwrap().1, &6);
            assert_eq!(ufm.get_root_of(3).unwrap().1, &6);
            assert_eq!(ufm.get_root_of(5).unwrap().1, &35);
            assert_eq!(ufm.get_root_of(7).unwrap().1, &35);
            assert_eq!(ufm.get_root_of(11).unwrap().1, &11);

            ufm.connect_between(&5, &11, |a, b| a * b);

            assert_eq!(ufm.get_root_of(2).unwrap().1, &6);
            assert_eq!(ufm.get_root_of(3).unwrap().1, &6);
            assert_eq!(ufm.get_root_of(5).unwrap().1, &385);
            assert_eq!(ufm.get_root_of(7).unwrap().1, &385);
            assert_eq!(ufm.get_root_of(11).unwrap().1, &385);
        }

        #[test]
        fn connect_usize_vec() {
            let mut ufm = UnionFindMap::from_iter(
                vec![vec![11usize, 12], vec![21, 22], vec![31, 32]]
                    .into_iter()
                    .enumerate(),
            );

            assert_eq!(ufm.get_root_of(0).unwrap().1, &vec![11, 12]);
            assert_eq!(ufm.get_root_of(1).unwrap().1, &vec![21, 22]);
            assert_eq!(ufm.get_root_of(2).unwrap().1, &vec![31, 32]);

            ufm.connect_between(0, 1, |mut a, mut b| {
                a.append(&mut b);
                a
            });

            assert_eq!(ufm.get_root_of(0).unwrap().1, &vec![11, 12, 21, 22]);
            assert_eq!(ufm.get_root_of(1).unwrap().1, &vec![11, 12, 21, 22]);
            assert_eq!(ufm.get_root_of(2).unwrap().1, &vec![31, 32]);

            ufm.connect_between(2, 1, |mut a, mut b| {
                a.append(&mut b);
                a
            });

            assert_eq!(ufm.get_root_of(0).unwrap().1, &vec![31, 32, 11, 12, 21, 22]);
            assert_eq!(ufm.get_root_of(1).unwrap().1, &vec![31, 32, 11, 12, 21, 22]);
            assert_eq!(ufm.get_root_of(2).unwrap().1, &vec![31, 32, 11, 12, 21, 22]);
        }

        #[allow(dead_code)]
        fn compiles_with_debug() {
            let ufm = UnionFindMap::from_iter((0..5).into_iter().map(|x| (x, x)));
            dbg!(ufm);

            let ufm = UnionFindMap::from_iter(vec![(0, "a")]);
            dbg!(ufm);
        }
    }

    mod set {
        // use std::collections::{HashMap, HashSet};
        // use std::iter::FromIterator;
        // use templates::snippet_union_find::union_find::UnionFindMap;
        // use test_case::test_case;
        //
        // #[test_case(vec ! [0])]
        // #[test_case(vec ! [0, 1])]
        // #[test_case(vec ! [0, 1, 2, 3, 4])]
        // fn check_initial(values: Vec<usize>) {
        //     let set = HashSet::from_iter(values);
        //     let uf = UnionFindMap::from_set(&set);
        //     let ac_set = HashSet::from_iter(uf.get_roots().copied());
        //
        //     assert_eq!(set, ac_set);
        // }
        //
        // #[test]
        // fn connect_isize() {
        //     let data = HashSet::from_iter(vec![-4, -2, 0, 1, 3]);
        //     let mut uf = UnionFindMap::from_set(&data);
        //     uf.connect_between(-4, -2);
        //     uf.connect_between(0, &1);
        //     uf.connect_between(&-4, &3);
        //
        //     assert_eq!(uf.get_root_of(-4), uf.get_root_of(-2));
        //     assert_eq!(uf.get_root_of(0), uf.get_root_of(1));
        //     assert_eq!(uf.get_root_of(&-4), uf.get_root_of(&3));
        //     assert_eq!(uf.get_root_of(&-2), uf.get_root_of(&3));
        //
        //     assert_ne!(uf.get_root_of(-4), uf.get_root_of(0));
        //     assert_ne!(uf.get_root_of(&1), uf.get_root_of(&3));
        // }
        //
        // #[test]
        // fn connect_string() {
        //     // let data = HashSet::from_iter(
        //     //     vec!["foo", "bar", "baz", "qux", "quux"]
        //     //         .iter()
        //     //         .map(|s| s.to_string()),
        //     // );
        //     let data = HashSet::from_iter(vec!["foo", "bar", "baz", "qux", "quux"]);
        //
        //     let mut uf = UnionFindMap::from_set(&data);
        //     uf.connect_between("foo", "bar");
        //     uf.connect_between("baz", &"qux");
        //     uf.connect_between(&"foo", &"quux");
        //
        //     assert_eq!(uf.get_root_of("foo"), uf.get_root_of("bar"));
        //     assert_eq!(uf.get_root_of("baz"), uf.get_root_of("qux"));
        //     assert_eq!(uf.get_root_of(&"foo"), uf.get_root_of(&"quux"));
        //     assert_eq!(uf.get_root_of(&"bar"), uf.get_root_of(&"quux"));
        //
        //     assert_ne!(uf.get_root_of("foo"), uf.get_root_of("baz"));
        //     assert_ne!(uf.get_root_of(&"qux"), uf.get_root_of(&"quux"));
        // }
        //
        // #[allow(dead_code)]
        // fn compiles_with_debug() {
        //     let set = HashSet::from_iter(0..5);
        //     let uf = UnionFindMap::from_set(&set);
        //     dbg!(uf);
        //
        //     let set = HashSet::from_iter(vec!["a"]);
        //     let uf = UnionFindMap::from_set(&set);
        //     dbg!(uf);
        // }
    }
}
