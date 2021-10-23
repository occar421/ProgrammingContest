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
        use std::iter::FromIterator;
        use templates::snippet_union_find::union_find::UnionFindSet;

        #[test]
        fn connect_isize() {
            let mut ufs = UnionFindSet::from_iter(vec![-4, -2, 0, 1, 3]);
            ufs.connect_between(-4, -2);
            ufs.connect_between(0, &1);
            ufs.connect_between(&-4, &3);

            assert_eq!(ufs.get_root_of(-4), ufs.get_root_of(-2));
            assert_eq!(ufs.get_root_of(0), ufs.get_root_of(1));
            assert_eq!(ufs.get_root_of(&-4), ufs.get_root_of(&3));
            assert_eq!(ufs.get_root_of(&-2), ufs.get_root_of(&3));

            assert_ne!(ufs.get_root_of(-4), ufs.get_root_of(0));
            assert_ne!(ufs.get_root_of(&1), ufs.get_root_of(&3));
        }

        #[test]
        fn connect_string() {
            let mut ufs = UnionFindSet::from_iter(vec!["foo", "bar", "baz", "qux", "quux"]);
            ufs.connect_between("foo", "bar");
            ufs.connect_between("baz", &"qux");
            ufs.connect_between(&"foo", &"quux");

            assert_eq!(ufs.get_root_of("foo"), ufs.get_root_of("bar"));
            assert_eq!(ufs.get_root_of("baz"), ufs.get_root_of("qux"));
            assert_eq!(ufs.get_root_of(&"foo"), ufs.get_root_of(&"quux"));
            assert_eq!(ufs.get_root_of(&"bar"), ufs.get_root_of(&"quux"));

            assert_ne!(ufs.get_root_of("foo"), ufs.get_root_of("baz"));
            assert_ne!(ufs.get_root_of(&"qux"), ufs.get_root_of(&"quux"));
        }

        #[allow(dead_code)]
        fn compiles_with_debug() {
            let ufs = UnionFindSet::from_iter(0..5);
            dbg!(ufs);

            let ufs = UnionFindSet::from_iter(vec!["a"]);
            dbg!(ufs);
        }
    }
}
