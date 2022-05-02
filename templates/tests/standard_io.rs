#[cfg(test)]
mod tests {
    use std::iter::FromIterator;
    use templates::standard_io::IterExt;
    use test_case::test_case;

    mod integer {
        use templates::standard_io::GenericInteger;
        use test_case::test_case;

        #[test_case(1, 1 => 1)]
        #[test_case(2, 1 => 1)]
        #[test_case(1, 2 => 1)]
        #[test_case(2, 2 => 2)]
        #[test_case(12, 2 => 2)]
        #[test_case(3, 5 => 1)]
        #[test_case(12, 8 => 4)]
        fn gcd(a: usize, b: usize) -> usize {
            templates::standard_io::gcd(a, b)
        }

        #[test_case(1, 1 => 1)]
        #[test_case(2, 1 => 2)]
        #[test_case(1, 2 => 2)]
        #[test_case(2, 2 => 2)]
        #[test_case(12, 2 => 12)]
        #[test_case(3, 5 => 15)]
        #[test_case(12, 8 => 24)]
        fn lcm(a: usize, b: usize) -> usize {
            templates::standard_io::lcm(a, b)
        }

        #[test_case(0 => (false, true))]
        #[test_case(1 => (true, false))]
        #[test_case(123 => (true, false))]
        #[test_case(1234 => (false, true))]
        fn odd_even(value: usize) -> (bool, bool) {
            (value.is_odd(), value.is_even())
        }
    }

    #[test_case(vec ! [], " " => "")]
    #[test_case(vec ! [1], " " => "1")]
    #[test_case(vec ! [1, 2], " " => "1 2")]
    #[test_case(vec ! [3, 4], "," => "3,4")]
    #[test_case(vec ! [5, 6, 7], "," => "5,6,7")]
    #[test_case(vec ! [8, 9, 0], ", " => "8, 9, 0")]
    #[test_case(vec ! [1, 2, 3, 4], "" => "1234")]
    fn easy_join_with_number(vec: Vec<usize>, separator: &str) -> String {
        vec.iter().join_as_string(separator)
    }

    #[test_case(vec ! [], " " => "")]
    #[test_case(vec ! ["a"], " " => "a")]
    #[test_case(vec ! ["b", "c"], " " => "b c")]
    #[test_case(vec ! ["d", "e"], "," => "d,e")]
    #[test_case(vec ! ["f", "g", "h"], "," => "f,g,h")]
    #[test_case(vec ! ["i", "j", "k"], ", " => "i, j, k")]
    #[test_case(vec ! ["lm", "no", "pq"], "," => "lm,no,pq")]
    #[test_case(vec ! ["r", "u", "s", "t"], "" => "rust")]
    fn easy_join_with_string(vec: Vec<&str>, separator: &str) -> String {
        vec.iter().join_as_string(separator)
    }

    #[test]
    fn group_with() {
        let data = vec![1, 1, 2, 2, 3];
        let result = data.into_iter().group_with();
        assert_eq!(result.len(), 3);
        assert_eq!(result[&1], vec![1, 1]);
        assert_eq!(result[&2], vec![2, 2]);
        assert_eq!(result[&3], vec![3]);
    }

    #[test]
    fn group_with_key() {
        let data = vec![1, 1, 2, 2, 3];
        let result = data.into_iter().group_with_key(|&x| x > 1);
        assert_eq!(result.len(), 2);
        assert_eq!(result[&true], vec![2, 2, 3]);
        assert_eq!(result[&false], vec![1, 1]);
    }

    #[test]
    fn invert_index() {
        use templates::invert_index;
        let a = vec![1, 2, 0, 4, 3];

        let b = invert_index!(a);

        assert_eq!(a, invert_index!(b));
    }

    #[test_case(1 => Vec::<(usize, usize)>::new())]
    #[test_case(2 => vec![(2,1)])]
    #[test_case(3 => vec![(3,1)])]
    #[test_case(12 => vec![(2,2),(3,1)])]
    #[test_case(600 => vec![(2,3),(3,1),(5,2)])]
    fn prime_factorize(n: usize) -> Vec<(usize, usize)> {
        let result = templates::standard_io::prime_factorize(n);
        let mut pairs: Vec<_> = result.iter().collect();
        pairs.sort_by_key(|(key, _)| *key);
        pairs.iter().map(|(key, value)| (**key, **value)).collect()
    }

    #[test_case(1 => vec![1])]
    #[test_case(2 => vec![1, 2])]
    #[test_case(3 => vec![1, 3])]
    #[test_case(4 => vec![1, 2, 4])]
    #[test_case(5 => vec![1, 5])]
    #[test_case(6 => vec![1, 2, 3, 6])]
    #[test_case(8 => vec![1, 2, 4, 8])]
    #[test_case(12 => vec![1, 2, 3, 4, 6, 12])]
    fn divisors_of(n: usize) -> Vec<usize> {
        let result = templates::standard_io::divisors_of(n);
        let mut result = Vec::from_iter(result);
        result.sort_unstable();
        result
    }

    #[test_case(0 => Vec::<usize>::new())]
    #[test_case(1 => Vec::<usize>::new())]
    #[test_case(2 => vec![2])]
    #[test_case(3 => vec![2, 3])]
    #[test_case(6 => vec![2, 3, 5])]
    #[test_case(7 => vec![2, 3, 5, 7])]
    #[test_case(8 => vec![2, 3, 5, 7])]
    #[test_case(20 => vec![2, 3, 5, 7, 11, 13, 17, 19])]
    #[test_case(100 => vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97])]
    fn eratosthenes_sieve(n: usize) -> Vec<usize> {
        templates::standard_io::eratosthenes_sieve(n)
    }

    mod collection_util {
        #[test]
        fn min() {
            use templates::standard_io::{min_with_partial, Min, PartialMin};
            use templates::{min, partial_min};

            assert_eq!(min!(2), 2);
            assert_eq!(min!(2, 3), 2);
            assert_eq!(min!(3, 2, 7, 5), 2);

            let empty: Vec<i32> = vec![];
            let none: Option<i32> = None;

            assert_eq!(partial_min!(3, vec![2, 7], 5), Some(2));
            assert_eq!(partial_min!(empty.clone()), None);
            assert_eq!(partial_min!(vec![empty.clone(), empty.clone()]), None);
            assert_eq!(partial_min!(vec![3, 2, 7, 5]), Some(2));
            assert_eq!(partial_min!(vec![vec![3, 2], vec![7, 5]]), Some(2));
            assert_eq!(
                partial_min!(vec![vec![vec![3], vec![2]], vec![vec![7], vec![5]]]),
                Some(2)
            );

            assert_eq!(partial_min!(3, none, 2, empty.clone(), 5, none, 7), Some(2));
        }

        #[test]
        fn max() {
            use templates::standard_io::{max_with_partial, Max, PartialMax};
            use templates::{max, partial_max};

            assert_eq!(max!(2), 2);
            assert_eq!(max!(2, 3), 3);
            assert_eq!(max!(3, 2, 7, 5), 7);

            let empty: Vec<i32> = vec![];
            let none: Option<i32> = None;

            assert_eq!(partial_max!(3, vec![2, 7], 5), Some(7));
            assert_eq!(partial_max!(empty.clone()), None);
            assert_eq!(partial_max!(vec![empty.clone(), empty.clone()]), None);
            assert_eq!(partial_max!(vec![3, 2, 7, 5]), Some(7));
            assert_eq!(partial_max!(vec![vec![3, 2], vec![7, 5]]), Some(7));
            assert_eq!(
                partial_max!(vec![vec![vec![3], vec![2]], vec![vec![7], vec![5]]]),
                Some(7)
            );

            assert_eq!(partial_max!(3, none, 2, empty.clone(), 7, none, 5), Some(7));
        }

        #[test]
        fn auto_sum() {
            use templates::standard_io::AutoSum;
            use templates::sum;

            assert_eq!(sum!(2), 2);
            assert_eq!(sum!(2, 3), 5);

            let empty: Vec<i32> = vec![];
            let none: Option<i32> = None;

            assert_eq!(sum!(empty.clone()), 0);
            assert_eq!(sum!(none), 0);
            assert_eq!(sum!(vec![1]), 1);
            assert_eq!(sum!(vec![1, 3, 5]), 9);
            assert_eq!(sum!(vec![1, 3, 5], 7), 16);
            assert_eq!(sum!(vec![vec![1], vec![3]]), 4);
        }

        #[test]
        fn auto_product() {
            use templates::product;
            use templates::standard_io::AutoProduct;

            assert_eq!(product!(2), 2);
            assert_eq!(product!(2, 3), 6);

            let empty: Vec<i32> = vec![];
            let none: Option<i32> = None;

            assert_eq!(product!(empty.clone()), 1);
            assert_eq!(product!(none), 1);
            assert_eq!(product!(vec![2]), 2);
            assert_eq!(product!(vec![2, 3, 5]), 30);
            assert_eq!(product!(vec![2, 3, 5], 7), 210);
            assert_eq!(product!(vec![vec![2], vec![3]]), 6);
        }
    }

    #[test_case('A', 0 => 'A')]
    #[test_case('A', 1 => 'B')]
    #[test_case('A', 2 => 'C')]
    #[test_case('A', 25 => 'Z')]
    #[test_case('a', 24 => 'y')]
    fn index_to_ascii(base: char, index: usize) -> char {
        let gen = templates::standard_io::index_to_ascii_gen(base);
        gen(index)
    }

    #[test_case('A', 'A' => 0)]
    #[test_case('A', 'B' => 1)]
    #[test_case('A', 'C' => 2)]
    #[test_case('A', 'Z' => 25)]
    #[test_case('a', 'y' => 24)]
    fn ascii_to_index(base: char, ascii: char) -> usize {
        let gen = templates::standard_io::ascii_to_index_gen(base);
        gen(ascii)
    }

    mod point2d {
        use test_case::test_case;

        #[test_case(0.0, 0.0, 0.0)]
        #[test_case(1.0, 0.0, 1.0)]
        #[test_case(0.0, 1.0, 1.0)]
        #[test_case(3.0, 4.0, 5.0)]
        #[test_case(5.0, 12.0, 13.0)]
        fn length(x: f64, y: f64, r: f64) {
            let p = templates::standard_io::Point2d { x, y };
            templates::assert_eq_with_error!(p.length(), r, 10f64.powi(-6));
        }
    }

    #[test_case(1, 0 => panics)]
    #[test_case(0, 1 => 0)]
    #[test_case(1, 1 => 1)]
    #[test_case(0, 2 => 0)]
    #[test_case(1, 2 => 1)]
    #[test_case(2, 2 => 1)]
    #[test_case(3, 2 => 2)]
    #[test_case(4, 2 => 2)]
    fn div_ceil_usize(a: usize, b: usize) -> usize {
        templates::standard_io::div_ceil(a, b)
    }

    mod div_ceil_isize {
        use test_case::test_case;

        #[test_case(1, 0 => panics)]
        #[test_case(0, 1 => 0)]
        #[test_case(1, 1 => 1)]
        #[test_case(0, 2 => 0)]
        #[test_case(1, 2 => 1)]
        #[test_case(2, 2 => 1)]
        #[test_case(3, 2 => 2)]
        #[test_case(4, 2 => 2)]
        fn pos_pos(a: isize, b: isize) -> isize {
            templates::standard_io::div_ceil(a, b)
        }

        #[test_case(0, -2 => 0)]
        #[test_case(1, -2 => 0)]
        #[test_case(2, -2 => -1)]
        #[test_case(3, -2 => -1)]
        #[test_case(4, -2 => -2)]
        fn pos_neg(a: isize, b: isize) -> isize {
            templates::standard_io::div_ceil(a, b)
        }

        #[test_case(-1, 2 => 0)]
        #[test_case(-2, 2 => -1)]
        #[test_case(-3, 2 => -1)]
        #[test_case(-4, 2 => -2)]
        fn neg_pos(a: isize, b: isize) -> isize {
            templates::standard_io::div_ceil(a, b)
        }

        #[test_case(-1, -2 => 1)]
        #[test_case(-2, -2 => 1)]
        #[test_case(-3, -2 => 2)]
        #[test_case(-4, -2 => 2)]
        fn neg_neg(a: isize, b: isize) -> isize {
            templates::standard_io::div_ceil(a, b)
        }
    }

    mod hash_multiset {
        use templates::standard_io::HashMultiset;

        #[test]
        fn value_quantity_pairs() {
            let mut set = HashMultiset::new();

            set.insert(1);
            set.insert(2);
            set.insert(2);

            let mut pairs: Vec<_> = set.value_quantity_pairs().collect();
            pairs.sort_unstable_by_key(|x| x.0);

            assert_eq!(pairs[0], (&1, &1));
            assert_eq!(pairs[1], (&2, &2));
        }

        #[test]
        fn len() {
            let mut set = HashMultiset::new();
            set.insert(1);
            set.insert(2);
            set.insert(2);
            assert_eq!(set.len(), 3);
        }

        #[test]
        fn is_empty() {
            let mut set = HashMultiset::new();

            assert!(set.is_empty());

            set.insert(1);

            assert!(!set.is_empty());

            set.insert(1);

            assert!(!set.is_empty());

            set.remove_single(&1);

            assert!(!set.is_empty());

            set.remove_single(&1);

            assert!(set.is_empty());
        }

        #[test]
        fn contains() {
            let mut set = HashMultiset::new();

            assert!(!set.contains(&1));

            set.insert(1);

            assert!(set.contains(&1));

            set.insert(1);

            assert!(set.contains(&1));

            set.remove_single(&1);

            assert!(set.contains(&1));

            set.remove_single(&1);

            assert!(!set.contains(&1));
        }
    }

    mod btree_multiset {
        use std::iter::FromIterator;
        use templates::standard_io::BTreeMultiset;

        #[test]
        fn value_quantity_pairs() {
            let mut set = BTreeMultiset::new();

            set.insert(1);
            set.insert(2);
            set.insert(2);

            let mut pairs: Vec<_> = set.value_quantity_pairs().collect();
            pairs.sort_unstable_by_key(|x| x.0);

            assert_eq!(pairs[0], (&1, &1));
            assert_eq!(pairs[1], (&2, &2));
        }

        #[test]
        fn key_range() {
            let set = BTreeMultiset::from_iter(vec![1, 2, 2, 3, 4, 4, 5]);

            let mut lte3_asc = set.key_range(..=3);
            assert_eq!(lte3_asc.next(), Some((&1, &1)));
            assert_eq!(lte3_asc.next(), Some((&2, &2)));
            assert_eq!(lte3_asc.next(), Some((&3, &1)));
            assert_eq!(lte3_asc.next(), None);

            let mut gte3_desc = set.key_range(3..);
            assert_eq!(gte3_desc.next_back(), Some((&5, &1)));
            assert_eq!(gte3_desc.next_back(), Some((&4, &2)));
            assert_eq!(gte3_desc.next_back(), Some((&3, &1)));
            assert_eq!(gte3_desc.next_back(), None);
        }

        #[test]
        fn len() {
            let mut set = BTreeMultiset::new();
            set.insert(1);
            set.insert(2);
            set.insert(2);
            assert_eq!(set.len(), 3);
        }

        #[test]
        fn is_empty() {
            let mut set = BTreeMultiset::new();

            assert!(set.is_empty());

            set.insert(1);

            assert!(!set.is_empty());

            set.insert(1);

            assert!(!set.is_empty());

            set.remove_single(&1);

            assert!(!set.is_empty());

            set.remove_single(&1);

            assert!(set.is_empty());
        }

        #[test]
        fn contains() {
            let mut set = BTreeMultiset::new();

            assert!(!set.contains(&1));

            set.insert(1);

            assert!(set.contains(&1));

            set.insert(1);

            assert!(set.contains(&1));

            set.remove_single(&1);

            assert!(set.contains(&1));

            set.remove_single(&1);

            assert!(!set.contains(&1));
        }
    }

    mod adjacent {
        use templates::standard_io::{
            adjacent2d_4neighbors, adjacent2d_8neighbors, Adjacent2d, Point2d,
        };

        #[test]
        fn adjacent2d_free() {
            let dydx = vec![
                Point2d { x: 0, y: -1 },
                Point2d { x: 1, y: 0 },
                Point2d { x: 0, y: 1 },
                Point2d { x: -1, y: 0 },
            ];
            let ads = Adjacent2d::new(Point2d { x: 0, y: 0 }, 0..=1, 0..=1, dydx.iter());
            let ads: Vec<_> = ads.collect();
            assert_eq!(ads.len(), 2);
            assert_eq!(ads[0], Point2d { x: 1, y: 0 });
            assert_eq!(ads[1], Point2d { x: 0, y: 1 });

            let ads = Adjacent2d::new(Point2d { x: 1, y: 1 }, 0..=1, 0..=1, dydx.iter());
            let ads: Vec<_> = ads.collect();
            assert_eq!(ads.len(), 2);
            assert_eq!(ads[0], Point2d { x: 1, y: 0 });
            assert_eq!(ads[1], Point2d { x: 0, y: 1 });

            let ads = Adjacent2d::new(Point2d { x: 1, y: 0 }, 0..=0, 0..=2, dydx.iter());
            let ads: Vec<_> = ads.collect();
            assert_eq!(ads.len(), 2);
            assert_eq!(ads[0], Point2d { x: 2, y: 0 });
            assert_eq!(ads[1], Point2d { x: 0, y: 0 });
        }

        #[test]
        fn adjacent2d_4() {
            let ads = adjacent2d_4neighbors(Point2d { x: 1, y: 1 }, ..=2, ..=2);
            let ads: Vec<_> = ads.collect();
            assert_eq!(ads.len(), 4);
            assert_eq!(ads[0], Point2d { x: 1, y: 0 });
            assert_eq!(ads[1], Point2d { x: 2, y: 1 });
            assert_eq!(ads[2], Point2d { x: 1, y: 2 });
            assert_eq!(ads[3], Point2d { x: 0, y: 1 });
        }

        #[test]
        fn adjacent2d_8() {
            let ads = adjacent2d_8neighbors(Point2d { x: 1, y: 1 }, ..=2, ..=2);
            let ads: Vec<_> = ads.collect();
            assert_eq!(ads.len(), 8);
            assert_eq!(ads[0], Point2d { x: 1, y: 0 });
            assert_eq!(ads[1], Point2d { x: 2, y: 0 });
            assert_eq!(ads[2], Point2d { x: 2, y: 1 });
            assert_eq!(ads[3], Point2d { x: 2, y: 2 });
            assert_eq!(ads[4], Point2d { x: 1, y: 2 });
            assert_eq!(ads[5], Point2d { x: 0, y: 2 });
            assert_eq!(ads[6], Point2d { x: 0, y: 1 });
            assert_eq!(ads[7], Point2d { x: 0, y: 0 });
        }
    }
}
