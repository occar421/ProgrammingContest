#[cfg(test)]
mod tests {
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
        use templates::standard_io::IterExt;
        vec.iter().easy_join(separator)
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
        use templates::standard_io::IterExt;
        vec.iter().easy_join(separator)
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
        use std::collections::HashSet;

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

            assert_eq!(partial_min!(vec![3, 2].iter()), Some(2));
            assert_eq!(partial_min!(vec![vec![3, 2], vec![7, 5]].iter()), Some(2));
            assert_eq!(
                partial_min!(vec![vec![3, 2].iter(), vec![7, 5].iter()]),
                Some(2)
            );
            assert_eq!(
                partial_min!(vec![vec![3, 2].iter(), vec![7, 5].iter()].iter()),
                Some(2)
            );
            assert_eq!(partial_min!(vec![3, 2].iter().filter(|&&x| x > 0)), Some(2));
            assert_eq!(
                partial_min!(vec![vec![3, 2].iter().filter(|&&x| x > 0)]),
                Some(2)
            );
            assert_eq!(partial_min!(vec![HashSet::<usize>::new().iter()]), None);
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
}
