#[cfg(test)]
mod tests {
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

    #[test_case(4 => vec![2, 3])]
    #[test_case(20 => vec![2, 3, 5, 7, 11, 13, 17, 19])]
    fn eratosthenes_sieve(n: usize) -> Vec<usize> {
        templates::standard_io::eratosthenes_sieve(n)
    }

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
}
