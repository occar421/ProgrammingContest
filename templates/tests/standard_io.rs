extern crate test_case_derive;

#[cfg(test)]
mod tests {
    use test_case_derive::test_case;

    #[test]
    fn _ignite() {}

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
}