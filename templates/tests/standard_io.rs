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
}