#[cfg(test)]
mod tests {
    use templates::snippet_fibonacci_number::fibonacci_number::{
        FibonacciNumberGenerator, FibonacciNumberGeneratorByMatrix,
        FibonacciNumberGeneratorWithCache,
    };
    use test_case::test_case;

    #[test_case(0 => 0)]
    #[test_case(1 => 1)]
    #[test_case(2 => 1)]
    #[test_case(3 => 2)]
    #[test_case(4 => 3)]
    #[test_case(10 => 55)]
    #[test_case(20 => 6765)]
    #[test_case(30 => 832040)]
    #[test_case(40 => 102334155)]
    fn cache_one(n: usize) -> usize {
        let generator = FibonacciNumberGeneratorWithCache::new();
        generator.generate(n)
    }

    #[test_case(0 => 0)]
    #[test_case(1 => 1)]
    #[test_case(2 => 1)]
    #[test_case(3 => 2)]
    #[test_case(4 => 3)]
    #[test_case(10 => 55)]
    #[test_case(20 => 6765)]
    #[test_case(30 => 832040)]
    #[test_case(40 => 102334155)]
    fn matrix_one(n: usize) -> usize {
        let generator = FibonacciNumberGeneratorByMatrix::new();
        generator.generate(n)
    }
}
