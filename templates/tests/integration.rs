#[cfg(test)]
mod tests {
    use templates::snippet_cumulative_sum::cumulative_sum::CumulativeSum1d;
    use templates::snippet_fibonacci_number::fibonacci_number::{
        FibonacciNumberGenerator, FibonacciNumberGeneratorByMatrix,
        FibonacciNumberGeneratorWithCache,
    };
    use templates::snippet_modular::modular::ModularUsize;
    use templates::standard_io::lcm;

    type Mod7 = ModularUsize<7>;

    #[test]
    fn lcm_mod7() {
        let result = lcm(Mod7::new(3), Mod7::new(4));
        assert_eq!(result.value(), 12 % 7);
    }

    #[test]
    fn fibonacci_number_cache_mod7() {
        let fib_gen = FibonacciNumberGeneratorWithCache::<Mod7>::new();
        assert_eq!(fib_gen.generate(20).value(), 6765 % 7);
        assert_eq!(fib_gen.generate(30).value(), 832040 % 7);
        assert_eq!(fib_gen.generate(40).value(), 102334155 % 7);
    }

    #[test]
    fn fibonacci_number_matrix_mod7() {
        let fib_gen = FibonacciNumberGeneratorByMatrix::<Mod7>::new();
        assert_eq!(fib_gen.generate(20).value(), 6765 % 7);
        assert_eq!(fib_gen.generate(30).value(), 832040 % 7);
        assert_eq!(fib_gen.generate(40).value(), 102334155 % 7);
    }

    #[test]
    fn cum_sum_mod7() {
        let data = vec![Mod7::new(2), Mod7::new(4), Mod7::new(6)];
        let cum_sum = CumulativeSum1d::new(data.len(), &data);
        assert_eq!(cum_sum.sum_in(1..2).value(), 4 % 7);
        assert_eq!(cum_sum.sum_in(..).value(), 12 % 7);
    }

    #[test]
    fn min_mod7() {
        use templates::partial_min;
        use templates::standard_io::PartialMin;

        let data = vec![
            vec![Mod7::new(2), Mod7::new(4)],
            vec![Mod7::new(6), Mod7::new(8)],
        ];
        assert_eq!(partial_min!(data).unwrap().value(), 8 % 7);
        assert_eq!(partial_min!(data.last()).unwrap().value(), 8 % 7);
    }

    #[test]
    fn sum_mod7() {
        use templates::standard_io::AutoSum;
        use templates::sum;
        let data = vec![
            vec![Mod7::new(2), Mod7::new(4)],
            vec![Mod7::new(6), Mod7::new(8)],
        ];
        assert_eq!(sum!(data).value(), 20 % 7);
        assert_eq!(sum!(data.last()).value(), 14 % 7);
    }
}
