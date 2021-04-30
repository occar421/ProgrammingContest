#[cfg(test)]
mod tests {
    use templates::snippet_modular::modular::PrimeModularUsize;
    use test_case::test_case;

    #[test_case(0 => 0)]
    #[test_case(1 => 1)]
    #[test_case(2 => 2)]
    #[test_case(3 => 0)]
    #[test_case(4 => 1)]
    #[test_case(5 => 2)]
    #[test_case(6 => 0)]
    #[test_case(12345678 => 0)]
    fn new_mod3(n: usize) -> usize {
        PrimeModularUsize::new(n, 3).value()
    }

    #[test_case(0,1 => 0)]
    #[test_case(1,1 => 1)]
    #[test_case(1,2 => 1)]
    #[test_case(2,0 => 1)]
    #[test_case(2,1 => 2)]
    #[test_case(2,2 => 1)]
    #[test_case(3,1 => 0)]
    #[test_case(3,2 => 0)]
    #[test_case(4,1 => 1)]
    #[test_case(4,2 => 1)]
    #[test_case(5,1 => 2)]
    #[test_case(5,2 => 1)]
    #[test_case(6,1 => 0)]
    #[test_case(6,2 => 0)]
    fn pow_mod3(n: usize, exp: usize) -> usize {
        let base = PrimeModularUsize::new(n, 3);
        base.pow(PrimeModularUsize::new(exp, 3)).value()
    }

    #[test_case(0 => None)]
    #[test_case(1 => Some(1))]
    #[test_case(2 => Some(2))]
    #[test_case(3 => None)]
    #[test_case(4 => Some(1))]
    #[test_case(5 => Some(2))]
    #[test_case(6 => None)]
    #[test_case(12345678 => None)]
    fn reciprocal_mod3(n: usize) -> Option<usize> {
        PrimeModularUsize::new(n, 3).reciprocal().map(|r| r.value())
    }

    #[test_case(0 => None)]
    #[test_case(1 => Some(1))]
    #[test_case(2 => Some(4))]
    #[test_case(3 => Some(5))]
    #[test_case(4 => Some(2))]
    #[test_case(5 => Some(3))]
    #[test_case(6 => Some(6))]
    #[test_case(7 => None)]
    fn reciprocal_mod7(n: usize) -> Option<usize> {
        PrimeModularUsize::new(n, 7).reciprocal().map(|r| r.value())
    }

    #[test]
    fn add() {
        let mut a = PrimeModularUsize::new(3, 7);
        a += PrimeModularUsize::new(5, 7);
        assert_eq!(a.value(), 1)
    }

    #[test]
    fn sub() {
        let mut a = PrimeModularUsize::new(3, 7);
        a -= PrimeModularUsize::new(5, 7);
        assert_eq!(a.value(), 5)
    }

    #[test]
    fn r#mut() {
        let mut a = PrimeModularUsize::new(3, 7);
        a *= PrimeModularUsize::new(5, 7);
        assert_eq!(a.value(), 1)
    }

    #[test]
    fn div() {
        let mut a = PrimeModularUsize::new(3, 7);
        a /= PrimeModularUsize::new(5, 7);
        assert_eq!(a.value(), 2)
    }

    #[test]
    fn neg() {
        let a = PrimeModularUsize::new(3, 7);
        assert_eq!((-a).value(), 4)
    }
}
