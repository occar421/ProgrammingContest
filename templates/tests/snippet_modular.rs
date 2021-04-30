#[cfg(test)]
mod tests {
    use templates::{
        modulo,
        snippet_modular::modular::{
            ModuloExt, PrimeModularCombinationGenerator, PrimeModularUsize,
        },
    };
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
        modulo!(3 by ModuloExt);
        type Mod3 = PrimeModularUsize<Modulo>;

        Mod3::new(n).value()
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
        modulo!(3 by ModuloExt);
        type Mod3 = PrimeModularUsize<Modulo>;

        Mod3::new(n).pow(exp).value()
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
        modulo!(3 by ModuloExt);
        type Mod3 = PrimeModularUsize<Modulo>;

        Mod3::new(n).reciprocal().map(|r| r.value())
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
        modulo!(7 by ModuloExt);
        type Mod7 = PrimeModularUsize<Modulo>;

        Mod7::new(n).reciprocal().map(|r| r.value())
    }

    #[test]
    fn add() {
        modulo!(7 by ModuloExt);
        type Mod7 = PrimeModularUsize<Modulo>;

        let mut a = Mod7::new(3);
        a += 5usize;
        assert_eq!(a.value(), 1)
    }

    #[test]
    fn sub() {
        modulo!(7 by ModuloExt);
        type Mod7 = PrimeModularUsize<Modulo>;

        let mut a = Mod7::new(3);
        a -= 5usize;
        assert_eq!(a.value(), 5)
    }

    #[test]
    fn mul() {
        modulo!(7 by ModuloExt);
        type Mod7 = PrimeModularUsize<Modulo>;

        let mut a = Mod7::new(3);
        a *= 5usize;
        assert_eq!(a.value(), 1)
    }

    #[test]
    fn div() {
        modulo!(7 by ModuloExt);
        type Mod7 = PrimeModularUsize<Modulo>;

        let mut a = Mod7::new(3);
        a /= 5usize;
        assert_eq!(a.value(), 2)
    }

    #[test]
    fn neg() {
        modulo!(7 by ModuloExt);
        type Mod7 = PrimeModularUsize<Modulo>;

        let a = Mod7::new(3);
        assert_eq!((-a).value(), 4)
    }

    #[test_case(Vec::<usize>::new() => 0)]
    #[test_case(vec![1] => 1)]
    #[test_case(vec![10, 20] => 2)]
    #[test_case(vec![1, 2, 3, 4, 5] => 1)]
    fn sum_mod7(values: Vec<usize>) -> usize {
        modulo!(7 by ModuloExt);
        type Mod7 = PrimeModularUsize<Modulo>;

        values.iter().map(|&x| Mod7::new(x)).sum::<Mod7>().value()
    }

    #[test_case(Vec::<usize>::new() => 1)]
    #[test_case(vec![0] => 0)]
    #[test_case(vec![2] => 2)]
    #[test_case(vec![10, 20] => 200 % 7)]
    #[test_case(vec![1, 2, 3, 4, 5] => 120 % 7)]
    fn product_mod7(values: Vec<usize>) -> usize {
        modulo!(7 by ModuloExt);
        type Mod7 = PrimeModularUsize<Modulo>;

        values
            .iter()
            .map(|&x| Mod7::new(x))
            .product::<Mod7>()
            .value()
    }

    #[test_case(3, 1 => 3 % 7)]
    #[test_case(4, 2 => 6 % 7)]
    #[test_case(5, 3 => 10 % 7)]
    fn combination_mod7(n: usize, r: usize) -> usize {
        modulo!(7 by ModuloExt);
        PrimeModularCombinationGenerator::<Modulo>::new(6)
            .generate(n, r)
            .value()
    }

    #[test_case(1234, 21 => 798762687)]
    #[test_case(4321, 765 => 70101255)]
    fn combination_mod998244353(n: usize, r: usize) -> usize {
        modulo!(998244353 by ModuloExt);

        PrimeModularCombinationGenerator::<Modulo>::new(5000)
            .generate(n, r)
            .value()
    }
}
