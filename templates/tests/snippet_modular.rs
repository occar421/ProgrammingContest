#[cfg(test)]
mod tests {
    use templates::snippet_modular::modular::ModularUsize;
    use test_case::test_case;

    type Mod3 = ModularUsize<3>;
    type Mod7 = ModularUsize<7>;
    type Mod998244353 = ModularUsize<998244353>;

    #[test_case(0 => 0)]
    #[test_case(1 => 1)]
    #[test_case(2 => 2)]
    #[test_case(3 => 0)]
    #[test_case(4 => 1)]
    #[test_case(5 => 2)]
    #[test_case(6 => 0)]
    #[test_case(12345678 => 0)]
    fn new_mod3(n: usize) -> usize {
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
        Mod7::new(n).reciprocal().map(|r| r.value())
    }

    #[test]
    fn add() {
        let mut a = Mod7::new(3);
        a += 5;
        assert_eq!(a.value(), 1)
    }

    #[test]
    fn sub() {
        let mut a = Mod7::new(3);
        a -= 5;
        assert_eq!(a.value(), 5)
    }

    #[test]
    fn mul() {
        let mut a = Mod7::new(3);
        a *= 5usize;
        assert_eq!(a.value(), 1)
    }

    #[test]
    fn div() {
        let mut a = Mod7::new(3);
        a /= 5usize;
        assert_eq!(a.value(), 2)
    }

    #[test]
    fn neg() {
        let a = Mod7::new(3);
        assert_eq!((-a).value(), 4)
    }

    #[test_case(Vec::<usize>::new() => 0)]
    #[test_case(vec![1] => 1)]
    #[test_case(vec![10, 20] => 2)]
    #[test_case(vec![1, 2, 3, 4, 5] => 1)]
    fn sum_mod7(values: Vec<usize>) -> usize {
        values.iter().map(|&x| Mod7::new(x)).sum::<Mod7>().value()
    }

    #[test_case(Vec::<usize>::new() => 1)]
    #[test_case(vec![0] => 0)]
    #[test_case(vec![2] => 2)]
    #[test_case(vec![10, 20] => 200 % 7)]
    #[test_case(vec![1, 2, 3, 4, 5] => 120 % 7)]
    fn product_mod7(values: Vec<usize>) -> usize {
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
        Mod7::combination_generator(6).generate(n, r).value()
    }

    #[test_case(1234, 21 => 798762687)]
    #[test_case(4321, 765 => 70101255)]
    fn combination_mod998244353(n: usize, r: usize) -> usize {
        Mod998244353::combination_generator(5000)
            .generate(n, r)
            .value()
    }

    #[test]
    fn auto_cast_mod7() {
        let z = Mod7::new(0);
        let vec = vec![z; 10];

        let s: Mod7 = vec.iter().sum();
        assert_eq!(z, s);
        let p: Mod7 = vec.iter().product();
        assert_eq!(z, p);

        assert_eq!((z + 1).value(), 1);
        assert_eq!((z - &1).value(), 6);
        assert_eq!((z + (-1)).value(), 6);
        assert_eq!((z - &(-1)).value(), 1);

        assert_eq!(z > 0, false);
        assert_eq!(z > 10, false);
        assert_eq!(z > 14, false);
        assert_eq!(z < 10, true);
        assert_eq!(z < 14, true);
        assert_eq!(z <= 0, true);
        assert_eq!(z == 0, true);
        assert_eq!(z == 10, false);
        assert_eq!(z == 14, false);
        assert_eq!(0 < z, false);
        assert_eq!(10 < z, false);
        assert_eq!(0 > z, false);
        assert_eq!(10 > z, true);
        assert_eq!(0 == z, true);
        assert_eq!(10 == z, false);
    }
}
