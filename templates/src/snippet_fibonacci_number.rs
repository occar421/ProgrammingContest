use crate::standard_io::GenericInteger;

pub mod fibonacci_number {
    //! FibonacciNumber
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_fibonacci_number.rs

    use super::GenericInteger;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::marker::PhantomData;

    pub trait FibonacciNumberGenerator<GI: GenericInteger> {
        fn generate(&self, n: usize) -> GI;
    }

    pub struct FibonacciNumberGeneratorWithCache<GI: GenericInteger> {
        cache: RefCell<HashMap<usize, GI>>,
    }

    impl<GI: GenericInteger> FibonacciNumberGeneratorWithCache<GI> {
        pub fn new() -> Self {
            let mut map = HashMap::new();
            map.insert(0, GI::zero());
            map.insert(1, GI::one());
            Self { cache: map.into() }
        }
    }

    impl<GI: GenericInteger> FibonacciNumberGenerator<GI> for FibonacciNumberGeneratorWithCache<GI> {
        fn generate(&self, n: usize) -> GI {
            if let Some(&result) = self.cache.borrow().get(&n) {
                return result;
            }

            let result = self.generate(n - 1) + self.generate(n - 2);

            self.cache.borrow_mut().insert(n, result);
            return result;
        }
    }

    // https://blog.miz-ar.info/2019/01/fast-fibonacci/
    pub struct FibonacciNumberGeneratorByMatrix<GI: GenericInteger>(PhantomData<GI>);

    impl<GI: GenericInteger> FibonacciNumberGeneratorByMatrix<GI> {
        pub fn new() -> Self {
            Self(PhantomData)
        }

        fn generate_inner(&self, n: usize) -> FibonacciPair<GI> {
            match n {
                0 => FibonacciPair::zero(),
                1 => FibonacciPair::one(),
                n => {
                    let pair = self.generate_inner(n / 2);
                    let FibonacciPair(c, d) = pair.pow2();
                    if n % 2 == 0 {
                        FibonacciPair(c, d)
                    } else {
                        FibonacciPair(d, c + d)
                    }
                }
            }
        }
    }

    impl<GI: GenericInteger> FibonacciNumberGenerator<GI> for FibonacciNumberGeneratorByMatrix<GI> {
        fn generate(&self, n: usize) -> GI {
            self.generate_inner(n).0
        }
    }

    struct FibonacciPair<GI: GenericInteger>(GI, GI);

    impl<GI: GenericInteger> FibonacciPair<GI> {
        fn zero() -> Self {
            Self(GI::zero(), GI::one())
        }

        fn one() -> Self {
            Self(GI::one(), GI::one())
        }

        fn pow2(&self) -> Self {
            Self(
                self.0 * ((GI::one() + GI::one()) * self.1 - self.0),
                self.0 * self.0 + self.1 * self.1,
            )
        }
    }
}
