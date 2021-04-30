use crate::standard_io::ThenSome;

pub mod modular {
    //! ref: https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_modular.rs

    use super::ThenSome;
    use std::fmt::{Display, Formatter, Result};
    use std::iter::{Product, Sum};
    use std::marker::PhantomData;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

    pub trait ModuloExt: Clone + Copy {
        fn modulo() -> usize;
    }

    #[macro_export]
    macro_rules! modulo {
        ($num: literal) => {
            modulo!($num by modular::ModuloExt);
        };
        ($num: literal by $trait: path) => {
            #[derive(Debug, Clone, Copy, Default, PartialOrd, Ord, PartialEq, Eq)]
            pub struct Modulo;

            impl $trait for Modulo {
                #[inline]
                fn modulo() -> usize {
                    $num
                }
            }
        };
    }

    #[derive(Debug, Clone, Copy, Default, PartialOrd, Ord, PartialEq, Eq)]
    pub struct PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        value: usize,
        modulo: PhantomData<M>,
    }

    impl<M> Display for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result {
            write!(f, "{}", self.value)
        }
    }

    // Rust in AtCoder does not support const generics due to its version
    impl<M> PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        /// Return the modular value
        ///
        /// # Arguments
        ///
        /// * `n` - Raw value
        pub fn new(n: usize) -> Self {
            Self {
                value: n % M::modulo(),
                modulo: PhantomData,
            }
        }

        #[inline]
        pub fn value(&self) -> usize {
            self.value
        }

        pub fn pow<T>(&self, exp: T) -> Self
        where
            T: Into<Self>,
            M: ModuloExt,
        {
            let exp = exp.into();

            let mut n = exp.value;
            let mut value = self.value;
            let mut result = 1;
            while n > 0 {
                if n & 0x1 == 0x1 {
                    result = (result * value) % M::modulo();
                }
                value = (value * value) % M::modulo();
                n >>= 1;
            }

            Self::new(result)
        }

        #[inline]
        pub fn reciprocal(&self) -> Option<Self> {
            (self.value != 0).then_some_(
                // Fermat's little theorem
                self.pow(Self::new(M::modulo() - 2)),
            )
        }

        #[inline]
        pub fn checked_div<T>(self, rhs: T) -> Option<Self>
        where
            T: Into<Self>,
        {
            rhs.into()
                .reciprocal()
                .map(|rhs_reciprocal| self * rhs_reciprocal)
        }
    }

    impl<T, M> Add<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        type Output = Self;

        #[inline]
        fn add(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();

            Self::new(self.value + rhs.value)
        }
    }

    impl<T, M> AddAssign<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        #[inline]
        fn add_assign(&mut self, rhs: T) {
            *self = *self + rhs;
        }
    }

    impl<T, M> Sub<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        type Output = Self;

        #[inline]
        fn sub(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();

            Self::new(M::modulo() + self.value - rhs.value)
        }
    }

    impl<T, M> SubAssign<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        #[inline]
        fn sub_assign(&mut self, rhs: T) {
            *self = *self - rhs;
        }
    }

    impl<T, M> Mul<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        type Output = Self;

        #[inline]
        fn mul(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();

            Self::new(self.value * rhs.value)
        }
    }

    impl<T, M> MulAssign<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        #[inline]
        fn mul_assign(&mut self, rhs: T) {
            *self = *self * rhs;
        }
    }

    impl<T, M> Div<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        type Output = Self;

        #[inline]
        fn div(self, rhs: T) -> Self::Output {
            self.checked_div(rhs).expect("Cannot divide by 0")
        }
    }

    impl<T, M> DivAssign<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        #[inline]
        fn div_assign(&mut self, rhs: T) {
            *self = *self / rhs
        }
    }

    impl<M> Neg for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        type Output = Self;

        #[inline]
        fn neg(self) -> Self::Output {
            Self::new(0) - self
        }
    }

    impl<M> Sum for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        fn sum<I>(iter: I) -> Self
        where
            I: Iterator<Item = Self>,
        {
            let mut result = Self::new(0);
            for x in iter {
                result += x;
            }
            result
        }
    }

    impl<M> Product for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        fn product<I>(iter: I) -> Self
        where
            I: Iterator<Item = Self>,
        {
            let mut result = Self::new(1);
            for x in iter {
                result *= x;
            }
            result
        }
    }

    impl<T, M> From<T> for PrimeModularUsize<M>
    where
        T: Into<usize>,
        M: ModuloExt,
    {
        #[inline]
        fn from(value: T) -> Self {
            Self::new(value.into())
        }
    }

    pub struct PrimeModularCombinationGenerator<M>
    where
        M: ModuloExt,
    {
        factorials: Vec<PrimeModularUsize<M>>,
        reciprocals_of_factorial: Vec<PrimeModularUsize<M>>,
    }

    impl<M> PrimeModularCombinationGenerator<M>
    where
        M: ModuloExt,
    {
        pub fn new(n_max: usize) -> Self {
            let mut factorials = Vec::with_capacity(n_max + 1);

            // calc from 0! to n!
            let mut f_of_i = PrimeModularUsize::new(1);
            factorials.push(f_of_i);
            for i in 1..=n_max {
                let i = PrimeModularUsize::new(i);
                f_of_i *= i;
                factorials.push(f_of_i);
            }
            let f_of_n = f_of_i;

            // reversed (reciprocals of factorial)
            let mut reversed_rof = Vec::with_capacity(n_max + 1);

            // calc n!^-1
            let mut f_of_i_reciprocal = f_of_n.reciprocal().expect("Should be non-0");
            reversed_rof.push(f_of_i_reciprocal);
            // calc from (n-1)!^-1 to 0!^-1
            for i in (1..=n_max).rev() {
                let i = PrimeModularUsize::new(i);
                f_of_i_reciprocal *= i;
                reversed_rof.push(f_of_i_reciprocal);
            }
            let reciprocals_of_factorial = {
                reversed_rof.reverse();
                reversed_rof
            };

            Self {
                factorials,
                reciprocals_of_factorial,
            }
        }

        pub fn generate(&self, n: usize, r: usize) -> PrimeModularUsize<M> {
            // n! * r!^-1 * (n-r)!^-1
            self.factorials[n]
                * self.reciprocals_of_factorial[r]
                * self.reciprocals_of_factorial[n - r]
        }
    }
}
