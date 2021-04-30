use crate::standard_io::ThenSome;

pub mod modular {
    //! ref: https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_modular.rs

    use super::ThenSome;
    use std::fmt::{Display, Formatter, Result};
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

    #[derive(Debug, Clone, Copy, Default, PartialOrd, Ord, PartialEq, Eq)]
    pub struct PrimeModularUsize {
        value: usize,
        modulo: usize,
    }

    impl Display for PrimeModularUsize {
        fn fmt(&self, f: &mut Formatter<'_>) -> Result {
            write!(f, "{}", self.value)
        }
    }

    // Rust in AtCoder does not support const generics due to its version
    impl PrimeModularUsize {
        /// Return the modular value
        ///
        /// # Arguments
        ///
        /// * `n` - Raw value
        /// * `modulo` - Modulo, must be a prime number
        pub fn new(n: usize, modulo: usize) -> Self {
            Self {
                value: n % modulo,
                modulo,
            }
        }

        #[inline]
        fn new_value(&self, value: usize) -> Self {
            Self::new(value, self.modulo)
        }

        #[inline]
        pub fn value(&self) -> usize {
            self.value
        }

        // remove after const generics
        #[inline]
        fn check_two(first: &Self, second: &Self) {
            debug_assert_eq!(first.modulo, second.modulo);
        }

        pub fn pow<T>(&self, exp: T) -> Self
        where
            T: Into<PrimeModularUsize>,
        {
            let exp = exp.into();
            Self::check_two(self, &exp);

            let mut n = exp.value;
            let mut value = self.value;
            let mut result = 1;
            while n > 0 {
                if n & 0x1 == 0x1 {
                    result = (result * value) % self.modulo;
                }
                value = (value * value) % self.modulo;
                n >>= 1;
            }

            self.new_value(result)
        }

        #[inline]
        pub fn reciprocal(&self) -> Option<Self> {
            (self.value != 0).then_some_(
                // Fermat's little theorem
                self.pow(self.new_value(self.modulo - 2)),
            )
        }

        #[inline]
        pub fn checked_div<T>(self, rhs: T) -> Option<Self>
        where
            T: Into<PrimeModularUsize>,
        {
            rhs.into()
                .reciprocal()
                .map(|rhs_reciprocal| self * rhs_reciprocal)
        }
    }

    impl<T> Add<T> for PrimeModularUsize
    where
        T: Into<PrimeModularUsize>,
    {
        type Output = Self;

        #[inline]
        fn add(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();
            Self::check_two(&self, &rhs);

            self.new_value(self.value + rhs.value)
        }
    }

    impl<T> AddAssign<T> for PrimeModularUsize
    where
        T: Into<PrimeModularUsize>,
    {
        #[inline]
        fn add_assign(&mut self, rhs: T) {
            *self = *self + rhs;
        }
    }

    impl<T> Sub<T> for PrimeModularUsize
    where
        T: Into<PrimeModularUsize>,
    {
        type Output = PrimeModularUsize;

        #[inline]
        fn sub(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();
            Self::check_two(&self, &rhs);

            self.new_value(self.modulo + self.value - rhs.value)
        }
    }

    impl<T> SubAssign<T> for PrimeModularUsize
    where
        T: Into<PrimeModularUsize>,
    {
        #[inline]
        fn sub_assign(&mut self, rhs: T) {
            *self = *self - rhs;
        }
    }

    impl<T> Mul<T> for PrimeModularUsize
    where
        T: Into<PrimeModularUsize>,
    {
        type Output = PrimeModularUsize;

        #[inline]
        fn mul(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();
            Self::check_two(&self, &rhs);

            self.new_value(self.value * rhs.value)
        }
    }

    impl<T> MulAssign<T> for PrimeModularUsize
    where
        T: Into<PrimeModularUsize>,
    {
        #[inline]
        fn mul_assign(&mut self, rhs: T) {
            *self = *self * rhs;
        }
    }

    impl<T> Div<T> for PrimeModularUsize
    where
        T: Into<PrimeModularUsize>,
    {
        type Output = PrimeModularUsize;

        #[inline]
        fn div(self, rhs: T) -> Self::Output {
            self.checked_div(rhs).expect("Cannot divide by 0")
        }
    }

    impl<T> DivAssign<T> for PrimeModularUsize
    where
        T: Into<PrimeModularUsize>,
    {
        #[inline]
        fn div_assign(&mut self, rhs: T) {
            *self = *self / rhs
        }
    }

    impl Neg for PrimeModularUsize {
        type Output = PrimeModularUsize;

        #[inline]
        fn neg(self) -> Self::Output {
            self.new_value(0) - self
        }
    }

    // after const generics
    // impl<T, const M: usize> From<T> for ModularUsize<M>
    // where
    //     T: Into<usize>,
    // {
    //     #[inline]
    //     fn from(value: T) -> Self {
    //         Self::new(value.into(), M)
    //     }
    // }
}
