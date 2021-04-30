use crate::standard_io::ThenSome;

pub mod modular {
    //! ref: https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_modular.rs

    use super::ThenSome;
    use std::fmt::{Display, Formatter, Result};
    use std::iter::Sum;
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

    // after const generics, Option is not required
    // currently cannot define module from an empty iter
    impl Sum<PrimeModularUsize> for Option<PrimeModularUsize> {
        fn sum<I>(iter: I) -> Self
        where
            I: Iterator<Item = PrimeModularUsize>,
        {
            let mut iter = iter;
            iter.next().map(|first| {
                let mut result = first;
                for x in iter {
                    result += x;
                }
                result
            })
        }
    }

    impl Sum<PrimeModularUsize> for usize {
        fn sum<I>(iter: I) -> Self
        where
            I: Iterator<Item = PrimeModularUsize>,
        {
            let sum: Option<PrimeModularUsize> = iter.sum();
            sum.map_or(0, |x| x.value())
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

    pub struct PrimeModularCombinationGenerator {
        factorials: Vec<PrimeModularUsize>,
        reciprocals_of_factorial: Vec<PrimeModularUsize>,
    }

    impl PrimeModularCombinationGenerator {
        pub fn new(n_max: usize, modulo: usize) -> Self {
            let mut factorials = Vec::with_capacity(n_max + 1);

            // calc from 0! to n!
            let mut f_of_i = PrimeModularUsize::new(1, modulo);
            factorials.push(f_of_i);
            for i in 1..=n_max {
                let i = PrimeModularUsize::new(i, modulo);
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
                let i = PrimeModularUsize::new(i, modulo);
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

        pub fn generate(&self, n: usize, r: usize) -> PrimeModularUsize {
            // n! * r!^-1 * (n-r)!^-1
            self.factorials[n]
                * self.reciprocals_of_factorial[r]
                * self.reciprocals_of_factorial[n - r]
        }
    }
}
