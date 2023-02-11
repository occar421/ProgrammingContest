use crate::standard_io::{AutoProduct, AutoSum, GenericInteger, Max, Min, PartialMax, PartialMin};

pub mod modular {
    //! Modular
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_modular.rs

    use super::{AutoProduct, AutoSum, GenericInteger, Max, Min, PartialMax, PartialMin};
    use std::cmp::Ordering;
    use std::fmt::{Debug, Display, Formatter};
    use std::hash::{Hash, Hasher};
    use std::iter::{Product, Sum};
    use std::ops::{
        Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
    };
    use std::str::FromStr;

    #[derive(Clone, Copy, Default)]
    pub struct PrimeModularUsize<const MODULO: usize> {
        value: usize,
    }

    /// ```
    /// # use templates::snippet_modular::modular::ModularUsize;
    /// type Mod998244353 = ModularUsize<998244353>;
    /// ```
    pub type ModularUsize<const MODULO: usize> = PrimeModularUsize<MODULO>;

    impl<const MODULO: usize> Display for PrimeModularUsize<MODULO> {
        #[inline]
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.value())
        }
    }

    impl<const MODULO: usize> Debug for PrimeModularUsize<MODULO> {
        #[inline]
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.value())
        }
    }

    impl<const MODULO: usize> PartialEq for PrimeModularUsize<MODULO> {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            self.value.eq(&other.value)
        }
    }

    impl<const MODULO: usize> Eq for PrimeModularUsize<MODULO> {}

    impl<const MODULO: usize> PartialOrd for PrimeModularUsize<MODULO> {
        #[inline]
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.value.partial_cmp(&other.value)
        }
    }

    impl<const MODULO: usize> Ord for PrimeModularUsize<MODULO> {
        #[inline]
        fn cmp(&self, other: &Self) -> Ordering {
            self.value.cmp(&other.value)
        }
    }

    impl<const MODULO: usize> Hash for PrimeModularUsize<MODULO> {
        #[inline]
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.value.hash(state)
        }
    }

    impl<const MODULO: usize> FromStr for PrimeModularUsize<MODULO> {
        type Err = std::num::ParseIntError;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            usize::from_str(s).map(|x| Self::new(x))
        }
    }

    impl<const MODULO: usize> PrimeModularUsize<MODULO> {
        /// Return the modular value
        ///
        /// # Arguments
        ///
        /// * `n` - Raw value
        pub fn new(n: usize) -> Self {
            Self { value: n % MODULO }
        }

        #[inline]
        pub fn value(&self) -> usize {
            self.value
        }

        pub fn pow<T>(&self, exp: T) -> Self
        where
            T: Into<Self>,
        {
            let exp = exp.into();

            let mut n = exp.value;
            let mut value = self.value;
            let mut result = 1;
            while n > 0 {
                if n & 0x1 == 0x1 {
                    result = (result * value) % MODULO;
                }
                value = (value * value) % MODULO;
                n >>= 1;
            }

            Self::new(result)
        }

        pub fn reciprocal(&self) -> Option<Self> {
            (self.value != 0).then(|| // use `then` for lazy evaluation
                // Fermat's little theorem
                self.pow(Self::new(MODULO - 2)))
        }

        pub fn checked_div<T>(self, rhs: T) -> Option<Self>
        where
            T: Into<Self>,
        {
            rhs.into()
                .reciprocal()
                .map(|rhs_reciprocal| self * rhs_reciprocal)
        }

        pub fn combination_generator(n_max: usize) -> PrimeModularCombinationGenerator<MODULO> {
            PrimeModularCombinationGenerator::new(n_max)
        }
    }

    impl<const MODULO: usize> From<&PrimeModularUsize<MODULO>> for PrimeModularUsize<MODULO> {
        fn from(v: &PrimeModularUsize<MODULO>) -> Self {
            *v
        }
    }

    impl<const MODULO: usize> From<usize> for PrimeModularUsize<MODULO> {
        #[inline]
        fn from(v: usize) -> Self {
            Self::new(v)
        }
    }

    impl<const MODULO: usize> From<&usize> for PrimeModularUsize<MODULO> {
        #[inline]
        fn from(v: &usize) -> Self {
            From::<usize>::from(*v)
        }
    }

    impl<const MODULO: usize> From<isize> for PrimeModularUsize<MODULO> {
        fn from(v: isize) -> Self {
            if v >= 0 {
                Self::new(v as usize)
            } else if let Some(v) = v.checked_neg() {
                -Self::new(v as usize)
            } else {
                -Self::new((v + MODULO as isize) as usize)
            }
        }
    }

    impl<const MODULO: usize> From<&isize> for PrimeModularUsize<MODULO> {
        #[inline]
        fn from(v: &isize) -> Self {
            From::<isize>::from(*v)
        }
    }

    impl<const MODULO: usize> From<i32> for PrimeModularUsize<MODULO> {
        #[inline]
        fn from(v: i32) -> Self {
            From::<isize>::from(v as isize)
        }
    }

    impl<const MODULO: usize> From<&i32> for PrimeModularUsize<MODULO> {
        #[inline]
        fn from(v: &i32) -> Self {
            From::<isize>::from(*v as isize)
        }
    }

    impl<T, const MODULO: usize> Add<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        type Output = Self;

        #[inline]
        fn add(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();

            Self::new(self.value + rhs.value)
        }
    }

    impl<T, const MODULO: usize> AddAssign<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        #[inline]
        fn add_assign(&mut self, rhs: T) {
            *self = *self + rhs;
        }
    }

    impl<T, const MODULO: usize> Sub<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        type Output = Self;

        #[inline]
        fn sub(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();

            Self::new(MODULO + self.value - rhs.value)
        }
    }

    impl<T, const MODULO: usize> SubAssign<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        #[inline]
        fn sub_assign(&mut self, rhs: T) {
            *self = *self - rhs;
        }
    }

    impl<T, const MODULO: usize> Mul<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        type Output = Self;

        #[inline]
        fn mul(self, rhs: T) -> Self::Output {
            let rhs = rhs.into();

            Self::new(self.value * rhs.value)
        }
    }

    impl<T, const MODULO: usize> MulAssign<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        #[inline]
        fn mul_assign(&mut self, rhs: T) {
            *self = *self * rhs;
        }
    }

    impl<T, const MODULO: usize> Div<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        type Output = Self;

        #[inline]
        fn div(self, rhs: T) -> Self::Output {
            self.checked_div(rhs).expect("Cannot divide by 0")
        }
    }

    impl<T, const MODULO: usize> DivAssign<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        #[inline]
        fn div_assign(&mut self, rhs: T) {
            *self = *self / rhs
        }
    }

    impl<T, const MODULO: usize> Rem<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        type Output = Self;

        #[inline]
        fn rem(self, rhs: T) -> Self::Output {
            Self::new(self.value % rhs.into().value)
        }
    }

    impl<T, const MODULO: usize> RemAssign<T> for PrimeModularUsize<MODULO>
    where
        T: Into<Self>,
    {
        #[inline]
        fn rem_assign(&mut self, rhs: T) {
            *self = *self % rhs
        }
    }

    impl<const MODULO: usize> Neg for PrimeModularUsize<MODULO> {
        type Output = Self;

        #[inline]
        fn neg(self) -> Self::Output {
            Self::new(0) - self
        }
    }

    impl<const MODULO: usize> PartialEq<usize> for PrimeModularUsize<MODULO> {
        fn eq(&self, other: &usize) -> bool {
            *other < MODULO && self.value == *other
        }
    }

    impl<const MODULO: usize> PartialOrd<usize> for PrimeModularUsize<MODULO> {
        fn partial_cmp(&self, other: &usize) -> Option<Ordering> {
            if *other < MODULO {
                self.value.partial_cmp(other)
            } else {
                Ordering::Less.into()
            }
        }
    }

    impl<const MODULO: usize> PartialEq<PrimeModularUsize<MODULO>> for usize {
        fn eq(&self, other: &PrimeModularUsize<MODULO>) -> bool {
            other.eq(self)
        }
    }

    impl<const MODULO: usize> PartialOrd<PrimeModularUsize<MODULO>> for usize {
        fn partial_cmp(&self, other: &PrimeModularUsize<MODULO>) -> Option<Ordering> {
            other.partial_cmp(self).map(|x| x.reverse())
        }
    }

    impl<const MODULO: usize> Sum for PrimeModularUsize<MODULO> {
        fn sum<I>(iter: I) -> Self
        where
            I: Iterator<Item = Self>,
        {
            iter.fold(Self::zero(), |acc, x| acc + x)
        }
    }

    impl<'a, const MODULO: usize> Sum<&'a PrimeModularUsize<MODULO>> for PrimeModularUsize<MODULO> {
        fn sum<I>(iter: I) -> Self
        where
            I: Iterator<Item = &'a Self>,
        {
            iter.fold(Self::zero(), |acc, x| acc + x)
        }
    }

    impl<const MODULO: usize> Product for PrimeModularUsize<MODULO> {
        fn product<I>(iter: I) -> Self
        where
            I: Iterator<Item = Self>,
        {
            iter.fold(Self::one(), |acc, x| acc * x)
        }
    }

    impl<'a, const MODULO: usize> Product<&'a PrimeModularUsize<MODULO>> for PrimeModularUsize<MODULO> {
        fn product<I>(iter: I) -> Self
        where
            I: Iterator<Item = &'a Self>,
        {
            iter.fold(Self::one(), |acc, x| acc * x)
        }
    }

    impl<const MODULO: usize> GenericInteger for PrimeModularUsize<MODULO> {
        #[inline]
        fn zero() -> Self {
            Self::new(0)
        }

        #[inline]
        fn one() -> Self {
            Self::new(1)
        }

        #[inline]
        fn is_odd(&self) -> bool {
            self.value.is_odd()
        }

        #[inline]
        fn is_even(&self) -> bool {
            self.value.is_even()
        }
    }

    impl<const MODULO: usize> PartialMin for PrimeModularUsize<MODULO> {
        type Result = PrimeModularUsize<MODULO>;

        #[inline]
        fn partial_min(&self) -> Option<Self::Result> {
            self.clone().into()
        }
    }

    impl<const MODULO: usize> Min for PrimeModularUsize<MODULO> {
        #[inline]
        fn min(&self) -> Self::Result {
            self.clone()
        }
    }

    impl<const MODULO: usize> PartialMax for PrimeModularUsize<MODULO> {
        type Result = PrimeModularUsize<MODULO>;

        #[inline]
        fn partial_max(&self) -> Option<Self::Result> {
            self.clone().into()
        }
    }

    impl<const MODULO: usize> Max for PrimeModularUsize<MODULO> {
        #[inline]
        fn max(&self) -> Self::Result {
            self.clone()
        }
    }

    impl<const MODULO: usize> AutoSum for PrimeModularUsize<MODULO> {
        type Result = PrimeModularUsize<MODULO>;

        #[inline]
        fn sum(&self) -> Self {
            self.clone()
        }
    }

    impl<const MODULO: usize> AutoProduct for PrimeModularUsize<MODULO> {
        type Result = PrimeModularUsize<MODULO>;

        #[inline]
        fn product(&self) -> Self {
            self.clone()
        }
    }

    pub struct PrimeModularCombinationGenerator<const MODULO: usize> {
        factorials: Vec<PrimeModularUsize<MODULO>>,
        reciprocals_of_factorial: Vec<PrimeModularUsize<MODULO>>,
    }

    impl<const MODULO: usize> PrimeModularCombinationGenerator<MODULO> {
        pub fn new(n_max: usize) -> Self {
            let mut factorials = Vec::with_capacity(n_max + 1);

            // calc from 0! to n!
            let mut f_of_i = PrimeModularUsize::new(1);
            factorials.push(f_of_i);
            for i in 1..=n_max {
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

        pub fn generate(&self, n: usize, r: usize) -> PrimeModularUsize<MODULO> {
            // n! * r!^-1 * (n-r)!^-1
            self.factorials[n]
                * self.reciprocals_of_factorial[r]
                * self.reciprocals_of_factorial[n - r]
        }
    }
}
