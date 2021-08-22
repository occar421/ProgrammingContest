use crate::standard_io::{GenericInteger, ThenSome};

pub mod modular {
    //! Modular
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_modular.rs

    use super::{GenericInteger, ThenSome};
    use std::cmp::Ordering;
    use std::fmt::{Debug, Display, Formatter};
    use std::hash::{Hash, Hasher};
    use std::iter::{Product, Sum};
    use std::marker::PhantomData;
    use std::ops::{
        Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
    };
    use std::str::FromStr;

    pub trait ModuloExt: Clone + Copy {
        fn modulo() -> usize;
    }

    #[macro_export]
    macro_rules! modulo {
        ($num: literal as $alias: ident) => {
            modulo!($num in modular as $alias);
        };
        ($num: literal in $module_base: path as $alias: ident) => {
            #[derive(Debug, Clone, Copy, Default, PartialOrd, Ord, PartialEq, Eq)]
            pub struct Modulo;

            use $module_base as base;

            impl base::ModuloExt for Modulo {
                #[inline]
                fn modulo() -> usize {
                    $num
                }
            }

            type $alias = base::PrimeModularUsize<Modulo>;
        };
    }

    pub trait ModularUsize {
        type Modulo: ModuloExt;
    }

    #[derive(Clone, Copy, Default)]
    pub struct PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        value: usize,
        modulo: PhantomData<M>,
    }

    impl<M> ModularUsize for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        type Modulo = M;
    }

    impl<M> Display for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.value())
        }
    }

    impl<M> Debug for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.value())
        }
    }

    impl<M> PartialEq for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn eq(&self, other: &Self) -> bool {
            self.value.eq(&other.value)
        }
    }

    impl<M> Eq for PrimeModularUsize<M> where M: ModuloExt {}

    impl<M> PartialOrd for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.value.partial_cmp(&other.value)
        }
    }

    impl<M> Ord for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn cmp(&self, other: &Self) -> Ordering {
            self.value.cmp(&other.value)
        }
    }

    impl<M> Hash for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.value.hash(state)
        }
    }

    impl<M> FromStr for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        type Err = std::num::ParseIntError;

        #[inline]
        fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
            usize::from_str(s).map(|x| Self::new(x))
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

    impl<M> From<&PrimeModularUsize<M>> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        fn from(v: &PrimeModularUsize<M>) -> Self {
            *v
        }
    }

    impl<M> From<usize> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn from(v: usize) -> Self {
            Self::new(v)
        }
    }

    impl<M> From<&usize> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn from(v: &usize) -> Self {
            From::<usize>::from(*v)
        }
    }

    impl<M> From<isize> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn from(v: isize) -> Self {
            if v >= 0 {
                Self::new(v as usize)
            } else if let Some(v) = v.checked_neg() {
                -Self::new(v as usize)
            } else {
                -Self::new((v + M::modulo() as isize) as usize)
            }
        }
    }

    impl<M> From<&isize> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn from(v: &isize) -> Self {
            From::<isize>::from(*v)
        }
    }

    impl<M> From<i32> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn from(v: i32) -> Self {
            From::<isize>::from(v as isize)
        }
    }

    impl<M> From<&i32> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn from(v: &i32) -> Self {
            From::<isize>::from(*v as isize)
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

    impl<T, M> Rem<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        type Output = Self;

        #[inline]
        fn rem(self, rhs: T) -> Self::Output {
            Self::new(self.value % rhs.into().value)
        }
    }

    impl<T, M> RemAssign<T> for PrimeModularUsize<M>
    where
        T: Into<Self>,
        M: ModuloExt,
    {
        #[inline]
        fn rem_assign(&mut self, rhs: T) {
            *self = *self % rhs
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

    impl<M> PartialEq<usize> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        fn eq(&self, other: &usize) -> bool {
            *other < M::modulo() && self.value == *other
        }
    }

    impl<M> PartialOrd<usize> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        fn partial_cmp(&self, other: &usize) -> Option<Ordering> {
            if *other < M::modulo() {
                self.value.partial_cmp(other)
            } else {
                Ordering::Less.into()
            }
        }
    }

    impl<M> PartialEq<PrimeModularUsize<M>> for usize
    where
        M: ModuloExt,
    {
        fn eq(&self, other: &PrimeModularUsize<M>) -> bool {
            other.eq(self)
        }
    }

    impl<M> PartialOrd<PrimeModularUsize<M>> for usize
    where
        M: ModuloExt,
    {
        fn partial_cmp(&self, other: &PrimeModularUsize<M>) -> Option<Ordering> {
            other.partial_cmp(self).map(|x| x.reverse())
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
            iter.fold(Self::zero(), |acc, x| acc + x)
        }
    }

    impl<'a, M> Sum<&'a PrimeModularUsize<M>> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        fn sum<I>(iter: I) -> Self
        where
            I: Iterator<Item = &'a Self>,
        {
            iter.fold(Self::zero(), |acc, x| acc + x)
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
            iter.fold(Self::one(), |acc, x| acc * x)
        }
    }

    impl<'a, M> Product<&'a PrimeModularUsize<M>> for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        fn product<I>(iter: I) -> Self
        where
            I: Iterator<Item = &'a Self>,
        {
            iter.fold(Self::one(), |acc, x| acc * x)
        }
    }

    impl<M> GenericInteger for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
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
            self.value % 2 == 1
        }

        #[inline]
        fn is_even(&self) -> bool {
            self.value % 2 == 0
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
        fn new(n_max: usize) -> Self {
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

    pub struct CombinationGenerator<U>(PhantomData<U>)
    where
        U: ModularUsize;

    impl<M> CombinationGenerator<PrimeModularUsize<M>>
    where
        M: ModuloExt,
    {
        #[inline]
        pub fn new(n_max: usize) -> PrimeModularCombinationGenerator<M> {
            PrimeModularCombinationGenerator::new(n_max)
        }
    }
}
