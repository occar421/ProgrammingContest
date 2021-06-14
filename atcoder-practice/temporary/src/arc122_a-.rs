// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::io;
use std::io::{BufRead, BufWriter, Result, Write};
use std::ops::{Add, Div, Mul, Rem, Sub};
use std::str::FromStr;

pub type NodeIndex0Based = usize;
pub type NodeIndex1Based = usize;
pub type Quantity = usize;
pub type Length = usize;
pub type ArrayIndex0Based = usize;
pub type ArrayIndex1Based = usize;
pub type Weight = usize;

// From https://github.com/tanakh/competitive-rs/blob/d5f51f01a6f85ddbebec4cfcb601746bee727181/src/lib.rs#L1-L92
//   and modified by this file author
macro_rules! input_original {
    (source = $s:expr; $($r:tt)*) => {
        let mut iter = $s.split_whitespace();
        let mut _next = || { iter.next().unwrap() };
        input_inner!{_next, $($r)*}
    };
    (stdin = $s:expr; $($r:tt)*) => {
        let mut bytes = std::io::Read::bytes(std::io::BufReader::new($s));
        let mut _next = move || -> String{
            bytes
                .by_ref()
                .map(|r|r.unwrap() as char)
                .skip_while(|c|c.is_whitespace())
                .take_while(|c|!c.is_whitespace())
                .collect()
        };
        input_inner!{_next, $($r)*}
    };
}

#[doc(hidden)]
macro_rules! input_inner {
    ($next:expr) => {};
    ($next:expr, ) => {};

    ($next:expr, $var:ident : $t:tt $($r:tt)*) => {
        let $var = read_value!($next, $t);
        input_inner!{$next $($r)*}
    };
    ($next:expr, mut $var:ident : $t:tt $($r:tt)*) => {
        let mut $var = read_value!($next, $t);
        input_inner!{$next $($r)*}
    };
}

#[doc(hidden)]
macro_rules! read_value {
    ($next:expr, ( $($t:tt),* )) => {
        ( $(read_value!($next, $t)),* )
    };

    ($next:expr, [ $t:tt ; $len:expr ]) => {
        (0..$len).map(|_| read_value!($next, $t)).collect::<Vec<_>>()
    };

    ($next:expr, chars) => {
        read_value!($next, String).chars().collect::<Vec<char>>()
    };

    ($next:expr, bytes) => {
        read_value!($next, String).into_bytes()
    };

    ($next:expr, usize1) => {
        read_value!($next, usize) - 1
    };

    ($next:expr, $t:ty) => {
        $next().parse::<$t>().expect("Parse error")
    };
}

#[allow(unused_macros)]
macro_rules! assert_judge {
    ($method:ident, $input:expr, $expected:expr) => {{
        let output = assert_judge_with_output!($method, $input);

        assert_eq!(output, $expected.trim());
    }};
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_output {
    ($method:ident, $input:expr) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output).expect("Should not emit error");

        String::from_utf8(output)
            .expect("Not UTF-8")
            .trim()
            .to_string()
    }};
}

#[allow(unused_macros)]
macro_rules! assert_eq_with_error {
    ($left:expr, $right:expr, $precision:expr) => {{
        match (&$left, &$right, &$precision) {
            (left_val, right_val, precision_val) => {
                if !(*left_val - *precision_val < *right_val
                    && *right_val < *left_val + *precision_val)
                {
                    // The re-borrows below are intentional. Without them, the stack slot for the
                    // borrow is initialized even before the values are compared, leading to a
                    // noticeable slow down.
                    panic!(
                        r#"assertion failed: `(left == right) +- precision`
      left: `{:?}`,
     right: `{:?}`,
 precision: `{:?}`"#,
                        &*left_val, &*right_val, &*precision_val
                    )
                }
            }
        }
    }};
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_error {
    ($method:ident, $input:expr, $expected:expr, $t:ty | $precision:expr ) => {{
        let output = assert_judge_with_output!($method, $input);

        let actual: $t = output.parse().unwrap();
        let expected: $t = $expected.parse().unwrap();

        assert_eq_with_error!(actual, expected, $precision);
    }};
}

pub trait GenericInteger:
    Copy
    + Clone
    + Eq
    + PartialEq
    + Hash
    + FromStr
    + Display
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;
}

macro_rules! implement_generic_integer {
    () => {};
    ($t:ty $(, $r:ty)*) => {
        impl GenericInteger for $t {
            #[inline]
            fn zero() -> Self { 0 }

            #[inline]
            fn one() -> Self { 1 }
        }

        implement_generic_integer![ $( $r ),* ];
    };
}

implement_generic_integer![u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize];

#[allow(dead_code)]
pub fn gcd<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    if b == T::zero() {
        a
    } else {
        gcd(b, a % b.clone())
    }
}

#[allow(dead_code)]
#[inline]
pub fn lcm<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    a / gcd(a.clone(), b) * b.clone()
}

#[allow(dead_code)]
pub fn prime_factorize(n: usize) -> HashMap<usize, Quantity> {
    let mut map = HashMap::new();

    let sqrt_n = (n as f64).sqrt().ceil() as usize;

    let mut n = n;
    for p in 2..=sqrt_n {
        if n % p != 0 {
            continue;
        }

        let mut exp_number = 0;
        while n % p == 0 {
            exp_number += 1;
            n /= p;
        }

        map.insert(p, exp_number);
    }

    if n != 1 {
        map.insert(n, 1);
    }

    map
}

pub trait IterExt<T>
where
    T: Display,
{
    fn easy_join(&mut self, separator: &str) -> String;
}

impl<TItem, TTrait> IterExt<TItem> for TTrait
where
    TItem: Display,
    TTrait: Iterator<Item = TItem>,
{
    #[inline]
    fn easy_join(&mut self, separator: &str) -> String {
        self.map(|i| format!("{}", i))
            .collect::<Vec<_>>()
            .join(separator)
    }
}

pub trait VecExt<T> {
    fn add_like_string(&mut self) -> T;
}

impl<T> VecExt<T> for Vec<T>
where
    T: GenericInteger,
{
    #[inline]
    fn add_like_string(&mut self) -> T {
        if let Ok(value) = self.iter().easy_join("").parse::<T>() {
            value
        } else {
            panic!("Invalid value")
        }
    }
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! swap {
    ($v1:expr, $v2:expr) => {
        let buf = $v1;
        $v1 = $v2;
        $v2 = buf;
    };
}

#[macro_export]
macro_rules! invert_index {
    ($v:expr) => {{
        let mut goal = vec![0usize; $v.len()];
        for (i, v) in $v.iter().enumerate() {
            goal[*v] = i;
        }
        goal
    }};
}

pub trait ThenSome: Into<bool> {
    fn then_some_<T>(self, t: T) -> Option<T> {
        if self.into() {
            Some(t)
        } else {
            None
        }
    }
}

impl ThenSome for bool {}

// From https://kuretchi.hateblo.jp/entry/rust_nested_vec
#[allow(unused_macros)]
macro_rules! nested_vec {
    ($e:expr; $n:expr) => {
        vec![$e; $n]
    };
    ($e:expr; $n:expr $(; $m:expr)+) => {
        vec![nested_vec!($e $(; $m)+); $n]
    };
}

// From https://maguro.dev/debug-macro/ with some modification
#[allow(unused_macros)]
macro_rules! dbg {
    () => {
        #[cfg(debug_assertions)]
        eprintln!();
    };
    ($($a:expr),* $(,)*) => {
        #[cfg(debug_assertions)]
        eprintln!(concat!($("| ", stringify!($a), "={:?} "),*, "|"), $(&$a),*);
    };
}

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

    #[derive(Debug, Clone, Copy, Default, PartialOrd, Ord, PartialEq, Eq)]
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
        fn fmt(&self, f: &mut Formatter<'_>) -> Result {
            write!(f, "{}", self.value())
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

// -- end of helpers

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let mut stdout = io::stdout();
    let output = BufWriter::new(stdout.lock());

    process(input, output).expect("Should not emit error");
    stdout.flush().unwrap();
}

#[allow(non_snake_case)]
fn process<R, W>(reader: R, mut writer: W) -> Result<()>
where
    R: BufRead,
    W: Write,
{
    #[allow(unused_macros)]
    macro_rules! input {
        ($($r:tt)*) => {
            input_original! { stdin = reader; $($r)* }
        };
    }
    #[allow(unused_macros)]
    macro_rules! print {
        ($($arg:tt)*) => {
            write!(writer, $($arg)*)?;
        }
    }
    #[allow(unused_macros)]
    macro_rules! println {
        () => {
            writeln!(writer)?;
        };
        ($($arg:tt)*) => {
            writeln!(writer, $($arg)*)?;
        }
    }

    {
        use std::cmp::min;

        modulo!(1_000_000_007 as ModMil7);

        input! {
            n: Length,
            a: [usize; n],
        }

        let mut memo = HashMap::new();
        memo.insert(0usize, 1usize);
        memo.insert(1, 1);
        memo.insert(2, 1);
        fn fib_inner(n: usize, memo: &mut HashMap<usize, usize>) -> usize {
            if let Some(&v) = memo.get(&n) {
                v
            } else {
                let result = fib_inner(n - 1, memo) + fib_inner(n - 2, memo);
                memo.insert(n, result);
                result
            }
        }
        let mut fib = |n: usize| fib_inner(n, &mut memo);

        match n {
            1 => {
                println!("{}", a[0]);
            }
            2 => {
                println!("{}", 2 * a[0]);
            }
            _ => {
                let num_patterns = ModMil7::new(fib(n + 1));
                let mut sum = num_patterns * ModMil7::new(a[0]);
                for (i, &a_i) in a.iter().skip(1).enumerate() {
                    let l = min(i + 1, n - i - 1);
                    let piece = ModMil7::new(a_i)
                        * (num_patterns
                            - ModMil7::new(2) * ModMil7::new(fib(n - l)) * ModMil7::new(fib(l)));
                    sum += piece;
                }
                println!("{}", sum);
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(
            process,
            "
3
3 1 5
",
            "15"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
4
1 1 1 1
",
            "10"
        );
    }

    #[test]
    fn sample3() {
        assert_judge!(
            process,
            "
10
866111664 178537096 844917655 218662351 383133839 231371336 353498483 865935868 472381277 579910117
",
            "279919144"
        );
    }
}
