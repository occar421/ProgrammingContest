// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::cmp::*;
use std::collections::*;
use std::fmt::{Debug, Display};
use std::hash::Hash;
#[allow(unused_imports)]
use std::iter::FromIterator;
use std::iter::{Product, Sum};
use std::ops::*;
use std::str::FromStr;

// From https://github.com/tanakh/competitive-rs/blob/d5f51f01a6f85ddbebec4cfcb601746bee727181/src/lib.rs#L1-L92
//   and modified by this file author
#[doc(hidden)]
struct Handler<F: FnMut() -> String> {
    handle: F,
}

#[doc(hidden)]
macro_rules! prepare_input {
    (source = $s:expr) => {{
        let mut iter = $s.split_whitespace();
        Handler {
            handle: || iter.next().unwrap(),
        }
    }};
    (stdin = $s:expr) => {{
        let mut bytes = std::io::Read::bytes(std::io::BufReader::new($s));
        Handler {
            handle: move || {
                bytes
                    .by_ref()
                    .map(|r| r.unwrap() as char)
                    .skip_while(|c| c.is_whitespace())
                    .take_while(|c| !c.is_whitespace())
                    .collect::<String>()
            },
        }
    }};
}

macro_rules! input_original {
    (source = $s:expr; $($r:tt)*) => {
        let mut _handler = prepare_input!{source = $s};
        let mut _next = || (_handler.handle)();
        input_inner!{_next, $($r)*}
    };
    (stdin = $s:expr; $($r:tt)*) => {
        let mut _handler = prepare_input!{stdin = $s};
        let mut _next = || (_handler.handle)();
        input_inner!{_next, $($r)*}
    };
    (handler = $h: ident; $($r:tt)*) => {
        let mut _next = || ($h.handle)();
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

    ($next:expr, [ $t:tt ; $len1:expr ; $len2:expr ]) => {
        (0..$len1).map(|_| (0..$len2).map(|_| read_value!($next, $t)).collect::<Vec<_>>()).collect::<Vec<_>>()
    };

    ($next:expr, [ $t:tt ; $len:expr ]) => {
        (0..$len).map(|_| read_value!($next, $t)).collect::<Vec<_>>()
    };

    ($next:expr, chars) => {
        (read_value!($next, String).chars().collect::<Vec<char>>()) as Vec<char>
    };

    ($next:expr, bytes) => {
        (read_value!($next, String).into_bytes()) as Vec<u8>
    };

    ($next:expr, usize0) => {
        (read_value!($next, usize)) as usize
    };

    ($next:expr, usize1) => {
        (read_value!($next, usize) - 1) as usize
    };

    ($next:expr, (Point2d<$t:tt>)) => {
        {
            let x = read_value!($next, $t);
            let y = read_value!($next, $t);
            Point2d { x, y }
        }
    };

    ($next:expr, $t:ty) => {
        ($next().parse::<$t>().expect("Parse error")) as $t
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

macro_rules! impl_collection_util {
    ($tr: tt :: $met: ident -> $ret: tt where $req: tt { $proc: ident }, []) => {};
    ($tr: tt :: $met: ident -> $ret: tt where $req: tt { $proc: ident }, [ $t: tt $(, $r:tt)* ]) => {
        impl<T, PT> $tr for $t<PT>
        where
            T: $req,
            PT: $tr<Result = T>,
        {
            type Result = T;

            #[inline]
            fn $met(&self) -> $ret<Self::Result> {
                $proc(self)
            }
        }

        impl<T, PT> $tr for &$t<PT>
        where
            T: $req,
            PT: $tr<Result = T>,
        {
            type Result = T;

            #[inline]
            fn $met(&self) -> $ret<Self::Result> {
                $proc(*self)
            }
        }

        impl_collection_util!($tr::$met -> $ret where $req {$proc}, [ $( $r ),* ]);
    };
}

type Slice<T> = [T];
type Id<T> = T;

pub trait Min: PartialMin {
    fn min(&self) -> Self::Result;
}

pub trait PartialMin {
    type Result;
    fn partial_min(&self) -> Option<Self::Result>;
}

fn iter_partial_min<'a, T, PT, I>(iter: I) -> Option<T>
where
    T: Ord,
    PT: 'a + PartialMin<Result = T>,
    I: 'a + IntoIterator<Item = &'a PT>,
{
    iter.into_iter().filter_map(|x| x.partial_min()).min()
}

impl_collection_util!(
    PartialMin::partial_min -> Option where Ord { iter_partial_min },
    [Option, Slice, Vec, HashSet]
);

pub fn min_with_partial<T>(o1: Option<T>, o2: Option<T>) -> Option<T>
where
    T: Ord,
{
    match (o1, o2) {
        (Some(v1), Some(v2)) => min(v1, v2).into(),
        (o1, None) => o1,
        (None, o2) => o2,
    }
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! min {
    ($x: expr) => (Min::min(&$x));
    ($x: expr, $($z: expr),+) => (::std::cmp::min(Min::min(&$x), min!($($z),*)));
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! partial_min {
    ($x: expr) => (PartialMin::partial_min(&$x));
    ($x: expr, $($z: expr),+) => (min_with_partial(PartialMin::partial_min(&$x), partial_min!($($z),*)));
}

pub trait Max: PartialMax {
    fn max(&self) -> Self::Result;
}

pub trait PartialMax {
    type Result;
    fn partial_max(&self) -> Option<Self::Result>;
}

fn iter_partial_max<'a, T, PT, I>(iter: I) -> Option<T>
where
    T: Ord,
    PT: 'a + PartialMax<Result = T>,
    I: 'a + IntoIterator<Item = &'a PT>,
{
    iter.into_iter().filter_map(|x| x.partial_max()).max()
}

impl_collection_util!(
    PartialMax::partial_max -> Option where Ord { iter_partial_max },
    [Option, Slice, Vec, HashSet]
);

pub fn max_with_partial<T>(o1: Option<T>, o2: Option<T>) -> Option<T>
where
    T: Ord,
{
    match (o1, o2) {
        (Some(v1), Some(v2)) => max(v1, v2).into(),
        (o1, None) => o1,
        (None, o2) => o2,
    }
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! max {
    ($x: expr) => (Max::max(&$x));
    ($x: expr, $($z: expr),+) => (::std::cmp::max(Max::max(&$x), max!($($z),*)));
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! partial_max {
    ($x: expr) => (PartialMax::partial_max(&$x));
    ($x: expr, $($z: expr),+) => (max_with_partial(PartialMax::partial_max(&$x), partial_max!($($z),*)));
}

pub trait AutoSum {
    type Result;
    fn sum(&self) -> Self::Result;
}

fn iter_auto_sum<'a, T, ST, I>(iter: I) -> T
where
    T: Sum,
    ST: 'a + AutoSum<Result = T>,
    I: 'a + IntoIterator<Item = &'a ST>,
{
    iter.into_iter().map(|x| x.sum()).sum()
}

impl_collection_util!(
    AutoSum::sum -> Id where Sum { iter_auto_sum },
    [Option, Slice, Vec, HashSet]
);

#[allow(unused_macros)]
#[macro_export]
macro_rules! sum {
    ($x: expr) => (AutoSum::sum(&$x));
    ($x: expr, $($z: expr),+) => (AutoSum::sum(&$x) + sum!($($z),*));
}

pub trait AutoProduct {
    type Result;
    fn product(&self) -> Self::Result;
}

fn iter_auto_product<'a, T, ST, I>(iter: I) -> T
where
    T: Product,
    ST: 'a + AutoProduct<Result = T>,
    I: 'a + IntoIterator<Item = &'a ST>,
{
    iter.into_iter().map(|x| x.product()).product()
}

impl_collection_util!(
    AutoProduct::product -> Id where Product { iter_auto_product },
    [Option, Slice, Vec, HashSet]
);

#[allow(unused_macros)]
#[macro_export]
macro_rules! product {
    ($x: expr) => (AutoProduct::product(&$x));
    ($x: expr, $($z: expr),+) => (AutoProduct::product(&$x) * product!($($z),*));
}

pub trait GenericInteger:
    Copy
    + Clone
    + Eq
    + PartialEq
    + Ord
    + PartialOrd
    + Hash
    + FromStr
    + Display
    + Debug
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + MulAssign
    + Div<Output = Self>
    + DivAssign
    + Rem<Output = Self>
    + RemAssign
{
    fn zero() -> Self;
    fn one() -> Self;
    fn is_odd(&self) -> bool;
    fn is_even(&self) -> bool;
}

#[doc(hidden)]
macro_rules! implement_generic_integer {
    () => {};
    ($t:ty $(, $r:ty)*) => {
        impl GenericInteger for $t {
            #[inline]
            fn zero() -> Self { 0 }

            #[inline]
            fn one() -> Self { 1 }

            #[inline]
            fn is_odd(&self) -> bool { self % 2 == 1 }

            #[inline]
            fn is_even(&self) -> bool { self % 2 == 0 }
        }

        impl PartialMin for $t {
            type Result = $t;

            #[inline]
            fn partial_min(&self) -> Option<Self::Result> {
                self.clone().into()
            }
        }

        impl Min for $t {
            #[inline]
            fn min(&self) -> Self::Result {
                self.clone()
            }
        }

        impl PartialMax for $t {
            type Result = $t;

            #[inline]
            fn partial_max(&self) -> Option<Self::Result> {
                self.clone().into()
            }
        }

        impl Max for $t {
            #[inline]
            fn max(&self) -> Self::Result {
                self.clone()
            }
        }

        impl AutoSum for $t {
            type Result = $t;

            #[inline]
            fn sum(&self) -> Self {
                self.clone()
            }
        }

        impl AutoProduct for $t {
            type Result = $t;

            #[inline]
            fn product(&self) -> Self {
                self.clone()
            }
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
    gcd_lcm(a, b).1
}

#[inline]
pub fn gcd_lcm<T>(a: T, b: T) -> (T, T)
where
    T: GenericInteger,
{
    if a == T::zero() && b == T::zero() {
        return (T::zero(), T::zero());
    }
    let gcd = gcd(a, b);
    let lcm = a * (b / gcd);
    return (gcd, lcm);
}

/// O(√N)
#[allow(dead_code)]
pub fn prime_factorize(n: usize) -> HashMap<usize, usize> {
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

const INC: [usize; 8] = [4, 2, 4, 2, 4, 6, 2, 6];

// https://memo.sugyan.com/entry/2021/02/06/021949
/// O(N log(logN) )
#[allow(dead_code)]
pub fn eratosthenes_sieve(n: usize) -> Vec<usize> {
    if n < 7 {
        return [2, 3, 5]
            .iter()
            .filter_map(|&x| (x <= n).then_some_(x))
            .collect();
    }
    let nf = n as f64;
    let mut primes = Vec::with_capacity((nf / nf.ln() * 1.2).floor() as usize);
    primes.push(2);
    primes.push(3);
    primes.push(5);
    let mut unmarked_numbers = vec![true; n + 1];

    // Wheel factorization
    let mut p = 7 - INC.last().unwrap();
    for i in INC.len() - 1.. {
        p += INC[i % INC.len()];

        if p > n {
            break;
        }

        if !unmarked_numbers[p] {
            continue;
        }

        primes.push(p);
        for px in (p * p..=n).step_by(p) {
            unmarked_numbers[px] = false;
        }
    }

    primes
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

pub trait Then: Into<bool> {
    fn then_<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> T,
    {
        if self.into() {
            Some(f())
        } else {
            None
        }
    }
}

impl Then for bool {}

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

#[allow(unused_macros)]
macro_rules! dbg_raw {
    () => {
        #[cfg(debug_assertions)]
        eprintln!();
    };
    ($a:expr) => {
        #[cfg(debug_assertions)]
        eprintln!("{:?}", $a);
    };
    ($a:expr, $($b:expr),+ $(,)*) => {
        #[cfg(debug_assertions)]
        eprint!("{:?}", $a);

        dbg_raw!($($b),+);
    };
}

// From https://qiita.com/hatoo@github/items/fa14ad36a1b568d14f3e
#[derive(PartialEq, PartialOrd)]
struct Total<T>(T);

impl<T: PartialEq> Eq for Total<T> {}

impl<T: PartialOrd> Ord for Total<T> {
    fn cmp(&self, other: &Total<T>) -> Ordering {
        self.0.partial_cmp(&other.0).unwrap()
    }
}

pub fn index_to_ascii_gen(base: char) -> impl Fn(usize) -> char {
    move |index| (index as u8 + base as u8) as char
}

pub fn ascii_to_index_gen(base: char) -> impl Fn(char) -> usize {
    move |ascii| ascii as usize - base as usize
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default)]
pub struct Point2d<T> {
    pub x: T,
    pub y: T,
}

pub mod modular {
    //! Modular
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_modular.rs

    use super::{AutoProduct, AutoSum, GenericInteger, Max, Min, PartialMax, PartialMin, ThenSome};
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

    impl<M> PartialMin for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        type Result = PrimeModularUsize<M>;

        #[inline]
        fn partial_min(&self) -> Option<Self::Result> {
            self.clone().into()
        }
    }

    impl<M> Min for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn min(&self) -> Self::Result {
            self.clone()
        }
    }

    impl<M> PartialMax for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        type Result = PrimeModularUsize<M>;

        #[inline]
        fn partial_max(&self) -> Option<Self::Result> {
            self.clone().into()
        }
    }

    impl<M> Max for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        #[inline]
        fn max(&self) -> Self::Result {
            self.clone()
        }
    }

    impl<M> AutoSum for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        type Result = PrimeModularUsize<M>;

        #[inline]
        fn sum(&self) -> Self {
            self.clone()
        }
    }

    impl<M> AutoProduct for PrimeModularUsize<M>
    where
        M: ModuloExt,
    {
        type Result = PrimeModularUsize<M>;

        #[inline]
        fn product(&self) -> Self {
            self.clone()
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

pub mod binary_indexed_tree {
    //! BinaryIndexedTree
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_binary_indexed_tree.rs

    mod range {
        use std::ops::{Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeTo};

        /// The range that inclusive bounds are prohibited.
        pub trait BinaryIndexedTreeSumRange: RangeBounds<usize> {
            fn to_range(&self, unbounded_end: usize) -> Range<usize> {
                let start = match self.start_bound() {
                    Bound::Unbounded => 0,
                    Bound::Included(&n) => n,
                    Bound::Excluded(&n) => n + 1,
                };
                let end = match self.end_bound() {
                    Bound::Unbounded => unbounded_end,
                    Bound::Included(&n) => n + 1,
                    Bound::Excluded(&n) => n,
                };

                start..end
            }
        }
        impl BinaryIndexedTreeSumRange for RangeFull {}
        impl BinaryIndexedTreeSumRange for RangeFrom<usize> {}
        impl BinaryIndexedTreeSumRange for RangeTo<usize> {}
        impl BinaryIndexedTreeSumRange for Range<usize> {}
        impl BinaryIndexedTreeSumRange for (Bound<usize>, Bound<usize>) {}
        impl BinaryIndexedTreeSumRange for RangeFrom<&usize> {}
        impl BinaryIndexedTreeSumRange for RangeTo<&usize> {}
        impl BinaryIndexedTreeSumRange for Range<&usize> {}
        impl<'a> BinaryIndexedTreeSumRange for (Bound<&'a usize>, Bound<&'a usize>) {}
    }

    use super::GenericInteger;
    use std::ops::{Bound, Range, RangeBounds};

    pub struct BinaryIndexedTree1d<GI: GenericInteger>(Vec<GI>);

    impl<GI: GenericInteger> BinaryIndexedTree1d<GI> {
        pub fn new_with_zeros(size: usize) -> Self {
            Self(vec![GI::zero(); size])
        }

        /// O( N logN )
        pub fn new_with_slice(data: &[GI]) -> Self {
            let mut s = Self::new_with_zeros(data.len());

            for (i, data_i) in data.iter().enumerate() {
                s.add_value_at(i, *data_i);
            }

            s
        }

        /// O(logN)
        pub fn add_value_at(&mut self, index: usize, value: GI) {
            assert!(index < self.0.len());

            let mut current = index;
            while current < self.0.len() {
                self.0[current] += value;
                current |= current + 1 // move to parent
            }
        }

        /// O(logN)
        pub fn sum_in(&self, range: impl RangeBounds<usize>) -> GI {
            let range = Self::normalize_range(range, self.0.len());

            self.sum_until(range.end) - self.sum_until(range.start)
        }

        #[inline]
        fn normalize_range(range: impl RangeBounds<usize>, unbounded_end: usize) -> Range<usize> {
            let start = match range.start_bound() {
                Bound::Unbounded => 0,
                Bound::Included(&n) => n,
                Bound::Excluded(&n) => n + 1,
            };
            let end = match range.end_bound() {
                Bound::Unbounded => unbounded_end,
                Bound::Included(&n) => n + 1,
                Bound::Excluded(&n) => n,
            };

            start..end
        }

        fn sum_until(&self, to: usize) -> GI {
            if to == 0 {
                return GI::zero();
            }

            let mut result = GI::zero();
            let mut current = to;
            while {
                current -= 1;
                result += self.0[current];

                current &= current + 1; // to parent's elder sibling

                current > 0
            } {}

            result
        }
    }
}

// -- end of helpers

fn main() {
    use std::io::*;

    let stdio = stdin();
    let input = stdio.lock();

    let mut stdout = stdout();
    let output = BufWriter::new(stdout.lock());

    process(input, output).expect("Should not emit error");
    stdout.flush().unwrap();
}

#[allow(non_snake_case, unused_mut, unused_variables)]
fn process<R, W>(reader: R, mut writer: W) -> std::io::Result<()>
where
    R: std::io::BufRead,
    W: std::io::Write,
{
    let mut _handler = prepare_input! { stdin = reader };
    #[allow(unused_macros)]
    macro_rules! input {
        ($($r:tt)*) => {
            input_original! { handler = _handler; $($r)* }
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
        modulo!(998244353 as ModSub1Mil);

        input! {
            n: usize,
            a: [usize; n],
        }

        // after checking editorial

        let map = {
            let set = BTreeSet::from_iter(a.iter());
            let mut map = HashMap::new();
            for (i, &a_i) in set.iter().enumerate() {
                map.insert(*a_i, i);
            }
            map
        };

        let mut tree = binary_indexed_tree::BinaryIndexedTree1d::new_with_zeros(map.len());

        let mut sum = ModSub1Mil::zero();
        for (i, a_i) in a.iter().enumerate() {
            let a_i = map[a_i];

            sum += tree.sum_in(..=a_i) * ModSub1Mil::new(2).pow(i);

            tree.add_value_at(a_i, ModSub1Mil::new(2).pow(i + 1).reciprocal().unwrap());
        }

        println!("{}", sum);
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
1 2 1
",
            "3"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
3
1 2 2
",
            "4"
        );
    }

    #[test]
    fn sample3() {
        assert_judge!(
            process,
            "
3
3 2 1
",
            "0"
        );
    }

    #[test]
    fn sample4() {
        assert_judge!(
            process,
            "
10
198495780 28463047 859606611 212983738 946249513 789612890 782044670 700201033 367981604 302538501
",
            "830"
        );
    }
}
