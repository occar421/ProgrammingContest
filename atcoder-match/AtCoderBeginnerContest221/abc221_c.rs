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

pub mod bit {
    //! Bit
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_bit.rs

    use std::marker::PhantomData;
    use std::ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Index, Not, Shl, ShlAssign,
        Shr, ShrAssign,
    };

    pub trait BitSizeExt: Clone + Copy {
        fn size() -> usize;
    }

    #[macro_export]
    macro_rules! bit_set {
        ($num: literal as $alias: ident) => {
            bit_size!($num in bit as $alias);
        };
        ($num: literal in $module_base: path as $alias: ident) => {
            #[derive(Debug, Clone, Copy, Default, PartialOrd, Ord, PartialEq, Eq)]
            pub struct BitSize;

            use $module_base as base;

            impl base::BitSizeExt for BitSize {
                #[inline]
                fn size() -> usize {
                    $num
                }
            }

            type $alias = base::BitSet<BitSize>;
        };
    }

    #[derive(Clone)]
    pub struct BitSet<S>
    where
        S: BitSizeExt,
    {
        // little endian
        chunks: Vec<u64>,
        size: PhantomData<S>,
    }

    const CHUNK_BIT_SIZE: usize = 64;
    const CHUNK_INDEX_MASK: usize = 63;
    // 2 ^ 6 = 64
    const CHUNK_BIT_LENGTH: usize = 6;

    impl<S> BitSet<S>
    where
        S: BitSizeExt,
    {
        pub fn zero() -> Self {
            Self {
                chunks: vec![0; (S::size() + (CHUNK_BIT_SIZE - 1)) / CHUNK_BIT_SIZE],
                size: PhantomData,
            }
        }

        pub fn new(value: impl Into<u64>) -> Self {
            let value = value.into();

            let mut v = Self::zero().clone();

            v.chunks[0] = value;

            v.chomp();
            v
        }

        pub fn set(&mut self, index: usize, value: bool) {
            assert!(index < S::size());

            let target_bit = 1 << (index & CHUNK_INDEX_MASK);

            if value {
                self.chunks[index >> CHUNK_BIT_LENGTH] |= target_bit;
            } else {
                self.chunks[index >> CHUNK_BIT_LENGTH] &= !target_bit;
            }
        }

        pub fn count_ones(&self) -> u32 {
            self.chunks.iter().map(|x| x.count_ones()).sum()
        }

        fn chomp(&mut self) {
            let r = S::size() & CHUNK_INDEX_MASK;
            if let Some(bits) = self.chunks.last_mut() {
                let d = CHUNK_BIT_SIZE - r;
                // erase "overflowed" bits
                *bits = (*bits << d) >> d;
            }
        }
    }

    impl<S> Not for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn not(self) -> Self::Output {
            let mut v = self.clone();
            for piece in v.chunks.iter_mut() {
                *piece = !*piece;
            }
            v.chomp();
            v
        }
    }

    impl<S> BitAnd<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn bitand(self, rhs: BitSet<S>) -> Self::Output {
            let mut v = self.clone();
            v &= rhs;
            v
        }
    }

    impl<S> BitAndAssign<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        fn bitand_assign(&mut self, rhs: BitSet<S>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece &= rhs_piece;
            }
        }
    }

    impl<S> BitOr<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn bitor(self, rhs: BitSet<S>) -> Self::Output {
            let mut v = self.clone();
            v |= rhs;
            v
        }
    }

    impl<S> BitOrAssign<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        fn bitor_assign(&mut self, rhs: BitSet<S>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece |= rhs_piece;
            }
            self.chomp();
        }
    }

    impl<S> BitXor<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn bitxor(self, rhs: BitSet<S>) -> Self::Output {
            let mut v = self.clone();
            v ^= rhs;
            v
        }
    }

    impl<S> BitXorAssign<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        fn bitxor_assign(&mut self, rhs: BitSet<S>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece ^= rhs_piece;
            }
        }
    }

    impl<S> Shl<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn shl(self, rhs: usize) -> Self::Output {
            let mut v = self.clone();
            v <<= rhs;
            v
        }
    }

    impl<S> ShlAssign<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
        fn shl_assign(&mut self, rhs: usize) {
            let chunk_shifts = rhs >> CHUNK_BIT_LENGTH;
            let shifts_in_chunk = rhs & CHUNK_INDEX_MASK;

            let chunks_length = self.chunks.len();

            if chunk_shifts >= chunks_length {
                // "overflow"
                for x in &mut self.chunks {
                    *x = 0;
                }
                return;
            }

            if shifts_in_chunk == 0 {
                for i in (chunk_shifts..chunks_length).rev() {
                    self.chunks[i] = self.chunks[i - chunk_shifts];
                }
            } else {
                for i in (chunk_shifts + 1..chunks_length).rev() {
                    self.chunks[i] = (self.chunks[i - chunk_shifts] << shifts_in_chunk)
                        | (self.chunks[i - chunk_shifts - 1] >> (CHUNK_BIT_SIZE - shifts_in_chunk));
                }
                self.chunks[chunk_shifts] = self.chunks[0] << shifts_in_chunk;
            }

            // jack up
            for x in &mut self.chunks[..chunk_shifts] {
                *x = 0;
            }

            self.chomp();
        }
    }

    impl<S> Shr<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn shr(self, rhs: usize) -> Self::Output {
            let mut v = self.clone();
            v >>= rhs;
            v
        }
    }

    impl<S> ShrAssign<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
        fn shr_assign(&mut self, rhs: usize) {
            let chunk_shifts = rhs >> CHUNK_BIT_LENGTH;
            let shifts_in_chunk = rhs & CHUNK_INDEX_MASK;

            let chunks_length = self.chunks.len();

            if chunk_shifts >= chunks_length {
                // 0b1's disappear
                for x in &mut self.chunks {
                    *x = 0;
                }
                return;
            }

            if shifts_in_chunk == 0 {
                for i in 0..(chunks_length - chunk_shifts) {
                    self.chunks[i] = self.chunks[i + chunk_shifts];
                }
            } else {
                for i in 0..(chunks_length - chunk_shifts - 1) {
                    self.chunks[i] = (self.chunks[i + chunk_shifts] >> shifts_in_chunk)
                        | (self.chunks[i + chunk_shifts + 1] << (CHUNK_BIT_SIZE - shifts_in_chunk));
                }
                self.chunks[chunks_length - chunk_shifts - 1] =
                    self.chunks[chunks_length - 1] >> shifts_in_chunk;
            }

            for x in &mut self.chunks[(chunks_length - chunk_shifts)..] {
                *x = 0;
            }
        }
    }

    const TRUE_REF: &bool = &true;
    const FALSE_REF: &bool = &false;

    impl<S> Index<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = bool;

        fn index(&self, index: usize) -> &Self::Output {
            [FALSE_REF, TRUE_REF][((self.chunks[index >> 6] >> (index & 63)) & 0b1) as usize]
        }
    }

    #[derive(Copy, Clone)]
    pub struct BitBasedSet {
        size: usize,
        value: usize,
    }

    impl BitBasedSet {
        fn new(size: usize, value: usize) -> Self {
            Self { size, value }
        }

        pub fn generator_of(size: usize) -> BitBasedSetGenerator {
            BitBasedSetGenerator::new(size)
        }

        #[inline]
        pub fn dump(&self) -> usize {
            self.value
        }

        #[inline]
        pub fn includes(&self, index: usize) -> bool {
            self.value & (0b1 << index) > 0
        }

        #[inline]
        pub fn is_empty(&self) -> bool {
            self.value.count_ones() == 0
        }

        #[inline]
        pub fn complement(&self) -> Self {
            Self::new(
                self.size,
                self.value ^ BitBasedSetGenerator::new(self.size).universal_set().value,
            )
        }

        #[inline]
        pub fn excluded_set(&self, index: usize) -> Self {
            Self::new(self.size, self.value & !(0b1 << index))
        }

        #[inline]
        pub fn appended_set(&self, index: usize) -> Self {
            Self::new(self.size, self.value | (0b1 << index))
        }
    }

    pub struct BitBasedSetIntoIter {
        set: BitBasedSet,
        current: usize,
    }

    impl Iterator for BitBasedSetIntoIter {
        type Item = usize;

        fn next(&mut self) -> Option<Self::Item> {
            let mut current = self.current;
            while self.set.size >= current {
                if self.set.includes(current) {
                    self.current = current + 1;
                    return Some(current);
                }
                current += 1;
            }
            return None;
        }
    }

    impl IntoIterator for BitBasedSet {
        type Item = usize;
        type IntoIter = BitBasedSetIntoIter;

        fn into_iter(self) -> Self::IntoIter {
            BitBasedSetIntoIter {
                set: self,
                current: 0,
            }
        }
    }

    pub struct BitBasedSetGenerator {
        size: usize,
    }

    impl BitBasedSetGenerator {
        fn new(size: usize) -> Self {
            Self { size }
        }

        #[inline]
        pub fn universal_set(&self) -> BitBasedSet {
            BitBasedSet::new(self.size, (0b1 << self.size) - 1)
        }

        #[inline]
        pub fn empty_set(&self) -> BitBasedSet {
            BitBasedSet::new(self.size, 0)
        }

        #[inline]
        pub fn combination(&self) -> usize {
            0b1 << self.size as u32
        }

        #[inline]
        pub fn from(&self, v: usize) -> BitBasedSet {
            BitBasedSet::new(self.size, v)
        }

        pub fn by_indices_iter<I>(&self, iter: I) -> BitBasedSet
        where
            I: Iterator<Item = usize>,
        {
            let mut v = 0;
            for i in iter {
                v |= 0b1 << i;
            }
            BitBasedSet::new(self.size, v)
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
        input! {
            n: String,
        }

        let bg = bit::BitBasedSet::generator_of(n.len());

        let size = 0b1 << n.len();

        let mut max = 0;
        let mut n: Vec<_> = n.chars().collect();
        for i in 1..size - 1 {
            let mut lefts = vec![];
            let mut rights = vec![];
            let bits = bg.from(i);
            for j in 0..n.len() {
                let char = n[j].to_digit(10).unwrap() as usize;
                if bits.includes(j) {
                    lefts.push(char);
                } else {
                    rights.push(char);
                }
            }
            lefts.sort_unstable();
            let left: usize = lefts
                .iter()
                .enumerate()
                .map(|(i, &v)| 10usize.pow(i as u32) * v)
                .sum();

            rights.sort_unstable();
            let right: usize = rights
                .iter()
                .enumerate()
                .map(|(i, &v)| 10usize.pow(i as u32) * v)
                .sum();

            max = max!(max, left * right);
        }

        println!("{}", max);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "123", "63");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "1010", "100");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "998244353", "939337176");
    }
}
