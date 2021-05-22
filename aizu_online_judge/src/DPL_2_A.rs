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

// From https://github.com/tanakh/competitive-rs/blob/d5f51f01a6f85ddbebec4cfcb601746bee727181/src/lib.rs#L1-L92
//   and modified by this file author
macro_rules! input {
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

pub mod bit {
    use super::{NodeIndex0Based, Quantity};
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
        pub fn includes(&self, index: NodeIndex0Based) -> bool {
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
        pub fn excluded_set(&self, index: NodeIndex0Based) -> Self {
            Self::new(self.size, self.value & !(0b1 << index))
        }

        #[inline]
        pub fn appended_set(&self, index: NodeIndex0Based) -> Self {
            Self::new(self.size, self.value | (0b1 << index))
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
        pub fn combination(&self) -> Quantity {
            0b1 << self.size as u32
        }

        pub fn from_indices_iter<I>(&self, iter: I) -> BitBasedSet
        where
            I: Iterator<Item = NodeIndex0Based>,
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
    use bit::BitBasedSet;

    input! {
        stdin = reader;
        v: Quantity, e: Quantity,
        std: [(NodeIndex0Based, NodeIndex0Based, usize); e],
    }

    let mut edges = HashMap::new();
    for &(src, dest, length) in std.iter() {
        edges.entry(src).or_insert(vec![]).push((dest, length));
    }

    fn search_dp(
        v: Quantity,
        edges: &HashMap<NodeIndex0Based, Vec<(NodeIndex0Based, usize)>>,
    ) -> Option<usize> {
        fn inner(
            edges: &HashMap<NodeIndex0Based, Vec<(NodeIndex0Based, usize)>>,
            dp: &mut Vec<Vec<Option<usize>>>,
            nodes: BitBasedSet,
            current_node: NodeIndex0Based,
        ) -> Option<usize> {
            if nodes.is_empty() {
                return (current_node == 0).then_some_(0);
            }

            if !nodes.includes(current_node) {
                return None;
            }

            let result = dp[nodes.dump()][current_node];
            if result.is_some() {
                return result;
            }

            let mut results = vec![];
            for &(dest, length) in edges.get(&current_node).unwrap_or(&vec![]).iter() {
                let v =
                    inner(edges, dp, nodes.excluded_set(current_node), dest).map(|r| r + length);
                results.push(v);
            }

            let result = results.iter().filter_map(|&r| r).min();
            dp[nodes.dump()][current_node] = result;
            result
        }

        let bbs_gen = BitBasedSet::generator_of(v);
        let mut dp = nested_vec![None; bbs_gen.combination(); v];
        inner(edges, &mut dp, bbs_gen.universal_set(), 0)
    }

    let result = search_dp(v, &edges);

    if let Some(result) = result {
        writeln!(writer, "{}", result)?;
    } else {
        writeln!(writer, "-1")?;
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
4 6
0 1 2
1 2 3
1 3 9
2 0 1
2 3 6
3 2 4
",
            "16"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
3 3
0 1 1
1 2 1
0 2 1
",
            "-1"
        );
    }
}
