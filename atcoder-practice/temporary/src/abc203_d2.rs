// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::collections::HashMap;
use std::fmt::{Debug, Display};
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
    + Ord
    + PartialOrd
    + Hash
    + FromStr
    + Display
    + Debug
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

pub mod cumulative_sum {
    //! CumulativeSum
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_cumulative_sum.rs

    mod range {
        use std::ops::{Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeTo};

        /// The range that inclusive bounds are prohibited.
        pub trait CumulativeSumRange: RangeBounds<usize> {
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
        impl CumulativeSumRange for RangeFull {}
        impl CumulativeSumRange for RangeFrom<usize> {}
        impl CumulativeSumRange for RangeTo<usize> {}
        impl CumulativeSumRange for Range<usize> {}
        impl CumulativeSumRange for (Bound<usize>, Bound<usize>) {}
        impl CumulativeSumRange for RangeFrom<&usize> {}
        impl CumulativeSumRange for RangeTo<&usize> {}
        impl CumulativeSumRange for Range<&usize> {}
        impl<'a> CumulativeSumRange for (Bound<&'a usize>, Bound<&'a usize>) {}
    }

    use super::{GenericInteger, Length};

    pub struct CumulativeSum1d<GI>
    where
        GI: GenericInteger,
    {
        cum_sum: Vec<GI>,
        source_length: Length,
    }

    impl<GI> CumulativeSum1d<GI>
    where
        GI: GenericInteger,
    {
        /// O( N )
        #[inline]
        pub fn new(source_length: Length, source: &Vec<GI>) -> Self {
            Self::new_with_evaluator(source_length, |i| source[i])
        }

        /// O( N )
        pub fn new_with_evaluator<F>(source_length: Length, evaluator: F) -> Self
        where
            F: Fn(usize) -> GI,
        {
            let mut cum_sum = nested_vec![GI::zero(); source_length + 1];

            for i in 0..source_length {
                cum_sum[i + 1] = cum_sum[i] + evaluator(i);
            }

            Self {
                cum_sum,
                source_length,
            }
        }

        /// O(1)
        ///
        /// # Examples
        ///
        ///     source: a b c
        ///     range: 0 1 2 3
        ///
        /// `0..2` => `a + b`
        ///
        pub fn sum_in(&self, range: impl range::CumulativeSumRange) -> GI {
            let range = range.to_range(self.source_length);

            self.cum_sum[range.end] - self.cum_sum[range.start]
        }

        pub fn dump(&self) -> &[GI] {
            &self.cum_sum
        }
    }

    pub struct CumulativeSum2d<GI>
    where
        GI: GenericInteger,
    {
        cum_sum: Vec<Vec<GI>>,
        source_height: Length,
        source_width: Length,
    }

    impl<GI> CumulativeSum2d<GI>
    where
        GI: GenericInteger,
    {
        #[inline]
        /// O(N^2)
        pub fn new(source_height: Length, source_width: Length, source: &Vec<Vec<GI>>) -> Self {
            Self::new_with_evaluator(source_height, source_width, |i, j| source[i][j])
        }

        /// O(N^2)
        pub fn new_with_evaluator<F>(
            source_height: Length,
            source_width: Length,
            evaluator: F,
        ) -> Self
        where
            F: Fn(usize, usize) -> GI,
        {
            let mut cum_sum = nested_vec![GI::zero(); source_height + 1; source_width + 1];

            for i in 0..source_height {
                for j in 0..source_width {
                    cum_sum[i + 1][j + 1] =
                        cum_sum[i + 1][j] + cum_sum[i][j + 1] - cum_sum[i][j] + evaluator(i, j);
                }
            }

            Self {
                cum_sum,
                source_height,
                source_width,
            }
        }

        /// O(1)
        ///
        /// # Examples
        ///     source:   a b c
        ///               d e f
        ///               g h i
        ///     h_range: 0 1 2 3
        ///
        /// `0..2, 0..2` => `a + b + d + e`
        ///
        pub fn sum_in(
            &self,
            vertical_range: impl range::CumulativeSumRange,
            horizontal_range: impl range::CumulativeSumRange,
        ) -> GI {
            let vertical_range = vertical_range.to_range(self.source_height);
            let horizontal_range = horizontal_range.to_range(self.source_width);

            self.cum_sum[vertical_range.end][horizontal_range.end]
                + self.cum_sum[vertical_range.start][horizontal_range.start]
                - self.cum_sum[vertical_range.end][horizontal_range.start]
                - self.cum_sum[vertical_range.start][horizontal_range.end]
        }
    }
}

pub mod binary_search {
    use super::GenericInteger;
    use std::ops::{Range, RangeInclusive};

    pub struct TFBorderResult<GI: GenericInteger> {
        pub max_true: Option<GI>,
        pub min_false: Option<GI>,
    }

    pub struct FTBorderResult<GI: GenericInteger> {
        pub max_false: Option<GI>,
        pub min_true: Option<GI>,
    }

    pub trait BinaryBorderSearch<Item, GI: GenericInteger> {
        /// O( log(N) )
        /// Should be sorted
        fn search_true_false_border(&self, predicate: impl Fn(&Item) -> bool)
            -> TFBorderResult<GI>;

        /// O( log(N) )
        /// Should be sorted
        #[inline]
        fn search_false_true_border(
            &self,
            predicate: impl Fn(&Item) -> bool,
        ) -> FTBorderResult<GI> {
            let result = self.search_true_false_border(|item| !predicate(item));
            FTBorderResult {
                max_false: result.max_true,
                min_true: result.min_false,
            }
        }
    }

    impl<Item> BinaryBorderSearch<Item, usize> for [Item] {
        /// O( log(N) )
        /// ```
        /// # use templates::snippet_binary_search::binary_search::BinaryBorderSearch;
        /// let vec = vec![1, 2, 3];
        /// let result = vec.search_true_false_border(|&x| x > 1);
        /// assert_eq!(result.max_true, 0);
        /// assert_eq!(result.min_false, 1);
        /// ```
        #[inline]
        fn search_true_false_border(
            &self,
            predicate: impl Fn(&Item) -> bool,
        ) -> TFBorderResult<usize> {
            (0..self.len()).search_true_false_border(|&i| predicate(&self[i]))
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for Range<GI> {
        /// O( log(high-low) )
        /// ```
        /// # use templates::snippet_binary_search::binary_search::BinaryBorderSearch;
        /// let range = 1..4;
        /// let result = range.search_true_false_border(|&x| x <= 1);
        /// assert_eq!(result.max_true, 1);
        /// assert_eq!(result.min_false, 2);
        /// ```
        fn search_true_false_border(&self, predicate: impl Fn(&GI) -> bool) -> TFBorderResult<GI> {
            if self.start >= self.end {
                return TFBorderResult {
                    max_true: None,
                    min_false: None,
                };
            }

            let first = self.start;
            if !predicate(&first) {
                return TFBorderResult {
                    max_true: None,
                    min_false: first.into(),
                };
            }

            let mut known_max_true = first;
            let mut known_min_false = self.end;
            while known_min_false - known_max_true > GI::one() {
                let mid =
                    known_max_true + (known_min_false - known_max_true) / (GI::one() + GI::one());
                if predicate(&mid) {
                    known_max_true = mid;
                } else {
                    known_min_false = mid;
                }
            }

            // all true
            if known_min_false == self.end {
                TFBorderResult {
                    max_true: (self.end - GI::one()).into(),
                    min_false: None,
                }
            } else {
                TFBorderResult {
                    max_true: known_max_true.into(),
                    min_false: known_min_false.into(),
                }
            }
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for Range<&GI> {
        #[inline]
        fn search_true_false_border(&self, predicate: impl Fn(&GI) -> bool) -> TFBorderResult<GI> {
            (*self.start..*self.end).search_true_false_border(predicate)
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for RangeInclusive<GI> {
        /// O( log(high-low) )
        /// ```
        /// # use templates::snippet_binary_search::binary_search::BinaryBorderSearch;
        /// let range = -1..=1;
        /// let result = range.search_true_false_border(|&x| x <= 1);
        /// assert_eq!(result.max_true, 1);
        /// assert_eq!(result.min_false, None);
        /// ```
        #[inline]
        fn search_true_false_border(&self, predicate: impl Fn(&GI) -> bool) -> TFBorderResult<GI> {
            (*self.start()..(*self.end() + GI::one())).search_true_false_border(predicate)
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for RangeInclusive<&GI> {
        #[inline]
        fn search_true_false_border(&self, predicate: impl Fn(&GI) -> bool) -> TFBorderResult<GI> {
            (**self.start()..(**self.end() + GI::one())).search_true_false_border(predicate)
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
        use binary_search::BinaryBorderSearch;
        use cumulative_sum::CumulativeSum2d;

        input! {
            n: Length, k: Length,
            a: [[usize; n]; n],
        }

        // after checking editorial

        let median_index = (k * k) / 2 + 1;
        let result = (0..=(10usize.pow(9))).search_false_true_border(|&x| {
            // O( N^2 )
            let cum_sum =
                CumulativeSum2d::new_with_evaluator(n, n, |i, j| if a[i][j] > x { 1 } else { 0 });

            for i in 0..=(n - k) {
                for j in 0..=(n - k) {
                    let n_larger_nums = cum_sum.sum_in(i..(i + k), j..(j + k));
                    if n_larger_nums < median_index {
                        return true;
                    }
                }
            } // O( (N-K)^2 )   K <= N

            false
        }); // O ( N^2 log(10^9) )

        println!("{}", result.min_true.unwrap_or(0));
    } // O ( N^2 log(10^9) )

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
3 2
1 7 0
5 8 11
10 4 2",
            "4"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
3 3
1 2 3
4 5 6
7 8 9",
            "5"
        );
    }

    #[test]
    fn sample_0() {
        assert_judge!(
            process,
            "
3 3
0 0 0
0 0 0
0 0 0",
            "0"
        );
    }
}
