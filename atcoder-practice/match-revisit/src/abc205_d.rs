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

pub mod binary_search {
    use super::GenericInteger;
    use std::ops::{Range, RangeInclusive};

    #[derive(Copy, Clone, Debug)]
    pub struct TFBorderResult<GI: GenericInteger> {
        pub max_true: Option<GI>,
        pub min_false: Option<GI>,
    }

    #[derive(Copy, Clone, Debug)]
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

        input! {
            n: Length, q: Length,
            a: [usize; n],
            k: [usize; q],
        }

        let mut counts = vec![0; n];
        for i in 0..a.len() {
            counts[i] = a[i] - (i + 1);
        } // O(N)

        for &k_i in k.iter() {
            // O( log(N) )
            let result = counts.search_false_true_border(|&x| k_i <= x);

            if result.max_false.is_none() {
                // below all checkpoints
                println!("{}", k_i);
            } else if let Some(min_true) = result.min_true {
                println!("{}", (a[min_true] - 1) - (counts[min_true] - k_i));
            } else {
                // above all checkpoints
                println!("{}", a.last().unwrap() + (k_i - counts.last().unwrap()));
            }
        } // O( Q log(N) )
    } // O( N + Q log(N) )

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
4 3
3 5 6 7
2
5
3",
            "
2
9
4"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
5 2
1 2 3 4 5
1
10",
            "
6
15"
        );
    }
}
