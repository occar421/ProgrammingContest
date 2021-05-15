// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::io;
use std::io::{BufRead, BufWriter, Result, Write};
use std::ops::{Div, Mul, Rem};
use std::str::FromStr;

pub type NodeIndex0Based = usize;
pub type NodeIndex1Based = usize;
pub type Quantity = usize;

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
    + Rem<Output = Self>
    + Div<Output = Self>
    + Mul<Output = Self>
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
    input! {
        stdin = reader;
        h: usize, w: usize, k: usize, v: usize,
        a: [[usize; w]; h],
    }

    let grid_cost = k;
    let budget = v;

    let cum_sum = {
        let mut cum_sum = vec![vec![0; w + 1]; h + 1];

        for j in 0..w {
            for i in 0..h {
                cum_sum[i + 1][j + 1] =
                    cum_sum[i + 1][j] + cum_sum[i][j + 1] - cum_sum[i][j] + a[i][j] + grid_cost;
            }
        }

        cum_sum
    };

    let mut max_area = 0;
    for i_start in 0..h {
        for i_end in i_start + 1..=h {
            for j_start in 0..w {
                for j_end in j_start + 1..=w {
                    let area_cost = cum_sum[i_end][j_end] + cum_sum[i_start][j_start]
                        - cum_sum[i_end][j_start]
                        - cum_sum[i_start][j_end];
                    if area_cost <= budget {
                        let area = (i_end - i_start) * (j_end - j_start);
                        max_area = max_area.max(area);
                    }
                }
            }
        }
    }

    writeln!(writer, "{}", max_area)?;

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
1 1 200 500
300
",
            "1"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
1 8 10 200
30 40 10 20 30 40 10 20
",
            "6"
        );
    }

    #[test]
    fn sample3() {
        assert_judge!(
            process,
            "
5 5 10 17
12 19 25 13 25
14 16 18 11 10
19 17 24 26 12
23 11 16 19 14
18 23 27 11 16
",
            "0"
        );
    }

    #[test]
    fn sample4() {
        assert_judge!(
            process,
            "
4 7 10 240
17 12 15 18 19 15 23
22 12 41 16 27 10 10
15 69 18 11 10 23 15
12 20 13 12 17 18 15
",
            "9"
        );
    }
}
