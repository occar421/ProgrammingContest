// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::collections::HashMap;
use std::fmt::Display;
use std::io;
use std::io::{BufRead, Result, Write};
use std::ops::{Div, Mul, Rem};
use std::str::FromStr;

// From https://qiita.com/tanakh/items/0ba42c7ca36cd29d0ac8
macro_rules! input {
    (source = $s:expr, $($r:tt)*) => {
        let mut iter = $s.split_whitespace();
        input_inner!{iter, $($r)*}
    };
    (stdin = $s:expr, $($r:tt)*) => {
        let s = {
            let mut s = String::new();
            $s.read_to_string(&mut s).unwrap();
            s
        };
        let mut iter = s.split_whitespace();
        input_inner!{iter, $($r)*}
    };
}

macro_rules! input_inner {
    ($iter:expr) => {};
    ($iter:expr, ) => {};

    ($iter:expr, $var:ident : $t:tt $($r:tt)*) => {
        let $var = read_value!($iter, $t);
        input_inner!{$iter $($r)*}
    };
}

macro_rules! read_value {
    ($iter:expr, ( $($t:tt),* )) => {
        ( $(read_value!($iter, $t)),* )
    };

    ($iter:expr, [ $t:tt ; $len:expr ]) => {
        (0..$len).map(|_| read_value!($iter, $t)).collect::<Vec<_>>()
    };

    ($iter:expr, chars) => {
        read_value!($iter, String).chars().collect::<Vec<char>>()
    };

    ($iter:expr, usize1) => {
        read_value!($iter, usize) - 1
    };

    ($iter:expr, $t:ty) => {
        $iter.next().unwrap_or_default().parse::<$t>().expect("Parse error")
    };
}

#[allow(unused_macros)]
macro_rules! assert_judge {
    ($method:ident, $input:expr, $expected:expr) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output).expect("Should not emit error");

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!(output, $expected);
    }};
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_output {
    ($method:ident, $input:expr) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output).expect("Should not emit error");

        String::from_utf8(output).expect("Not UTF-8")
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
                    // The reborrows below are intentional. Without them, the stack slot for the
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
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output).expect("Should not emit error");

        let output = String::from_utf8(output).expect("Not UTF-8");

        let actual: $t = output.parse().unwrap();
        let expected: $t = $expected.parse().unwrap();

        assert_eq_with_error!(actual, expected, $precision);
    }};
}

pub trait GenericInteger:
    Copy + PartialEq + FromStr + Display + Rem<Output = Self> + Div<Output = Self> + Mul<Output = Self>
{
    fn zero() -> Self;
}

macro_rules! dec_gi {
    () => {};
    ($t:ty $(, $r:ty)*) => {
        impl GenericInteger for $t {
            #[inline]
            fn zero() -> Self { 0 }
        }

        dec_gi![ $( $r ),* ];
    };
}

dec_gi![u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize];

#[allow(dead_code)]
pub fn gcd<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    if b == T::zero() {
        a
    } else {
        gcd(b, a % b)
    }
}

#[allow(dead_code)]
#[inline]
pub fn lcm<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    a / gcd(a, b) * b
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

trait ThenSome: Into<bool> {
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

    let output = io::stdout();

    process(input, output).expect("Should not emit error");
}

#[allow(non_snake_case)]
fn process<R, W>(mut reader: R, mut writer: W) -> Result<()>
where
    R: BufRead,
    W: Write,
{
    input! {
        stdin = reader,
        n: usize, m: usize
    }

    // after checking editor's note
    let mut empty_map = HashMap::new();
    let mut map = HashMap::new();
    for i in 1..=m {
        empty_map.insert(i, 0);
        map.insert(i, 1);
    }

    for _ in 1..n {
        let mut working_map = empty_map.clone();
        for i in 1..=m {
            let value = map.get(&i).unwrap().clone();
            for j in 1..=m {
                if i * j > m {
                    break;
                }
                *working_map.get_mut(&(i * j)).unwrap() += value;
            }
        }
        map = working_map;
    }

    write!(writer, "{}", map.values().sum::<usize>() % 998244353)?;

    Ok(())
}

struct MontgomeryModularMultiplication {
    n: usize,
    nb: usize,
    r2: usize,
    mask: usize,
    nr: usize,
}

impl MontgomeryModularMultiplication {
    fn new(n: usize) -> MontgomeryModularMultiplication {
        let nb = bit_length(n);
        // Rを、Nより大きい最小の2の冪乗数とする
        // R^2 mod n : この1回だけ除算が必要になる
        let r2 = (1 << (nb * 2)) % n;
        // Rを2の冪乗とすることで、mod Rをビットマスクで求められるようになる
        let mask = (1 << nb) - 1;

        // N * N' = -1 mod R となるN'の導出
        // Rを2の冪乗とすることで加算とビットシフトで求められるようになる
        let mut nr = 0;
        let mut t = 0;
        let mut vi = 1;
        for _ in 0..nb {
            if t & 1 == 0 {
                t += n;
                nr += vi;
            }
            t >>= 1;
            vi <<= 1;
        }

        MontgomeryModularMultiplication {
            n,
            nb,
            r2,
            mask,
            nr,
        }
    }

    fn reduction(&self, t: usize) -> usize {
        // モンゴメリリダクション
        let mut c = t * self.nr;
        c &= self.mask;
        c *= self.n;
        c += t;
        c >>= self.nb;
        if c >= self.n {
            c -= self.n;
        }
        return c;
    }

    fn mul(&self, a: usize, b: usize) -> usize {
        // a * b mod n を計算
        self.reduction(self.reduction(a * b) * self.r2)
    }

    fn exp(&self, a: usize, b: usize) -> usize {
        // a ^ b mod n を計算
        let mut p = self.reduction(a * self.r2);
        let mut x = self.reduction(self.r2);
        let mut y = b;
        while y != 0 {
            if y & 1 != 1 {
                x = self.reduction(x * p);
            }
            p = self.reduction(p * p);
            y >>= 1;
        }
        self.reduction(x)
    }
}

fn bit_length(n: usize) -> usize {
    (n as f64).log2().floor() as usize + 1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "3 4", "13");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "20 30", "71166");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "200000 200000", "835917264");
    }
}
