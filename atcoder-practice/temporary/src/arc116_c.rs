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

struct ModularCombinationGenerator {
    montgomery: MontgomeryExp2ModularMultiplication,
    factorials: Vec<usize>,
    reciprocal_factorials: Vec<usize>,
}

impl ModularCombinationGenerator {
    fn new(n_max: usize, modulo_number: usize) -> Self {
        let montgomery = MontgomeryExp2ModularMultiplication::new(modulo_number);

        let mut f = 1;
        let mut factorials = Vec::with_capacity(n_max + 1);
        factorials.push(1); // by 0!

        // calc from 1! to n!
        for i in 1..=n_max {
            f = montgomery.mul(f, i);
            factorials.push(f);
        }

        // reversed_factorial
        let mut reversed_r_f = Vec::with_capacity(n_max + 1);
        // calc n!^-1
        let mut inv = montgomery.exp(f, modulo_number - 2);
        reversed_r_f.push(inv);

        // calc from (n-1)!^-1 to 0!^-1
        for i in (1..=n_max).rev() {
            inv = montgomery.mul(inv, i);
            reversed_r_f.push(inv);
        }
        let reciprocal_factorials = {
            reversed_r_f.reverse();
            reversed_r_f
        };

        Self {
            montgomery,
            factorials,
            reciprocal_factorials,
        }
    }

    fn get(&self, n: usize, r: usize) -> usize {
        // n! * r!^-1 * (n-r)!^-1
        self.montgomery.mul(
            self.factorials[n],
            self.montgomery.mul(
                self.reciprocal_factorials[r],
                self.reciprocal_factorials[n - r],
            ),
        )
    }
}

struct MontgomeryExp2ModularMultiplication {
    /** N */
    n: usize,
    n_bit_length: usize,
    /** R^2 mod N */
    r_square: usize,
    /** bit mask for x mod R */
    mod_r_mask: usize,
    n_prime: usize,
}

impl MontgomeryExp2ModularMultiplication {
    fn new(n: usize) -> Self {
        if n % 2 == 0 {
            panic!("Precondition not met")
        }
        let n_bit_length = bit_length(n);
        let r_square = (1 << (n_bit_length * 2)) % n;
        let mod_r_mask = (1 << n_bit_length) - 1;

        let mut result = 0;
        let mut t = 0;
        for i in 0..n_bit_length {
            if t & 0x1 == 0x0 {
                t += n;
                result += 1 << i;
            }
            t >>= 1;
        }

        Self {
            n,
            n_bit_length,
            r_square,
            mod_r_mask,
            n_prime: result,
        }
    }

    fn do_reduction(&self, t: usize) -> usize {
        // t <- (T + (TN' mod R)N)/R
        let temp = self.div_r(t + self.mod_r(t * self.n_prime) * self.n);

        // if t >= N then return t - N else return t
        if temp >= self.n {
            temp - self.n
        } else {
            temp
        }
    }

    #[inline]
    fn mod_r(&self, x: usize) -> usize {
        x & self.mod_r_mask
    }

    #[inline]
    fn div_r(&self, x: usize) -> usize {
        x >> self.n_bit_length
    }

    /** a*b mod N */
    fn mul(&self, a: usize, b: usize) -> usize {
        // MR(MR(ab)R^2)
        self.do_reduction(self.do_reduction(a * b) * self.r_square)
    }

    /** a^b mod N */
    fn exp(&self, a: usize, b: usize) -> usize {
        let mut p = self.do_reduction(a * self.r_square);
        let mut x = self.do_reduction(self.r_square);
        for i in 0..bit_length(b) {
            if (b & (0x1 << i)) != 0x0 {
                x = self.do_reduction(x * p);
            }
            p = self.do_reduction(p * p);
        }
        self.do_reduction(x)
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

    #[test]
    fn montgomery() {
        let m19 = MontgomeryExp2ModularMultiplication::new(19);
        assert_eq!(m19.mul(7, 11), 7 * 11 % 19);
        assert_eq!(m19.exp(1, 0), 1usize.pow(0) % 19);
        assert_eq!(m19.exp(1, 1), 1usize.pow(1) % 19);
        assert_eq!(m19.exp(2, 2), 2usize.pow(2) % 19);
        assert_eq!(m19.exp(3, 3), 3usize.pow(3) % 19);
        assert_eq!(m19.exp(4, 4), 4usize.pow(4) % 19);
        assert_eq!(m19.exp(5, 5), 5usize.pow(5) % 19);
        assert_eq!(m19.exp(3, 5), 3usize.pow(5) % 19);
        assert_eq!(m19.exp(5, 3), 5usize.pow(3) % 19);

        let m25 = MontgomeryExp2ModularMultiplication::new(25);
        assert_eq!(m25.mul(7, 11), 7 * 11 % 25);
        assert_eq!(m25.exp(1, 0), 1usize.pow(0) % 25);
        assert_eq!(m25.exp(1, 1), 1usize.pow(1) % 25);
        assert_eq!(m25.exp(2, 2), 2usize.pow(2) % 25);
        assert_eq!(m25.exp(3, 3), 3usize.pow(3) % 25);
        assert_eq!(m25.exp(4, 4), 4usize.pow(4) % 25);
        assert_eq!(m25.exp(5, 5), 5usize.pow(5) % 25);
        assert_eq!(m25.exp(3, 5), 3usize.pow(5) % 25);
        assert_eq!(m25.exp(5, 3), 5usize.pow(3) % 25);
    }

    #[test]
    fn combination() {
        let c = ModularCombinationGenerator::new(6, 7);
        assert_eq!(c.get(3, 1), 3 % 7);
        assert_eq!(c.get(4, 2), 6 % 7);
        assert_eq!(c.get(5, 3), 10 % 7);
    }
}
