// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::io;
use std::io::{BufRead, Write};
use std::ops::{Rem, Div, Mul};
use std::fmt::Display;

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
        $iter.next().unwrap().parse::<$t>().expect("Parse error")
    };
}

#[allow(unused_macros)]
macro_rules! assert_judge {
    ($method:ident, $input:expr, $expected:expr) => {
        {
            let input = $input.as_bytes();
            let mut output = Vec::new();

            $method(&input[..], &mut output);

            let output = String::from_utf8(output).expect("Not UTF-8");

            assert_eq!(output, $expected);
        }
    };
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_output {
    ($method:ident, $input:expr) => {
        {
            let input = $input.as_bytes();
            let mut output = Vec::new();

            $method(&input[..], &mut output);

            String::from_utf8(output).expect("Not UTF-8")
        }
    };
}

#[allow(unused_macros)]
macro_rules! assert_eq_with_error {
    ($left:expr, $right:expr, $precision:expr) => ({
        match (&$left, &$right, &$precision) {
            (left_val, right_val, precision_val) => {
                if !(*left_val - *precision_val < *right_val && *right_val < *left_val + *precision_val) {
                    // The reborrows below are intentional. Without them, the stack slot for the
                    // borrow is initialized even before the values are compared, leading to a
                    // noticeable slow down.
                    panic!(r#"assertion failed: `(left == right) +- precision`
      left: `{:?}`,
     right: `{:?}`,
 precision: `{:?}`"#, &*left_val, &*right_val, &*precision_val)
                }
            }
        }
    });
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_error {
    ($method:ident, $input:expr, $expected:expr, $t:ty | $precision:expr ) => {
        {
            let input = $input.as_bytes();
            let mut output = Vec::new();

            $method(&input[..], &mut output);

            let output = String::from_utf8(output).expect("Not UTF-8");

            let actual: $t = output.parse().unwrap();
            let expected: $t = $expected.parse().unwrap();

            assert_eq_with_error!(actual, expected, $precision);
        }
    };
}

pub trait GenericInteger: Copy + PartialEq + Rem<Output=Self> + Div<Output=Self> + Mul<Output=Self> {
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
pub fn gcd<T>(a: T, b: T) -> T where T: GenericInteger {
    if b == T::zero() {
        a
    } else {
        gcd(b, a % b)
    }
}

#[allow(dead_code)]
#[inline]
pub fn lcm<T>(a: T, b: T) -> T where T: GenericInteger {
    a / gcd(a, b) * b
}

pub trait IterExt<T> where T: Display {
    fn easy_join(&mut self, separator: &str) -> String;
}

impl<TItem, TTrait> IterExt<TItem> for TTrait where TItem: Display, TTrait: Iterator<Item=TItem> {
    #[inline]
    fn easy_join(&mut self, separator: &str) -> String {
        self.map(|i| format!("{}", i)).collect::<Vec<_>>().join(separator)
    }
}

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let output = io::stdout();

    process(input, output);
}

fn process<R, W>(mut reader: R, mut writer: W) -> () where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        n: usize, d: usize
    }

//    let mut count = 0;
//    for x in 1..=n {
//        for y in x..=n {
//            let sq_min_z = d + 1 - (x * x + y * y);
//            if sq_min_z < 0 || sq_min_z < y * y {
//                println!("{:?}", (x, y, "brk!"));
//                break;
//            }
//            let min_z = (sq_min_z as f64).sqrt() as i64;
//            for z in min_z..=n {
//                let sq_w: i64 = (x * x + y * y + z * z) - d;
//                if sq_w < 0 {
//                    println!("{:?}", (x, y, z, "not enough", sq_w));
//                    continue;
//                }
//                let w = (sq_w as f64).sqrt() as i64;
//                if w * w == sq_w && w <= n {
//                    println!("{:?}", (x, y, z, w));
//                    count += n_diff3(x, y, z);
//                } else {
//                    println!("{:?}", (x, y, z, "wasted", w))
//                }
//            }
//        }
//    }
//
//    write!(writer, "{}", count);

    // after checking editor's note :(
    // x^2 + y^2 + z^2 = w^2 + D
    // x^2 + y^2 = w^2 - z^2 + D
    let mut left_side_memo = vec![0usize; 2 * n * n + d + 1];
    let mut right_side_memo = vec![0usize; 2 * n * n + d + 1];
    for x in 1..=n {
        for y in 1..=n {
            left_side_memo[x * x + y * y] += 1;
        }
    }
    for w in 1..=n {
        for z in 1..=n {
            if let Some(ww_zz_d) = (w * w + d).checked_sub(z * z) {
                right_side_memo[ww_zz_d] += 1;
            }
        }
    }

    let count: usize = left_side_memo.iter().zip(right_side_memo.iter())
        .map(|v| v.0 * v.1).sum();
    write!(writer, "{}", count);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "3 2", "7");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "7 100", "6");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "1500 1000000", "1911906");
    }

    #[test]
    fn large_05() {
        assert_judge!(process, "1492 0", "744810");
    }
}