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
        t: usize,
        records: [(chars); t]
    }

    't: for record in records.iter() {
        let mut n_red = 0;
        let mut n_green = 0;
        let mut n_white = 0;
        for light in record.iter().rev() {
            match light {
                'R' => {
                    n_red += 1;
                }
                'G' => {
                    if n_red == 0 {
                        writeln!(writer, "impossible");
                        continue 't;
                    }
                    n_red -= 1;
                    n_green += 1;
                }
                'W' => {
                    if n_green == 0 && n_white == 0 {
                        writeln!(writer, "impossible");
                        continue 't;
                    }
                    if n_green > 0 {
                        n_green -= 1;
                    }
                    n_white += 1;
                }
                _ => panic!("invalid input")
            };
        };

        writeln!(writer, "{}", if n_red == 0 && n_green == 0 && n_white >= 0 { "possible" } else { "impossible" });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"\
5
WWWWWWWWWGR
WWWWGWGRR
WWWWWWWWWWWWWWGRRG
WGRWGR
WWWWWWWWWWWWWWWWWGGWGWGGWGWGGGWGG
",
"\
possible
possible
impossible
possible
impossible
");
    }

    #[test]
    fn sample() {
        assert_judge!(process,
"\
15
WWWWWWWWWGR
WWWWGWGRR
WWWWWWWWWWWWWWGRRG
WGRWGR
WWWWWWWWWWWWWWWWWGGWGWGGWGWGGGWGG
WWWGRGRW
WWWGRGWR
WWWGWGRR
WWWGGWRR
W
R
G
WW
GR
RGW
",
"\
possible
possible
impossible
possible
impossible
impossible
impossible
possible
impossible
impossible
impossible
impossible
impossible
impossible
impossible
");
    }
}
