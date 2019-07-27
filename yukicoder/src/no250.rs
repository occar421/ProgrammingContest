// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::io;
use std::io::{BufRead, Write};
use std::ops::{Div, Mul, Rem};

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
    ($method:ident, $input:expr, $expected:expr) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!($expected, output);
    }};
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_output {
    ($method:ident, $input:expr) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output);

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

trait GenericInteger:
    Copy + PartialEq + Rem<Output = Self> + Div<Output = Self> + Mul<Output = Self>
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
fn gcd<T>(a: T, b: T) -> T
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
fn lcm<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    a / gcd(a, b) * b
}

#[allow(unused_macros)]
macro_rules! swap {
    ($v1:expr, $v2:expr) => {
        let buf = $v1;
        $v1 = $v2;
        $v2 = buf;
    };
}

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let output = io::stdout();

    process(input, output);
}

fn process<R, W>(mut reader: R, mut writer: W) -> ()
where
    R: BufRead,
    W: Write,
{
    input! {
        stdin = reader,
        q: usize,
        dxt: [(usize, usize, usize); q]
    }

    fn le_combinations2(n: u128, k: u128, max: u128) -> bool {
        if k > n {
            return 1 <= max;
        }

        let k = if n - k < k { n - k } else { k };

        let mut numerator = 1u128;
        let mut denominator = 1u128;

        // from small numbers
        for d in (0..k).rev() {
            numerator *= n - d;
            if numerator % (k - d) == 0 {
                numerator /= k - d;
            } else {
                denominator *= k - d;
            }

            if numerator / denominator > max {
                return false;
            }
        }

        return numerator / denominator <= max;
    }

    for (d, x, t) in dxt {
        let n = x + d - 1; // (x+1 d-1 -1)
        let k = d - 1;
        let passed = le_combinations2(n as u128, k as u128, t as u128);
        writeln!(writer, "{}", if passed { "AC" } else { "ZETUBOU" });
    }
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
1 3 1
2 4 50
3 3 9
",
            "\
AC
AC
ZETUBOU
"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
3
58 62 1000
12 34 56
987 65 1234
",
            "\
ZETUBOU
ZETUBOU
ZETUBOU
"
        );
    }
}
