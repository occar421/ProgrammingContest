use std::io;
use std::io::{BufRead, Write};
use std::ops::{Rem, Div, Mul};

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

            assert_eq!($expected, output);
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

trait GenericInteger: Copy + PartialEq + Rem<Output=Self> + Div<Output=Self> + Mul<Output=Self> {
    fn zero() -> Self;
}

macro_rules! dec_gi {
    () => {};
    ($t:ty $(, $r:ty)*) => {
        impl GenericInteger for $t {
            fn zero() -> Self { 0 }
        }

        dec_gi![ $( $r ),* ];
    };
}

dec_gi![u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize];

#[allow(dead_code)]
fn gcd<T>(a: T, b: T) -> T where T: GenericInteger {
    if b == T::zero() {
        a
    } else {
        gcd(b, a % b)
    }
}

#[allow(dead_code)]
fn lcm<T>(a: T, b: T) -> T where T: GenericInteger {
    a / gcd(a, b) * b
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
        s_before: chars,
        n: usize,
        s_after: chars
    }

    let n_coins_before = s_before.iter().filter(|&s| *s == 'o').count();
    let n_coins_after = s_after.iter().filter(|&s| *s == 'o').count();
    if n_coins_before != n_coins_after {
        write!(writer, "SUCCESS");
        return;
    }

    if n_coins_before == 3 || n_coins_before == 0 {
        write!(writer, "FAILURE");
        return;
    }

    let seeker = if n_coins_before == 1 { 'o' } else { 'x' };

    let index_before = s_before.iter().position(|&s| s == seeker).unwrap() as i8;
    let index_after = s_after.iter().position(|&s| s == seeker).unwrap() as i8;

    let is_feasible = match (n, index_after, index_before) {
        (0, a, b) => a == b,
        (1, 0, 0) => true, // swap others
        (1, 2, 2) => true, // swap others
        (1, a, b) => (a - b).abs() == 1,
        (2, _, _) => true, // always feasible
        (_, _, _) => true
    };

    write!(writer, "{}", if is_feasible { "FAILURE" } else { "SUCCESS" });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"
xxo
1
oxx
", "SUCCESS");
    }

    #[test]
    fn sample2() {
        assert_judge!(process,
"
xoo
2
oox
", "FAILURE");
    }

    #[test]
    fn sample3() {
        assert_judge!(process,
"
ooo
0
xxx
", "SUCCESS");
    }

    #[test]
    fn sample4() {
        assert_judge!(process,
"
oxo
2000000000
oxo
", "FAILURE");
    }

    #[test]
    fn test3() {
        assert_judge!(process,
"
xxo
1
xxo
", "FAILURE");
    }
}