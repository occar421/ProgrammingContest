// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::io;
use std::io::{BufRead, Write};
use std::ops::{Rem, Div, Mul};
use std::collections::VecDeque;

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

trait GenericInteger: Copy + PartialEq + Rem<Output=Self> + Div<Output=Self> + Mul<Output=Self> {
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

fn process<R, W>(mut reader: R, mut writer: W) -> () where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        n: usize, d: usize, k: usize
    }

//    // working fine (AC) but slow
//    if k == 1 {
//        if d <= n {
//            write!(writer, "{}", d);
//        } else {
//            write!(writer, "-1");
//        }
//        return;
//    }
//
//    let mut queue = VecDeque::new();
//    let mut min_number = 1;
//    let mut sum = 0;
//
//    loop {
//        while queue.len() < k - 1 {
//            queue.push_front(min_number);
//            sum += min_number;
//            min_number += 1;
//            if min_number > n - (k - queue.len() - 1) {
//                write!(writer, "-1");
//                return;
//            }
//
//            // can't achieve D with rest of numbers
//            if d > sum &&
//                n * (n + 1) / 2 - (n - (k - queue.len())) * (n - (k - queue.len()) + 1) / 2
//                    < d - sum {
//                break;
//            }
//        }
//        if sum < d && queue.len() == k - 1 {
//            let next = d - sum;
//            if next >= min_number && next <= n {
//                write!(writer, "{} {}",
//                       queue.iter().rev().map(|q| format!("{}", q)).collect::<Vec<_>>().join(" "), next);
//                return;
//            }
//        }
//
//        while let Some(a) = queue.pop_front() {
//            sum -= a;
//            min_number = a + 1;
//            if min_number > n - (k - queue.len() - 1) {
//                continue;
//            } else {
//                break;
//            }
//        }
//    }

    // considering editor's note :p
    let lower_limit = k * (k + 1) / 2;
    let upper_limit = n * (n + 1) / 2 - (n - k) * (n - k + 1) / 2;
    if lower_limit > d || d > upper_limit {
        write!(writer, "-1");
        return;
    }

    let mut result = vec![0; k];
    for i in 0..k {
        result[i] = i + 1;
    }
    let mut rests = d - lower_limit;

    let mut max_value = n;
    for i in (0..k).rev() {
        if rests + result[i] <= max_value {
            result[i] += rests;
            break;
        }
        rests -= max_value - result[i];
        result[i] = max_value;
        max_value -= 1;
    }

    write!(writer, "{}",
           result.iter().map(|q| format!("{}", q)).collect::<Vec<_>>().join(" "));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "10 9 3", "1 2 6");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "10 9 4", "-1");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "30 40 4", "1 2 7 30");
    }

    #[test]
    fn _99_system_test2() {
        assert_judge!(process, "15 104 10", "5 7 8 9 10 11 12 13 14 15");
    }

    #[test]
    fn system_test1() {
        assert_judge!(process, "20 730 1", "-1");
    }

    #[test]
    fn testcase17() {
        assert_judge!(process, "100 955 10", "91 92 93 94 95 96 97 98 99 100");
    }
}