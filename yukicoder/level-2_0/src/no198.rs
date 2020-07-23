use std::io;
use std::io::{BufRead, Write};
use std::ops::{Rem, Div, Mul};
use std::cmp::min;

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
        b: i64,
        n: i64,
        c: [i64; n]
    }

//    let sum_candies_in_boxes = c.iter().sum::<i64>();
//    let avg_candies_in_boxes = sum_candies_in_boxes as f64 / n as f64;
////    let target = {
////        let target = if n < b {
////            avg_candies_in_boxes.round() as i64
////        } else {
////            avg_candies_in_boxes.ceil() as i64 + 1
////        };
////
////        if (b as f64) >= (target as f64 - avg_candies_in_boxes) * n as f64 {
////            target
////        } else if n < b {
////            target - 1
////        } else {
////            target - 2
////        }
////    };
////    let n_picks = c.iter().filter(|&c| *c > target).map(|c| c - target).sum::<i64>();
////    let n_puts = c.iter().filter(|&c| *c < target).map(|c| target - c).sum::<i64>();
//    // referred editor's note a bit
//    let targets = vec![avg_candies_in_boxes.floor() - 1_f64, avg_candies_in_boxes.floor(), avg_candies_in_boxes.ceil(), avg_candies_in_boxes.ceil() + 1_f64];
//    let targets = targets.iter().filter(|&t| b as f64 >= (*t - avg_candies_in_boxes) * n as f64).map(|&t| t as i64);
//
//    let candidates = targets.map(|t| {
//        let n_picks = c.iter().filter(|&c| *c > t).map(|c| c - t).sum::<i64>();
//        let n_puts = c.iter().filter(|&c| *c < t).map(|c| t - c).sum::<i64>();
//        n_picks + n_puts
//    });
//
////    write!(writer, "{}", n_picks + n_puts);
//    write!(writer, "{}", candidates.min().unwrap());

    // from editor's note :(
    let sum_candies_in_boxes = c.iter().sum::<i64>();

    let mut left = 0;
    let mut right = (sum_candies_in_boxes + b) / n;
    while right - left > 3 {
        let ml = left + (right - left) * 1 / 3;
        let ml_n_changes = c.iter().map(|c| (c - ml).abs()).sum::<i64>();
        let mr = left + (right - left) * 2 / 3;
        let mr_n_changes = c.iter().map(|c| (c - mr).abs()).sum::<i64>();
        if ml_n_changes > mr_n_changes {
            left = ml;
        } else {
            right = mr;
        }
    }

    let mut answer = std::i64::MAX;
    for i in left..=right {
        answer = min(answer, c.iter().map(|c| (c - i).abs()).sum());
    }
    write!(writer, "{}", answer);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"
1
3
0
1
2
", "2");
    }

    #[test]
    fn sample2() {
        assert_judge!(process,
"
1
3
0
0
1
", "1");
    }

    #[test]
    fn sample3() {
        assert_judge!(process,
"
0
4
0
4
2
2
", "4");
    }

    #[test]
    fn sample4() {
        assert_judge!(process,
"
1000000000
1
1000000000
", "0");
    }

    #[test]
    fn test3() {
        assert_judge!(process,
"
0
2
0
1
", "1");
    }

    #[test]
    fn test5() {
        assert_judge!(process,
"
3
4
5
6
7
8
", "4");
    }

    #[test]
    fn test7() {
        assert_judge!(process,
"
6
6
1000000000
1000000000
1000000000
1000000000
1000000000
1000000000
", "0");
    }

    #[test]
    fn test9() {
        assert_judge!(process,
"
8
8
1000000000
1000000000
1000000000
1000000000
1000000000
999999992
1000000000
1000000000
", "8");
    }
}