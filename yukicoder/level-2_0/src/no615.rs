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
        n: usize, k: usize,
        a: [i64; n]
    }

    let a = {
        let mut a = a;
        a.sort();
        a as Vec<i64>
    };

    let differences = {
        let mut d = a.windows(2).map(|w| (w[1] - w[0])).enumerate().collect::<Vec<_>>();
        d.sort_by_key(|e| e.1);
        d
    };

//    for d in differences.iter().rev().take(k).collect::<Vec<_>>().windows(2) {
//        let starts_at = min(d[0].0, d[1].0);
//        let ends_at = max(d[0].0, d[1].0);
//        let range = a.iter().skip(starts_at).take(ends_at - starts_at);
//        range.max()
//    }

//    let answer: i64 = differences.iter().rev().take(k).collect::<Vec<_>>().windows(2).map(|d| {
//        let starts_at = min(d[0].0, d[1].0);
//        let ends_at = max(d[0].0, d[1].0);
//        let mut range = a.iter().skip(starts_at).take(ends_at - starts_at);
//        let range = range.by_ref();
//        println!("{:?} {:?}", range.collect::<Vec<_>>(), range.collect::<Vec<_>>().iter().max());
//        range.max().unwrap() - range.min().unwrap()
//    }).sum();

    let separations = {
        let mut d = differences.iter().rev().take(k - 1).map(|d| d.0).collect::<Vec<_>>();
        d.sort();
        d
    };

    let mut answer = 0;
    let mut prev = -1_i64;
    for s in separations {
        let r: Vec<_> = a.iter().skip((prev + 1) as usize).take((s as i64 - prev) as usize).collect();
        answer += *r.iter().max().unwrap() - *r.iter().min().unwrap();
        prev = s as i64;
    }
    let r: Vec<_> = a.iter().skip((prev + 1) as usize).collect();
    answer += *r.iter().max().unwrap() - *r.iter().min().unwrap();

    write!(writer, "{:?}", answer);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"
5 2
1 10 11 2 9
", "3");
    }

    #[test]
    fn sample2() {
        assert_judge!(process,
"
4 2
0 7 3 13
", "7");
    }

    #[test]
    fn sample3() {
        assert_judge!(process,
"
3 3
1 10 100
", "0");
    }

    #[test]
    fn sample4() {
        assert_judge!(process,
"
3 1
0 0 1000000000000
", "1000000000000");
    }

    #[test]
    fn sample5() {
        assert_judge!(process,
"
10 3
1 12 19 23 28 3 32 36 41 7
", "28");
    }
}