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
        a: [[u8; 4]; 4]
    }

    let a: Vec<Vec<u8>> = a;
    let mut d = [[false; 4]; 4]; // is it should be in right place?

    fn right_number(i: usize, j: usize) -> u8 {
        return (i * 4 + j + 1) as u8;
    }

    // one stroke
    let mut pos: (usize, usize) = (std::usize::MAX, std::usize::MAX);
    for i in 0..4 {
        for j in 0..4 {
            d[i][j] = a[i][j] == right_number(i, j);
            if a[i][j] == 0 {
                pos = (i, j);
            }
        }
    }

    while pos != (3, 3) {
        if pos.0 > 0 { // can go left
            if !d[pos.0 - 1][pos.1] && right_number(pos.0, pos.1) == a[pos.0 - 1][pos.1] {
                d[pos.0][pos.1] = true;
                pos = (pos.0 - 1, pos.1);
                continue;
            }
        }

        if pos.1 > 0 { // can go up
            if !d[pos.0][pos.1 - 1] && right_number(pos.0, pos.1) == a[pos.0][pos.1 - 1] {
                d[pos.0][pos.1] = true;
                pos = (pos.0, pos.1 - 1);
                continue;
            }
        }

        if pos.0 < 3 { // can go right
            if !d[pos.0 + 1][pos.1] && right_number(pos.0, pos.1) == a[pos.0 + 1][pos.1] {
                d[pos.0][pos.1] = true;
                pos = (pos.0 + 1, pos.1);
                continue;
            }
        }

        if pos.1 < 3 { // can go down
            if !d[pos.0][pos.1 + 1] && right_number(pos.0, pos.1) == a[pos.0][pos.1 + 1] {
                d[pos.0][pos.1] = true;
                pos = (pos.0, pos.1 + 1);
                continue;
            }
        }

        break; // can not move anymore
    }
    d[pos.0][pos.1] = true;

    let is_succeeded = d.iter().all(|d| d.iter().all(|d| *d));

//    write!(writer, "{:?}", d);
    write!(writer, "{}", if is_succeeded { "Yes" } else { "No" });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"
1 2 3 4
5 6 7 8
9 10 11 12
13 14 15 0
", "Yes");
    }

    #[test]
    fn sample2() {
        assert_judge!(process,
"
1 2 3 4
5 6 7 8
9 10 12 0
13 14 11 15
", "Yes");
    }

    #[test]
    fn sample3() {
        assert_judge!(process,
"
1 2 3 4
5 6 7 8
9 10 12 15
13 14 11 0
", "No");
    }
}