use std::io;
use std::io::{BufRead, Write};
use std::ops::{Rem, Div, Mul};
use std::collections::HashMap;

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
        s: chars
    }

    let s: Vec<char> = s;

    // A -> +1, B -> -1

//    let mut v: Vec<i32> = Vec::new();
//    let mut current = 'x';
//    let mut counter = 0;
//    for c in s.iter() {
//        if *c == current {
//            counter += if *c == 'A' { 1 } else { -1 };
//        } else {
//            v.push(counter);
//            current = *c;
//            counter = if *c == 'A' { 1 } else { -1 };
//        }
//    }
//    v.push(counter);
//    v.remove(0);
//
//    counter = 0;
//    for i in 0..v.len() {
//        v[i] += counter;
//        counter = v[i];
//    }
//
//    write!(writer, "{:?}", v);

    // checked editor's note :(
    let mut v = vec![0; s.len() + 1];
    let mut counter = 0;
    v[0] = counter;
    for (i, c) in s.iter().enumerate() {
        counter += if *c == 'A' { 1 } else { -1 };
        v[i + 1] = counter;
    }

    let mut start_map = HashMap::new();
    let mut end_map = HashMap::new();

    for (i, c) in v.iter().enumerate() {
        if start_map.contains_key(c) {
            end_map.insert(c, i);
        } else {
            start_map.insert(c, i);
        }
    }

    let max = end_map.iter().map(|x| x.1 - start_map[x.0]).max().unwrap_or(0);

//    write!(writer, "{:?} {:?} {:?} {:?}", v, start_map, end_map, max);
    write!(writer, "{}", max);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "AAABBA", "4");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "ABBBBBA", "2");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "B", "0");
    }
}