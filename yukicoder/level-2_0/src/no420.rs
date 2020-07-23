use std::io;
use std::io::{BufRead, Write};

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

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let output = io::stdout();

    process(input, output);
}

// f(0) = 0
// f(1) = f(0) + 1 = 1 :> 1
// f(2) = f(1) + 0 = 1 :> 1
// f(3) = f(1) + 1 = 2 :> 1 + 1
// f(4) = f(2) + 0 = 1 :> 1
// f(5) = f(2) + 1 = 2 :> 1 + 1
// f(6) = f(3) + 0 = 2 :> 1 + 1
// f(7) = f(3) + 1 = 3 :> ?
// f(8) = f(4) + 0 = 1 :> 1
// f(9) = f(4) + 1 = 2 :> 1 + 1
// f(10)= f(5) + 0 = 2 :> 1 + 1
// f(11)= f(5) + 1 = 3 :> ?
// f(12)= f(6) + 0 = 2
// f(13)= f(6) + 1 = 3
// f(14)= f(7) + 0 = 3
// f(15)= f(7) + 1 = 4
// f(16)= f(8) + 0 = 1

// 0 <= n < 2^4
// f(n)==4
// 15: ((0 * 2 + 1 * 2 + 1) * 2 + 1) * 2 + 1
// f(n)==3
//  7: ((0 * 2 + 1 * 2 + 1) * 2 + 1)

// 11: ((0 * 2 + 1 * 2 + 0) * 2 + 1) * 2 + 1
// 13: ((0 * 2 + 1 * 2 + 1) * 2 + 0) * 2 + 1
// 14: ((0 * 2 + 1 * 2 + 1) * 2 + 1) * 2 + 0

// f(n)==2
//  3: ((0 * 2 + 1 * 2 + 1)        )
//  5: ((0 * 2 + 1 * 2 + 0) * 2 + 1)
//  6: ((0 * 2 + 1 * 2 + 1) * 2 + 0)

//  9: ((0 * 2 + 1 * 2 + 0) + 2 + 0) * 2 + 1
// 10: ((0 * 2 + 1 * 2 + 0) * 2 + 1) * 2 + 0
// 12: ((0 * 2 + 1 * 2 + 1) * 2 + 0) * 2 + 0

//fn c(x: u64, max_bits: u8) -> Vec<(u64, u8)> {
//    if x == 1 {
//        return vec![(0, 0), (1, 1)];
//    }
//    let v = c(x - 1, max_bits);
//    return v.iter().flat_map(|v|
//        if v.1 >= max_bits {
//            vec![(v.0 << 1, v.1)]
//        } else {
//            vec![(v.0 << 1, v.1), ((v.0 << 1) | 1_u64, v.1 + 1)]
//        }
//    ).collect();
//}

fn process<R, W>(mut reader: R, mut writer: W) -> () where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        x: u128
    }

//    if x > 31 || x == 0 {
//        write!(writer, "0 0");
//        return;
//    }
//    let x = x as u8;
//
//    let mut original_numbers = Vec::new();
//
//    // 32/x && top-bit==1
//    for combi in c(31, x) {
//        if combi.1 != x {
//            continue;
//        }
////        let code = (combi.0 << 1) + 1;
//        let code = combi.0;
//
////        let mut v = 0;
////        // from bottom bit
////        for i in 0..32 {
////            let bottom_bit = (code >> i) & 1;
////            v += v * 2 + bottom_bit;
////        }
//        original_numbers.push(code);
//    }
//
//    write!(writer, "{} {}", original_numbers.len(), original_numbers.iter().sum::<u64>());


    // after checking editor's note :(
    if x > 31 {
        write!(writer, "0 0");
        return;
    }
    if x == 0 {
        write!(writer, "1 0");
        return;
    }

    let mut c = 1_u128;
    for i in 0..x {
        c *= 31 - i;
    }
    for i in 0..x {
        c /= x - i;
    }

    let mut cs = 1_u128;
    for i in 0..x - 1 {
        cs *= 30 - i;
    }
    for i in 0..x - 1 {
        cs /= x - 1 - i
    }
    let s = (2u128.pow(31) - 1) * cs;

    write!(writer, "{} {}", c, s);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "5", "169911 58851789346035");
    }

    #[test]
    fn system_test1() {
        assert_judge!(process, "15", "300540195 312292816465495725");
    }
}