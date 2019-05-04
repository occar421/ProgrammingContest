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

// q = 1 - p
// 2 => [1] 2
// 3 => [2] 2,3
// 4 => [2 + q] 2,3,4q
// 5 => [3 + q] 2,3,4q,5
// 6 => [3 + q + qq] 2,3,4q,5,6qq
// 7 => [4] 2,3,4q,5,6qq,7
// 8 => [4 + q + 2qq] 2,3,4q,5,6qq,7,8qq
// 9 => [4 + 2q + 2qq] 2,3,4q,5,6qq,7,8qq,9q
//10 => [4 + 2q + 3qq] 2,3,4q,5,6qq,7,8qq,9q,10qq

// 4q <- 2
// 6qq <- 2, 3
// 8qq <- 4q
// 9q <- 3
// 10qq <- 2, 5

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
        n: usize, p: f64
    }

    // x * i => +1 :=> *q

    let mut counters = vec![0; n + 1];

    for i in 2..n + 1 {
        for j in (2 * i..n + 1).step_by(i) {
            counters[j] += 1;
        }
    }

    let mut e = 0f64;

    for i in 2..n + 1 {
        if counters[i] == 0 {
            // prime number
            e += 1.0f64;
        } else {
            e += (1.0f64 - p).powi(counters[i]);
        }
    }

    write!(writer, "{}", e);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        let output = assert_judge_with_output!(process, "10 1.00000");

        input! {
             source = output,
             o: f64,
        }

        assert_eq_with_error!(4f64, o, 10f64.powi(-6));
    }

    #[test]
    fn sample2() {
        let output = assert_judge_with_output!(process, "10 0.00000");

        input! {
             source = output,
             o: f64,
        }

        assert_eq_with_error!(9f64, o, 10f64.powi(-6));
    }

    #[test]
    fn sample3() {
        let output = assert_judge_with_output!(process, "10 0.50000");

        input! {
             source = output,
             o: f64,
        }

        assert_eq_with_error!(5.75f64, o, 10f64.powi(-6));
    }
}