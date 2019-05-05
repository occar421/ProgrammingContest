use std::io;
use std::io::{BufRead, Write};
use std::collections::vec_deque::VecDeque;
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

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let output = io::stdout();

    process(input, output);
}

// 1: 0001
// 2: 0010
// 3: 0011
// 5: 0101
// 7: 0111
//10: 1010
// 8: 1000
// 9: 1001
//11: 1011

fn count_bit(n: usize) -> usize {
    let mut c = 0;
    for i in 0..32 {
        c += (n >> i) & 1_usize;
    }
    c
}

fn process<R, W>(mut reader: R, mut writer: W) -> () where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        n: usize
    }

    if n == 1 {
        write!(writer, "1");
        return;
    }

    // breadth first search
    let mut points = [None; 10001];
    points[1] = Some(1);
    let mut queue = VecDeque::new();
    queue.push_back(1);
    while let Some(current) = queue.pop_front() {
        let current_hops = points[current].unwrap();
        let n_steps = count_bit(current);
        if n_steps < current { // 0 < current - n_steps
            let next = current - n_steps;
            match points[next] {
                Some(i) => {
                    points[next] = Some(min(i, current_hops + 1));
                }
                None => {
                    points[next] = Some(current_hops + 1);
                    queue.push_back(next);
                }
            }
        }
        if current + n_steps <= n {
            let next = current + n_steps;
            match points[next] {
                Some(i) => {
                    points[next] = Some(min(i, current_hops + 1));
                }
                None => {
                    if next == n {
                        write!(writer, "{}", current_hops + 1);
                        return;
                    }
                    points[next] = Some(current_hops + 1);
                    queue.push_back(next);
                }
            }
        }
    }

    write!(writer, "-1");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "5", "4");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "11", "9");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "4", "-1");
    }

    #[test]
    fn system_test2() {
        assert_judge!(process, "1", "1");
    }
}