// occar421(MasuqaT)/template-procon-stdio.rs
// https://gist.github.com/occar421/c3368bf225aa84934e1a0fadd9b047f1

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
        h: usize, w: usize,
        n: usize,
        sk: [(char, usize); n]
    }
    let sk: Vec<(char, usize)> = sk;

    /* TLE answer
    // is_white?
    let mut map = vec![vec![false; w]; h];
    for i in 0..h {
        for j in 0..w {
            if i % 2 == j % 2 {
                map[i][j] = true;
            }
        }
    }

    for sk in sk.iter() {
        if sk.0 == 'C' {
            let bottom = map[h - 1][sk.1];
            for i in (1..h).rev() {
                map[i][sk.1] = map[i - 1][sk.1];
            }
            map[0][sk.1] = bottom;
        } else {
            let right = map[sk.1][w - 1];
            for j in (1..w).rev() {
                map[sk.1][j] = map[sk.1][j - 1];
            }
            map[sk.1][0] = right;
        }
    }

    write!(writer, "{}", if map[0][0] { "white" } else { "black" });
    */

    /* wrong
    let mut c_counts = vec![0; w];
    let mut r_counts = vec![0; h];

    let mut position = (0, 0);
    for sk in sk.iter().rev() {
        if sk.0 == 'C' {
            if position.0 == sk.1 {
                position.0 = (h + position.0 - 1 - c_counts[sk.1]) % h;
                c_counts[sk.1] = 0;
                // need to loop
            } else {
                c_counts[sk.1] += 1;
                // store
            }
        } else {// R
            if position.1 == sk.1 {
                position.1 = (w + position.1 - 1 - r_counts[sk.1]) % w;
                r_counts[sk.1] = 0;
                // need to loop
            } else {
                r_counts[sk.1] += 1;
            }
        }
    }

    write!(writer, "{}", if position.0 % 2 == position.1 % 2 { "white" } else { "black" });
    */

    /* didn't work
    let stub: VecDeque<bool> = VecDeque::new();
    let mut init_row = [vec![false; w], vec![false; w]]; // even, odd
    for j in 0..w {
        let is_white = j % 2 == 0;
        init_row[0][j] = is_white;
        init_row[1][j] = !is_white;
    }
    let mut map = vec![stub; h];
    for i in 0..h {
        map[i] = VecDeque::from(init_row[i % 2].clone());
    }

    for sk in sk.iter() {
        if sk.0 == 'C' {
            let bottom = map[h - 1][sk.1];
            for i in (1..h).rev() {
                map[i][sk.1] = map[i - 1][sk.1];
            }
            map[0][sk.1] = bottom;
        } else {
            let right = map[sk.1].pop_back().unwrap();
            map[sk.1].push_front(right);
        }
    }

    write!(writer, "{}", if map[0][0] { "white" } else { "black" });
    */

    // solution from editor's note
    let mut row = 0;
    let mut column = 0;
    for (s, k) in sk.iter().rev() {
        if *s == 'R' {
            if *k == row {
                column = (w + column - 1) % w;
            }
        } else {
            if *k == column {
                row = (h + row - 1) % h;
            }
        }
    }
    write!(writer, "{}", if (row + column) % 2 == 0 { "white" } else { "black" });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"
4 5
3
R 1
C 4
R 0
", "black");
    }

    #[test]
    fn sample2() {
        assert_judge!(process,
"
5 5
4
C 3
R 2
C 3
R 4
", "white");
    }

    #[test]
    fn sample3() {
        assert_judge!(process,
"
6 5
10
C 0
C 2
R 5
C 3
R 0
C 2
R 3
C 1
C 2
R 0
", "white");
    }

    #[test]
    fn sample4() {
        assert_judge!(process,
"
1 2
5
C 0
R 0
C 0
R 0
C 1
", "white");
    }
}