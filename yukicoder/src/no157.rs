use std::io;
use std::io::{BufRead, Write};
use std::ops::{Rem, Div, Mul};
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
        w: usize, h: usize,
        c: [chars; h]
    }

//    // find first hole
//    let mut i = c.iter().position(|r| r.iter().find(|&c| *c == '.').is_some()).unwrap();
//    let mut j = c[i].iter().position(|c| *c == '.').unwrap();
//    let mut first_hole = vec![(i, j)];
//    loop {
//        if c[i][j + 1] == '.' {
//            first_hole.push((i, j + 1));
//            j = j + 1;
//        } else {
//            loop {
//
//            }
//        }
//    }
//
//    write!(writer, "{}", i);

    // checked editor's note :(
    #[derive(Debug, Clone)]
    struct Point {
        x: usize,
        y: usize,
    }

    // c[y][x]
    let y = c.iter().position(|r| r.iter().find(|&c| *c == '.').is_some()).unwrap();
    let x = c[y].iter().position(|c| *c == '.').unwrap();
    const MAX_SIZE: usize = 21;
    let mut checked = [[false; MAX_SIZE]; MAX_SIZE];
    for i in 0..y {
        for j in 0..MAX_SIZE {
            checked[i][j] = true;
        }
    }
    for j in 0..=x {
        checked[y][j] = true;
    }
    for i in 0..MAX_SIZE {
        checked[i][0] = true;
        checked[i][MAX_SIZE - 1] = true;
    }
    for j in 0..MAX_SIZE {
        checked[0][j] = true;
        checked[MAX_SIZE - 1][j] = true;
    }

    let mut first_hole = vec![Point { x, y }];
    let mut search_queue = VecDeque::new();
    search_queue.push_back((y + 1, x));
    checked[y + 1][x] = true;
    search_queue.push_back((y, x + 1));
    checked[y][x + 1] = true;
    while let Some((y, x)) = search_queue.pop_front() {
        if c[y][x] == '.' {
            first_hole.push(Point { x, y });
            if !checked[y + 1][x] {
                search_queue.push_back((y + 1, x));
                checked[y + 1][x] = true;
            }
            if !checked[y - 1][x] {
                search_queue.push_back((y - 1, x));
                checked[y - 1][x] = true;
            }
            if !checked[y][x + 1] {
                search_queue.push_back((y, x + 1));
                checked[y][x + 1] = true;
            }
            if !checked[y][x - 1] {
                search_queue.push_back((y, x - 1));
                checked[y][x - 1] = true;
            }
        }
    }

    let first_y = y;
    let mut x = 0;
    let mut y = 0;
    'outer: for (i, r) in c.iter().enumerate() {
        // skip
        if i < first_y {
            continue;
        }

        for (j, c) in r.iter().enumerate() {
            if !checked[i][j] && *c == '.' {
                y = i;
                x = j;
                break 'outer;
            }
        }
    }
    for i in 0..y {
        for j in 0..MAX_SIZE {
            checked[i][j] = true;
        }
    }
    for j in 0..=x {
        checked[y][j] = true;
    }

    let mut second_hole = vec![Point { x, y }];
    if !checked[y + 1][x] {
        search_queue.push_back((y + 1, x));
        checked[y + 1][x] = true;
    }
    if !checked[y][x + 1] {
        search_queue.push_back((y, x + 1));
        checked[y][x + 1] = true;
    }
    while let Some((y, x)) = search_queue.pop_front() {
        if c[y][x] == '.' {
            second_hole.push(Point { x, y });
            if !checked[y + 1][x] {
                search_queue.push_back((y + 1, x));
                checked[y + 1][x] = true;
            }
            if !checked[y - 1][x] {
                search_queue.push_back((y - 1, x));
                checked[y - 1][x] = true;
            }
            if !checked[y][x + 1] {
                search_queue.push_back((y, x + 1));
                checked[y][x + 1] = true;
            }
            if !checked[y][x - 1] {
                search_queue.push_back((y, x - 1));
                checked[y][x - 1] = true;
            }
        }
    }

    let mut min_distance = std::i32::MAX;
    for Point { x: x1, y: y1 } in first_hole {
        for Point { x: x2, y: y2 } in &second_hole {
            min_distance = min(min_distance, (*x2 as i32 - x1 as i32).abs() + (*y2 as i32 - y1 as i32).abs() - 1);
        }
    }

    write!(writer, "{}", min_distance);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"
9 5
#########
#.####.##
#..###.##
#..###..#
#########
", "3");
    }

    #[test]
    fn sample2() {
        assert_judge!(process,
"
8 5
########
####..##
#..#..##
#...####
########
", "1");
    }

    #[test]
    fn sample3() {
        assert_judge!(process,
"
9 9
#########
#.......#
#.#####.#
#.#...#.#
#.#.#.#.#
#.#...#.#
#.#####.#
#.......#
#########
", "1");
    }

    #[test]
    fn sample4() {
        assert_judge!(process,
"
8 6
########
#....###
#.######
#.####.#
#.######
########
", "3");
    }

    #[test]
    fn _1() {
        assert_judge!(process,
"
4 5
####
####
#.##
##.#
####
", "1");
    }
}