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
        s: [chars; h]
    }

    // referred editorial comments :(

    for di in 0..h as i32 {
        'attempt: for dj in (1 - w as i32)..w as i32 {
            if di == 0 && dj < 0 {
                continue;
            }

            let mut map = vec![vec!['.'; w]; h];
            let mut is_modified = false;

            // copy
            for i in 0..h {
                for j in 0..w {
                    map[i][j] = s[i][j];
                }
            }

            for i in 0..h {
                for j in 0..w {
                    if map[i][j] == '#' {
                        map[i][j] = '!';

                        if i as i32 + di >= h as i32 || j as i32 + dj < 0 || j as i32 + dj >= w as i32 {
                            continue 'attempt;
                        }
                        let idi = (i as i32 + di) as usize;
                        let jdj = (j as i32 + dj) as usize;
                        if map[idi][jdj] == '#' {
                            map[idi][jdj] = '?';
                            is_modified = true;
                        } else {
                            continue 'attempt;
                        }
                    }
                }
            }

            if is_modified {
                write!(writer, "YES");
            } else {
                // All squares are white
                write!(writer, "NO");
            }
            return;
        }
    }

    write!(writer, "NO");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"
3 3
##.
###
.#.
", "YES");
    }

    #[test]
    fn sample2() {
        assert_judge!(process,
"
5 3
.#.
.#.
.#.
.#.
.#.
", "NO");
    }

    #[test]
    fn sample3() {
        assert_judge!(process,
"
3 9
######...
#.####.#.
######...
", "YES");
    }

    #[test]
    fn sample4() {
        assert_judge!(process,
"
3 5
#...#
##.##
#...#
", "NO");
    }

    #[test]
    fn sample5() {
        assert_judge!(process,
"
5 8
###.....
#.####..
..####..
..####.#
.....###
", "YES");
    }

    #[test]
    fn sample6() {
        assert_judge!(process,
"
23 33
...............##................
...........##########............
.......##################........
...##########################....
.##....##################....##..
.######....##########....######..
.##########....##....##########..
.##....########..##############..
.######....####..##############..
.##############..##############..
.##############..##############..
.##############..##############..
...############..############....
.......########..########........
...........####..####............
...............##................
.................................
........#...#...........#........
........#...............#........
#.#.#.#.#.#.#.###.###.###.###.#.#
#.#.#.#.##..#.#...#.#.#.#.##..##.
.#..###.#.#.#.###.###.###.###.#..
#................................
", "NO");
    }
}