use std::io;
use std::io::{BufRead, Write};
use std::cmp::max;

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
        n: usize,
        a: [usize; n]
    }

    let mut max_retrograde = 0;
    let mut milestone = 0;
    for i in 0..n {
        if milestone >= a[i] {
            max_retrograde = max(max_retrograde, a[i])
        } else {
            milestone = a[i];
        }
    }

    let mut n_retrogrades = 0;

    let mut milestone = 0;
    for i in 0..n {
        if milestone >= a[i] {
            n_retrogrades += 1;
        } else {
            milestone = a[i];
            if a[i] < max_retrograde {
                n_retrogrades += 1;
            }
        }
    }

    write!(writer, "{}", n_retrogrades);


//    // solution from editor's note
//    let mut count = 0;
//    let mut current = n + 1;
//    for i in (0..n).rev() {
//        if a[i] + 1 == current {
//            count += 1;
//            current = a[i];
//        }
//    }
//    write!(writer, "{}", n - count);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process,
"
5
3 1 4 2 5
"
, "2");
    }

    #[test]
    fn sample2() {
        assert_judge!(process,
"
4
4 3 2 1
"
, "3");
    }

    #[test]
    fn sample3() {
        assert_judge!(process,
"
4
1 2 3 4
"
, "0");
    }
}