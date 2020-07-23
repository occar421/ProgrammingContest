use std::io;
use std::io::{BufRead, Write};

macro_rules! input {
    (stdin = $stdin:expr, $($r:tt)*) => {
        let s = {
            let mut s = String::new();
            $stdin.read_to_string(&mut s).unwrap();
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

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let output = io::stdout();

    process(input, output)
}

// 0 -> 6
// 1 -> 2
// 2 -> 5
// 3 -> 5
// 4 -> 4
// 5 -> 5
// 6 -> 6
// 7 -> 3
// 8 -> 7
// 9 -> 6

// 2 -> 1
// 3 -> 7
// 4 -> 11
// 5 -> 71
// 6 -> 111
// 7 -> 711

// odd -> 7111...
// even -> 1111...

fn process<R, W>(mut reader: R, mut writer: W) where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        n: i32
    }

    let n_digits_by_1 = n / 2;
    if n % 2 == 1 {
        write!(writer, "7{}", "1".repeat((n_digits_by_1 - 1) as usize));
    } else {
        write!(writer, "{}", "1".repeat(n_digits_by_1 as usize));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "2", "1\
        ");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "3", "7\
        ");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "4", "11\
        ");
    }
}