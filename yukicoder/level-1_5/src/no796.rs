use std::io;
use std::io::{BufRead, Write};

macro_rules! input {
    (source = $s:expr, $($r:tt)*) => {
        let mut iter = $s.split_whitespace();
        input_inner!{iter, $($r)*}
    };
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

// 2 -> 3 1 -> 4
// 3 -> 3 3 1 -> 7
// 4 -> 3 2 1 1 -> 7
// 5 -> 3 1 1 1 1 -> 7
// 6 -> 3 3 1 1 1 1 -> 10
// 7 -> 3 2 1 1 1 1 1 -> 10

fn process<R, W>(mut reader: R, mut writer: W) -> () where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        n: usize
    }

    match n % 3 {
        0 => {
            write!(writer, "3 3{}", " 1".repeat(n - 2));
        }
        1 => {
            write!(writer, "3 2{}", " 1".repeat(n - 2));
        }
        2 => {
            write!(writer, "3{}", " 1".repeat(n - 1));
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        let output = assert_judge_with_output!(process, "3");

        input! {
            source = output,
            o: [u32; 3],
        }

        assert!(o.iter().sum::<u32>() % 3 == 1);
        assert!(o.iter().product::<u32>() % 3 == 0);
        assert!(o.iter().sum::<u32>() <= 321456);
    }

    #[test]
    fn sample2() {
        let output = assert_judge_with_output!(process, "4");

        input! {
            source = output,
            o: [u32; 4],
        }

        assert!(o.iter().sum::<u32>() % 3 == 1);
        assert!(o.iter().product::<u32>() % 3 == 0);
        assert!(o.iter().sum::<u32>() <= 321456);
    }
}