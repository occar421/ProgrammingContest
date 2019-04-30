use std::io;
use std::io::{BufRead, Write};
use std::collections::HashSet;

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

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let output = io::stdout();

    process(input, output)
}

fn process<R, W>(mut reader: R, mut writer: W) where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        n: i32,
        turns: [(i32, i32, i32, i32, String); n]
    }

    let mut possible: HashSet<i32> = (0..9 + 1).collect();
    let mut never = HashSet::new();

    for turn in turns {
        if turn.4 == "YES" {
            let new_possible: HashSet<_> = [turn.0, turn.1, turn.2, turn.3].iter().cloned().collect();
            possible = possible.intersection(&new_possible).cloned().collect();
        } else {
            never.insert(turn.0);
            never.insert(turn.1);
            never.insert(turn.2);
            never.insert(turn.3);
        }
    }

    let mut difference = possible.difference(&never);
    write!(writer, "{}", difference.next().unwrap());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        let input = b"3
1 2 4 3 NO
8 5 6 7 NO
0 1 2 3 NO
";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("9", output)
    }

    #[test]
    fn sample2() {
        let input = b"2
1 2 3 4 YES
4 5 6 7 YES
";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("4", output)
    }

    #[test]
    fn sample3() {
        let input = b"4
2 6 5 3 NO
1 0 4 7 YES
1 7 8 4 YES
7 1 9 8 NO
";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("4", output)
    }
}