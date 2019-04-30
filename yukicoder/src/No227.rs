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
        a: [usize; 5],
    }

    let mut buckets = vec![0; 14];

    for a in a {
        buckets[a] = buckets[a] + 1;
    }

    let has_triple = buckets.contains(&3);
    let n_doubles = buckets.iter().filter(|&&b| b == 2).count();

    let message = match (has_triple, n_doubles) {
        (true, 1) => "FULL HOUSE",
        (true, 0) => "THREE CARD",
        (false, 2) => "TWO PAIR",
        (false, 1) => "ONE PAIR",
        _ => "NO HAND"
    };
    write!(writer, "{}", message);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        let input = b"5 6 5 6 5";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("FULL HOUSE", output)
    }

    #[test]
    fn sample2() {
        let input = b"5 6 5 7 5";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("THREE CARD", output)
    }

    #[test]
    fn sample3() {
        let input = b"5 6 5 6 7";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("TWO PAIR", output)
    }

    #[test]
    fn sample4() {
        let input = b"5 6 5 7 8";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("ONE PAIR", output)
    }

    #[test]
    fn sample5() {
        let input = b"5 6 7 8 9";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("NO HAND", output)
    }

    #[test]
    fn sample6() {
        let input = b"5 5 5 5 5";
        let mut output = Vec::new();

        process(&input[..], &mut output);

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!("NO HAND", output)
    }
}