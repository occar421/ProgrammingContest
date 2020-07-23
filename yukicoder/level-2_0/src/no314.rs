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

// 1 ->  [1] k
// 2 ->  [2] kk,       kp
// 3 ->  [2] kkp,      kpk
// 3 -> "2" + 0
// 4 ->  [3] kkpk,     kpkp,      kpkk
// 4 -> "3" + 1, "2" + 1
// 5 ->  [4] kkpkk,    kkpkp,     kpkkp,     kpkpk
// 5 -> "4" + 1, "3" + 2, "2" + 2
// 6 ->  [5] kkpkkp,   kkpkpk,    kpkkpk,    kpkpkk,   kpkpkp
// 6 -> "5" + 1, "4" + 2, "3" + 3, "2" + 3
// 7 ->  [7] kkpkkpk,  kkpkpkk,   kkpkpkpk,  kpkkpkk,  kpkkpkp,  kpkpkkp,  kpkpkpk
// 7 -> "6" + 2, "5" + 3, "4" + 4, "3" + 5, "2" + 5
// 8 ->  [9] kkpkkpkk, kkpkkpkp,  kkpkpkkpk, kkpkpkpk, kpkkpkkp, kpkkpkpk, kpkpkkpk, kpkpkpkk, kpkpkpkp

// q(n) = q(n-3) + q(n-2)

fn process<R, W>(mut reader: R, mut writer: W) -> () where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        n: usize
    }

    static HASH: usize = 1000000007;

    let mut memo: Vec<usize> = vec![0; n + 3];
    memo[1] = 1;
    memo[2] = 2;
    memo[3] = 2;
    for i in 4..n + 1 {
        memo[i] = (memo[i - 3] + memo[i - 2]) % HASH;
    }

    write!(writer, "{}", memo[n]);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "3", "2");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "4", "3");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "100", "831891005");
    }
}