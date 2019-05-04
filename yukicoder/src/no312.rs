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
        n: usize
    }

    let rt_n = (n as f64).sqrt();
    let limit = rt_n.ceil() as usize;

//    let mut vec: Vec<_> = (3..limit + 1).collect();
//
//    for p in 3..limit + 1 {
//        vec.retain(|&x| x <= p || x % p != 0);
//    }
//
//    for p in vec {
//        if n % p == 0 {
//            write!(writer, "{}", p);
//            return;
//        }
//    }
//
//    write!(writer, "{}", original_n);

    let mut least_primes = vec![0; limit + 1];

    least_primes[1] = 1;
    least_primes[2] = 2;
    for i in 3..limit + 1 {
        if least_primes[i] == 0 {
            if n % i == 0 {
                write!(writer, "{}", i);
                return;
            }

            least_primes[i] = i;

            for j in (2 * i..limit + 1).step_by(i) {
                if least_primes[j] == 0 {
                    least_primes[j] = i;
                }
            }
        }
    }

    write!(writer, "{}", if n % 2 == 0 && n / 2 != 2 { n / 2 } else { n });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "9", "3");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "30", "3");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "114514", "31");
    }

    #[test]
    fn challenge02() {
        assert_judge!(process, "999999999958", "499999999979");
    }

    #[test]
    fn system_test9() {
        assert_judge!(process, "842870279900", "4");
    }

    #[test]
    fn t2() {
        assert_judge!(process, "4", "4");
    }
}