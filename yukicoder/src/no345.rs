use std::io;
use std::io::{BufRead, Write};
use std::cmp::min;

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

//
//   ┌--------------[w]-┐
//   v                  |
// None -[c]-> C -[w]-> CW <-[w;c]-> CCw
//            [c]                    [c]
//
enum State {
    None,
    C(usize),
    Cw(usize),
    CwC(usize, usize),
}

fn process<R, W>(mut reader: R, mut writer: W) where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        s: chars
    }

    let mut answer = std::usize::MAX;
    let mut state = State::None;

    for (i, c) in s.iter().enumerate() {
        state = match (state, c) {
            (State::None, 'c') => State::C(i),
            (State::C(_), 'c') => State::C(i),
            (State::C(s), 'w') => State::Cw(s),
            (State::Cw(s), 'c') => State::CwC(s, i),
            (State::Cw(s), 'w') => {
                answer = min(answer, i - s + 1);
                State::None
            }
            (State::CwC(s1, _), 'c') => State::CwC(s1, i),
            (State::CwC(s1, s2), 'w') => {
                answer = min(answer, i - s1 + 1);
                State::Cw(s2)
            }
            (s, _) => s
        }
    }

    if answer == std::usize::MAX {
        write!(writer, "-1");
        return;
    }
    write!(writer, "{}", answer);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "ilovechiwawa", "6\
         ");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "wachiwachi", "-1\
         ");
    }

    #[test]
    fn sample3() {
        assert_judge!(process, "chiwaaaaaaamikawayadeeeeesu", "16\
         ");
    }
}