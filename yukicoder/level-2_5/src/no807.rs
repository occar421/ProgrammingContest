// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::io;
use std::io::{BufRead, Write};
use std::ops::{Rem, Div, Mul};
use std::fmt::Display;
use std::collections::{HashMap, BinaryHeap};
use std::cmp::{min, Ordering};

// From https://qiita.com/tanakh/items/0ba42c7ca36cd29d0ac8
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

            assert_eq!(output, $expected);
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

#[allow(unused_macros)]
macro_rules! assert_judge_with_error {
    ($method:ident, $input:expr, $expected:expr, $t:ty | $precision:expr ) => {
        {
            let input = $input.as_bytes();
            let mut output = Vec::new();

            $method(&input[..], &mut output);

            let output = String::from_utf8(output).expect("Not UTF-8");

            let actual: $t = output.parse().unwrap();
            let expected: $t = $expected.parse().unwrap();

            assert_eq_with_error!(actual, expected, $precision);
        }
    };
}

pub trait GenericInteger: Copy + PartialEq + Rem<Output=Self> + Div<Output=Self> + Mul<Output=Self> {
    fn zero() -> Self;
}

macro_rules! dec_gi {
    () => {};
    ($t:ty $(, $r:ty)*) => {
        impl GenericInteger for $t {
            #[inline]
            fn zero() -> Self { 0 }
        }

        dec_gi![ $( $r ),* ];
    };
}

dec_gi![u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize];

#[allow(dead_code)]
pub fn gcd<T>(a: T, b: T) -> T where T: GenericInteger {
    if b == T::zero() {
        a
    } else {
        gcd(b, a % b)
    }
}

#[allow(dead_code)]
#[inline]
pub fn lcm<T>(a: T, b: T) -> T where T: GenericInteger {
    a / gcd(a, b) * b
}

pub trait IterExt<T> where T: Display {
    fn easy_join(&mut self, separator: &str) -> String;
}

impl<TItem, TTrait> IterExt<TItem> for TTrait where TItem: Display, TTrait: Iterator<Item=TItem> {
    #[inline]
    fn easy_join(&mut self, separator: &str) -> String {
        self.map(|i| format!("{}", i)).collect::<Vec<_>>().join(separator)
    }
}

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let output = io::stdout();

    process(input, output);
}

#[derive(Copy, Clone)]
struct NodeInfo {
    cost: usize,
    is_confirmed: bool,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
struct State {
    has_ticket: bool,
    node_index: usize,
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct QueueItem {
    state: State,
    weight: usize,
}

impl Ord for QueueItem {
    fn cmp(&self, other: &Self) -> Ordering {
        other.weight.cmp(&self.weight) // ascending
    }
}

impl PartialOrd for QueueItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn process<R, W>(mut reader: R, mut writer: W) -> () where
    R: BufRead,
    W: Write {
    input! {
        stdin = reader,
        n: usize, m: usize,
        abc: [(usize1, usize1, usize); m]
    }
    let abc: Vec<(usize, usize, usize)> = abc;

    // after checkin editor's note :(
    let mut distance_map = vec![HashMap::new(); n];
    for (i, j, d) in abc.iter() {
        distance_map[*i].insert(*j, *d);
        distance_map[*j].insert(*i, *d);
    }

    // Dijkstra with distance from point 0
    let mut node = HashMap::with_capacity(2 * n);
    node.insert(State { has_ticket: true, node_index: 0 }, NodeInfo { cost: 0, is_confirmed: false });
    node.insert(State { has_ticket: false, node_index: 0 }, NodeInfo { cost: 0, is_confirmed: false }); // exists because of impl.
    for i in 1..n {
        node.insert(State { has_ticket: true, node_index: i }, NodeInfo { cost: std::usize::MAX, is_confirmed: false });
        node.insert(State { has_ticket: false, node_index: i }, NodeInfo { cost: std::usize::MAX, is_confirmed: false });
    }

    let mut queue = BinaryHeap::new();
    queue.push(QueueItem { state: State { has_ticket: true, node_index: 0 }, weight: 0 });
    while let Some(QueueItem { state: current_state, weight: _ }) = queue.pop() {
        if node[&current_state].is_confirmed {
            continue;
        }
        node.get_mut(&current_state).unwrap().is_confirmed = true;

        for (&target_index, &cost) in &distance_map[current_state.node_index] {
            let target_state = State { has_ticket: current_state.has_ticket, node_index: target_index };
            let point_info_target = node[&target_state];
            if !point_info_target.is_confirmed {
                let new_cost = min(point_info_target.cost, node[&current_state].cost + cost);
                node.get_mut(&target_state).unwrap().cost = new_cost;
                if new_cost < point_info_target.cost { // minimum cost updated
                    queue.push(QueueItem { state: target_state, weight: new_cost });
                }
            }

            if current_state.has_ticket { // can use ticket (has_ticket:true -> has_ticket:false)
                let target_state = State { has_ticket: false, node_index: target_index };
                let point_info_target = node[&target_state];
                let new_cost = min(point_info_target.cost, node[&current_state].cost);
                node.get_mut(&target_state).unwrap().cost = new_cost;
                if new_cost < point_info_target.cost { // minimum cost updated
                    queue.push(QueueItem { state: target_state, weight: new_cost });
                }
            }
        }
    }

    // min dist with ticket + min dist without ticket
    for i in 0..n {
        let _ = writeln!(writer, "{}", node[&State { has_ticket: true, node_index: i }].cost + node[&State { has_ticket: false, node_index: i }].cost);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(process, "\
5 6
1 2 2
1 3 3
1 4 4
2 5 10
3 5 7
4 5 8
", "\
0
2
3
4
12
");
    }

    #[test]
    fn sample2() {
        assert_judge!(process, "\
6 8
1 2 5
2 6 8
1 3 3
3 5 2
5 6 1
1 4 6
4 5 2
1 6 10
", "\
0
5
3
6
6
6
");
    }
}