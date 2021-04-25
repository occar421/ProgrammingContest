// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::collections::HashMap;
use std::fmt::Display;
use std::io;
use std::io::{BufRead, Result, Write};
use std::ops::{Div, Mul, Rem};
use std::str::FromStr;

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
        $iter.next().unwrap_or_default().parse::<$t>().expect("Parse error")
    };
}

#[allow(unused_macros)]
macro_rules! assert_judge {
    ($method:ident, $input:expr, $expected:expr) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output).expect("Should not emit error");

        let output = String::from_utf8(output).expect("Not UTF-8");

        assert_eq!(output, $expected);
    }};
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_output {
    ($method:ident, $input:expr) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output).expect("Should not emit error");

        String::from_utf8(output).expect("Not UTF-8")
    }};
}

#[allow(unused_macros)]
macro_rules! assert_eq_with_error {
    ($left:expr, $right:expr, $precision:expr) => {{
        match (&$left, &$right, &$precision) {
            (left_val, right_val, precision_val) => {
                if !(*left_val - *precision_val < *right_val
                    && *right_val < *left_val + *precision_val)
                {
                    // The reborrows below are intentional. Without them, the stack slot for the
                    // borrow is initialized even before the values are compared, leading to a
                    // noticeable slow down.
                    panic!(
                        r#"assertion failed: `(left == right) +- precision`
      left: `{:?}`,
     right: `{:?}`,
 precision: `{:?}`"#,
                        &*left_val, &*right_val, &*precision_val
                    )
                }
            }
        }
    }};
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_error {
    ($method:ident, $input:expr, $expected:expr, $t:ty | $precision:expr ) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output).expect("Should not emit error");

        let output = String::from_utf8(output).expect("Not UTF-8");

        let actual: $t = output.parse().unwrap();
        let expected: $t = $expected.parse().unwrap();

        assert_eq_with_error!(actual, expected, $precision);
    }};
}

pub trait GenericInteger:
    Copy + PartialEq + FromStr + Display + Rem<Output = Self> + Div<Output = Self> + Mul<Output = Self>
{
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
pub fn gcd<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    if b == T::zero() {
        a
    } else {
        gcd(b, a % b)
    }
}

#[allow(dead_code)]
#[inline]
pub fn lcm<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    a / gcd(a, b) * b
}

pub trait IterExt<T>
where
    T: Display,
{
    fn easy_join(&mut self, separator: &str) -> String;
}

impl<TItem, TTrait> IterExt<TItem> for TTrait
where
    TItem: Display,
    TTrait: Iterator<Item = TItem>,
{
    #[inline]
    fn easy_join(&mut self, separator: &str) -> String {
        self.map(|i| format!("{}", i))
            .collect::<Vec<_>>()
            .join(separator)
    }
}

pub trait VecExt<T> {
    fn add_like_string(&mut self) -> T;
}

impl<T> VecExt<T> for Vec<T>
where
    T: GenericInteger,
{
    #[inline]
    fn add_like_string(&mut self) -> T {
        if let Ok(value) = self.iter().easy_join("").parse::<T>() {
            value
        } else {
            panic!("Invalid value")
        }
    }
}

#[allow(unused_macros)]
macro_rules! swap {
    ($v1:expr, $v2:expr) => {
        let buf = $v1;
        $v1 = $v2;
        $v2 = buf;
    };
}

#[macro_export]
macro_rules! invert_index {
    ($v:expr) => {{
        let mut goal = vec![0usize; $v.len()];
        for (i, v) in $v.iter().enumerate() {
            goal[*v] = i;
        }
        goal
    }};
}

trait ThenSome: Into<bool> {
    fn then_some_<T>(self, t: T) -> Option<T> {
        if self.into() {
            Some(t)
        } else {
            None
        }
    }
}

impl ThenSome for bool {}

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let output = io::stdout();

    process(input, output).expect("Should not emit error");
}

#[allow(non_snake_case)]
fn process<R, W>(mut reader: R, mut writer: W) -> Result<()>
where
    R: BufRead,
    W: Write,
{
    type NodeIndex1Based = usize;

    input! {
        stdin = reader,
        n: NodeIndex1Based, m: usize,
        ab: [(NodeIndex1Based, NodeIndex1Based); m],
    }

    // after checking editorial

    let mut edges = HashMap::new();
    for (src, dest) in ab.iter() {
        edges.entry(*src).or_insert(vec![]).push(*dest);
        edges.entry(*dest).or_insert(vec![]).push(*src);
    }

    #[derive(Copy, Clone, PartialEq)]
    enum NodeColor {
        Red,
        Green,
        Blue,
        None,
    }

    fn find_path_dfs(
        current: NodeIndex1Based,
        edges: &HashMap<NodeIndex1Based, Vec<NodeIndex1Based>>,
        arrived_node_flags: &mut Vec<bool>,
        path: &mut Vec<NodeIndex1Based>,
    ) {
        if arrived_node_flags[current] {
            return;
        }
        arrived_node_flags[current] = true;

        path.push(current);

        for &dest in edges.get(&current).unwrap_or(&vec![]).iter() {
            find_path_dfs(dest, edges, arrived_node_flags, path);
        }
    }

    fn count_in_path_dfs(
        edges: &HashMap<NodeIndex1Based, Vec<NodeIndex1Based>>,
        path: &[NodeIndex1Based],
        node_colors: &mut Vec<NodeColor>,
    ) -> usize {
        fn inner(
            edges: &HashMap<NodeIndex1Based, Vec<NodeIndex1Based>>,
            path: &[NodeIndex1Based],
            node_colors: &mut Vec<NodeColor>,
        ) -> usize {
            let (&current, remaining_path) = match path.split_first() {
                Some(result) => result,
                None => return 1, // reached leaf
            };
            let mut result = 0;

            'color: for &color in &[NodeColor::Red, NodeColor::Green, NodeColor::Blue] {
                node_colors[current] = color;

                for &i in edges.get(&current).unwrap_or(&vec![]).iter() {
                    if node_colors[i] == node_colors[current] {
                        // this color will conflict
                        continue 'color;
                    }
                }

                result += inner(edges, &remaining_path, node_colors);
            }

            node_colors[current] = NodeColor::None;

            return result;
        }

        let &current = path.first().unwrap();

        node_colors[current] = NodeColor::Red; // check only 1 possibility
        let red_result = inner(edges, &path[1..], node_colors);
        node_colors[current] = NodeColor::None;

        return red_result * 3;
    }

    let mut arrived_node_flags = vec![false; n + 1];
    let mut answer = 1;
    let mut node_colors = vec![NodeColor::None; n + 1];

    for i in 1..=n {
        let mut path = vec![];

        find_path_dfs(i, &edges, &mut arrived_node_flags, &mut path);

        if !path.is_empty() {
            answer *= count_in_path_dfs(&edges, path.as_slice(), &mut node_colors);
        }
    }

    write!(writer, "{}", answer)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sample1() {
        assert_judge!(
            process,
            "
3 3
1 2
2 3
3 1
",
            "6"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process, "
3 0
", "27"
        );
    }

    #[test]
    fn sample3() {
        assert_judge!(
            process,
            "
4 6
1 2
2 3
3 4
2 4
1 3
1 4
",
            "0"
        );
    }

    #[test]
    fn sample4() {
        assert_judge!(
            process,
            "
20 0
",
            "3486784401"
        );
    }
}
