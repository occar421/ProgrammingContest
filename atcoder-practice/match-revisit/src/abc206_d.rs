// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::io;
use std::io::{BufRead, BufWriter, Result, Write};
use std::ops::{Add, Div, Mul, Rem, Sub};
use std::str::FromStr;

pub type NodeIndex0Based = usize;
pub type NodeIndex1Based = usize;
pub type Quantity = usize;
pub type Length = usize;
pub type ArrayIndex0Based = usize;
pub type ArrayIndex1Based = usize;
pub type Weight = usize;

// From https://github.com/tanakh/competitive-rs/blob/d5f51f01a6f85ddbebec4cfcb601746bee727181/src/lib.rs#L1-L92
//   and modified by this file author
macro_rules! input_original {
    (source = $s:expr; $($r:tt)*) => {
        let mut iter = $s.split_whitespace();
        let mut _next = || { iter.next().unwrap() };
        input_inner!{_next, $($r)*}
    };
    (stdin = $s:expr; $($r:tt)*) => {
        let mut bytes = std::io::Read::bytes(std::io::BufReader::new($s));
        let mut _next = move || -> String{
            bytes
                .by_ref()
                .map(|r|r.unwrap() as char)
                .skip_while(|c|c.is_whitespace())
                .take_while(|c|!c.is_whitespace())
                .collect()
        };
        input_inner!{_next, $($r)*}
    };
}

#[doc(hidden)]
macro_rules! input_inner {
    ($next:expr) => {};
    ($next:expr, ) => {};

    ($next:expr, $var:ident : $t:tt $($r:tt)*) => {
        let $var = read_value!($next, $t);
        input_inner!{$next $($r)*}
    };
    ($next:expr, mut $var:ident : $t:tt $($r:tt)*) => {
        let mut $var = read_value!($next, $t);
        input_inner!{$next $($r)*}
    };
}

#[doc(hidden)]
macro_rules! read_value {
    ($next:expr, ( $($t:tt),* )) => {
        ( $(read_value!($next, $t)),* )
    };

    ($next:expr, [ $t:tt ; $len:expr ]) => {
        (0..$len).map(|_| read_value!($next, $t)).collect::<Vec<_>>()
    };

    ($next:expr, chars) => {
        read_value!($next, String).chars().collect::<Vec<char>>()
    };

    ($next:expr, bytes) => {
        read_value!($next, String).into_bytes()
    };

    ($next:expr, usize1) => {
        read_value!($next, usize) - 1
    };

    ($next:expr, $t:ty) => {
        $next().parse::<$t>().expect("Parse error")
    };
}

#[allow(unused_macros)]
macro_rules! assert_judge {
    ($method:ident, $input:expr, $expected:expr) => {{
        let output = assert_judge_with_output!($method, $input);

        assert_eq!(output, $expected.trim());
    }};
}

#[allow(unused_macros)]
macro_rules! assert_judge_with_output {
    ($method:ident, $input:expr) => {{
        let input = $input.as_bytes();
        let mut output = Vec::new();

        $method(&input[..], &mut output).expect("Should not emit error");

        String::from_utf8(output)
            .expect("Not UTF-8")
            .trim()
            .to_string()
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
                    // The re-borrows below are intentional. Without them, the stack slot for the
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
        let output = assert_judge_with_output!($method, $input);

        let actual: $t = output.parse().unwrap();
        let expected: $t = $expected.parse().unwrap();

        assert_eq_with_error!(actual, expected, $precision);
    }};
}

pub trait GenericInteger:
    Copy
    + Clone
    + Eq
    + PartialEq
    + Ord
    + PartialOrd
    + Hash
    + FromStr
    + Display
    + Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
{
    fn zero() -> Self;
    fn one() -> Self;
}

macro_rules! implement_generic_integer {
    () => {};
    ($t:ty $(, $r:ty)*) => {
        impl GenericInteger for $t {
            #[inline]
            fn zero() -> Self { 0 }

            #[inline]
            fn one() -> Self { 1 }
        }

        implement_generic_integer![ $( $r ),* ];
    };
}

implement_generic_integer![u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize];

#[allow(dead_code)]
pub fn gcd<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    if b == T::zero() {
        a
    } else {
        gcd(b, a % b.clone())
    }
}

#[allow(dead_code)]
#[inline]
pub fn lcm<T>(a: T, b: T) -> T
where
    T: GenericInteger,
{
    a / gcd(a.clone(), b) * b.clone()
}

#[allow(dead_code)]
pub fn prime_factorize(n: usize) -> HashMap<usize, Quantity> {
    let mut map = HashMap::new();

    let sqrt_n = (n as f64).sqrt().ceil() as usize;

    let mut n = n;
    for p in 2..=sqrt_n {
        if n % p != 0 {
            continue;
        }

        let mut exp_number = 0;
        while n % p == 0 {
            exp_number += 1;
            n /= p;
        }

        map.insert(p, exp_number);
    }

    if n != 1 {
        map.insert(n, 1);
    }

    map
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
#[macro_export]
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

pub trait ThenSome: Into<bool> {
    fn then_some_<T>(self, t: T) -> Option<T> {
        if self.into() {
            Some(t)
        } else {
            None
        }
    }
}

impl ThenSome for bool {}

// From https://kuretchi.hateblo.jp/entry/rust_nested_vec
#[allow(unused_macros)]
macro_rules! nested_vec {
    ($e:expr; $n:expr) => {
        vec![$e; $n]
    };
    ($e:expr; $n:expr $(; $m:expr)+) => {
        vec![nested_vec!($e $(; $m)+); $n]
    };
}

// From https://maguro.dev/debug-macro/ with some modification
#[allow(unused_macros)]
macro_rules! dbg {
    () => {
        #[cfg(debug_assertions)]
        eprintln!();
    };
    ($($a:expr),* $(,)*) => {
        #[cfg(debug_assertions)]
        eprintln!(concat!($("| ", stringify!($a), "={:?} "),*, "|"), $(&$a),*);
    };
}

pub mod union_find {
    //! UnionFind
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_union_find.rs

    use super::{NodeIndex0Based, Quantity};
    use std::collections::HashSet;
    use std::fmt::Debug;
    use std::hash::Hash;

    pub trait UnionFind<N: Hash + Eq>: Debug {
        fn get_root_of(&self, node: &N) -> Option<&N>;
        fn get_size_of(&self, node: &N) -> Option<Quantity>;
        fn connect_between(&mut self, a: &N, b: &N) -> Option<bool>;
        fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &N> + 'a>;

        #[inline]
        fn union(&mut self, a: &N, b: &N) -> Option<bool> {
            self.connect_between(a, b)
        }
        #[inline]
        fn find(&self, node: &N) -> Option<&N> {
            self.get_root_of(node)
        }
    }

    pub fn new_with_indices(n: Quantity) -> impl UnionFind<NodeIndex0Based> {
        plain::UnionFindPlain::new(n)
    }

    pub fn new_from_set<'a, N: Hash + Eq + Debug>(set: &'a HashSet<N>) -> impl UnionFind<N> + 'a {
        mapped::UnionFindMapped::new(set)
    }

    mod plain {
        use super::super::{NodeIndex0Based, Quantity};
        use super::UnionFind;

        #[derive(Debug)]
        enum Node {
            Root {
                size: Quantity,
                index: NodeIndex0Based,
            },
            Children {
                parent: NodeIndex0Based,
            },
        }

        #[derive(Debug)]
        pub struct UnionFindPlain {
            nodes: Vec<Node>,
        }

        impl UnionFindPlain {
            pub fn new(n: Quantity) -> Self {
                UnionFindPlain {
                    nodes: (0..n).map(|i| Node::Root { size: 1, index: i }).collect(),
                }
            }
        }

        impl UnionFind<NodeIndex0Based> for UnionFindPlain {
            /// O( log(N) )
            /// Due to its immutability, it can't be O( α(N) ) by path compression
            fn get_root_of(&self, i: &NodeIndex0Based) -> Option<&NodeIndex0Based> {
                match self.nodes.get(*i)? {
                    Node::Root { index, .. } => Some(index),
                    Node::Children { parent } => self.get_root_of(parent),
                }
            }

            fn get_size_of(&self, i: &NodeIndex0Based) -> Option<Quantity> {
                match self.nodes[*self.get_root_of(i)?] {
                    Node::Root { size, .. } => size.into(),
                    _ => panic!("Illegal condition"),
                }
            }

            /// O( log(N) )
            fn connect_between(
                &mut self,
                a: &NodeIndex0Based,
                b: &NodeIndex0Based,
            ) -> Option<bool> {
                let mut a = *self.get_root_of(a)?;
                let mut b = *self.get_root_of(b)?;
                if a == b {
                    // already in the same union
                    return Some(false);
                }

                // Nodes with `a` and `b` must exist assured by ? op

                if self.get_size_of(&a) < self.get_size_of(&b) {
                    swap!(a, b);
                }

                self.nodes[a] = match self.nodes[a] {
                    Node::Root { size, index } => Node::Root {
                        size: size + self.get_size_of(&b).unwrap(),
                        index,
                    },
                    _ => panic!("Illegal condition"),
                };
                self.nodes[b] = Node::Children { parent: a };

                return Some(true);
            }

            fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &NodeIndex0Based> + 'a> {
                Box::new(self.nodes.iter().filter_map(|node| match node {
                    Node::Root { index, .. } => Some(index),
                    Node::Children { .. } => None,
                }))
            }
        }
    }

    mod mapped {
        use super::super::{NodeIndex0Based, Quantity};
        use super::plain::UnionFindPlain;
        use super::UnionFind;
        use std::collections::{HashMap, HashSet};
        use std::fmt::{Debug, Formatter};
        use std::hash::Hash;
        use std::iter::FromIterator;

        pub struct UnionFindMapped<'a, N> {
            core: UnionFindPlain,
            map: HashMap<&'a N, NodeIndex0Based>,
            r_map: HashMap<NodeIndex0Based, &'a N>,
        }

        impl<'a, N: Hash + Eq + Debug> UnionFindMapped<'a, N> {
            pub fn new(set: &'a HashSet<N>) -> Self {
                let labelled_values = set.iter().enumerate();

                UnionFindMapped {
                    core: UnionFindPlain::new(set.len()),
                    map: HashMap::from_iter(labelled_values.clone().map(|(i, x)| (x, i))),
                    r_map: HashMap::from_iter(labelled_values),
                }
            }
        }

        impl<N: Hash + Eq + Debug> Debug for UnionFindMapped<'_, N> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                writeln!(f, "UnionFindMapped {{")?;
                writeln!(f, "  map: {:?}", self.map)?;
                writeln!(f, "  r_map: {:?}", self.r_map)?;
                writeln!(f, "  core: {:?}", self.core)?;
                writeln!(f, "}}")
            }
        }

        impl<N: Hash + Eq + Debug> UnionFind<N> for UnionFindMapped<'_, N> {
            fn get_root_of(&self, node: &N) -> Option<&N> {
                let core_node = *self.map.get(&node)?;
                let core_root = self.core.get_root_of(&core_node)?;
                Some(&self.r_map[core_root])
            }

            fn get_size_of(&self, node: &N) -> Option<Quantity> {
                let core_node = *self.map.get(node)?;
                self.core.get_size_of(&core_node)
            }

            fn connect_between(&mut self, a: &N, b: &N) -> Option<bool> {
                let core_a = *self.map.get(&a)?;
                let core_b = *self.map.get(&b)?;
                self.core.connect_between(&core_a, &core_b)
            }

            fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &N> + 'a> {
                Box::new(
                    self.core
                        .get_roots()
                        .map(move |core_root| self.r_map[core_root]),
                )
            }
        }
    }
}

// -- end of helpers

fn main() {
    let stdio = io::stdin();
    let input = stdio.lock();

    let mut stdout = io::stdout();
    let output = BufWriter::new(stdout.lock());

    process(input, output).expect("Should not emit error");
    stdout.flush().unwrap();
}

#[allow(non_snake_case)]
fn process<R, W>(reader: R, mut writer: W) -> Result<()>
where
    R: BufRead,
    W: Write,
{
    #[allow(unused_macros)]
    macro_rules! input {
        ($($r:tt)*) => {
            input_original! { stdin = reader; $($r)* }
        };
    }
    #[allow(unused_macros)]
    macro_rules! print {
        ($($arg:tt)*) => {
            write!(writer, $($arg)*)?;
        }
    }
    #[allow(unused_macros)]
    macro_rules! println {
        () => {
            writeln!(writer)?;
        };
        ($($arg:tt)*) => {
            writeln!(writer, $($arg)*)?;
        }
    }

    {
        use std::collections::HashSet;
        use std::iter::FromIterator;
        use union_find::UnionFind;

        input! {
            n: Length,
            a: [usize; n],
        }

        let set = HashSet::from_iter(a.clone());
        let mut uf = union_find::new_from_set(&set);
        for i in 0..(n / 2) {
            uf.connect_between(&a[i], &a[n - i - 1]);
        }

        println!("{}", set.len() - uf.get_roots().count());
    }

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
8
1 5 3 2 5 2 3 1",
            "2"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
7
1 2 3 4 1 2 3",
            "1"
        );
    }

    #[test]
    fn sample3() {
        assert_judge!(
            process,
            "
1
200000",
            "0"
        );
    }

    #[test]
    fn test1() {
        assert_judge!(
            process,
            "
8
1 2 3 2 3 19 1 19",
            "3"
        );
    }
}
