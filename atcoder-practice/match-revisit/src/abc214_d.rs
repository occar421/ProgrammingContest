// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::cmp::*;
use std::collections::*;
use std::fmt::{Debug, Display};
use std::hash::Hash;
#[allow(unused_imports)]
use std::iter::FromIterator;
use std::ops::*;
use std::str::FromStr;

// From https://github.com/tanakh/competitive-rs/blob/d5f51f01a6f85ddbebec4cfcb601746bee727181/src/lib.rs#L1-L92
//   and modified by this file author
#[doc(hidden)]
struct Handler<F: FnMut() -> String> {
    handle: F,
}

#[doc(hidden)]
macro_rules! prepare_input {
    (source = $s:expr) => {{
        let mut iter = $s.split_whitespace();
        Handler {
            handle: || iter.next().unwrap(),
        }
    }};
    (stdin = $s:expr) => {{
        let mut bytes = std::io::Read::bytes(std::io::BufReader::new($s));
        Handler {
            handle: move || {
                bytes
                    .by_ref()
                    .map(|r| r.unwrap() as char)
                    .skip_while(|c| c.is_whitespace())
                    .take_while(|c| !c.is_whitespace())
                    .collect::<String>()
            },
        }
    }};
}

macro_rules! input_original {
    (source = $s:expr; $($r:tt)*) => {
        let mut _handler = prepare_input!{source = $s};
        let mut _next = || (_handler.handle)();
        input_inner!{_next, $($r)*}
    };
    (stdin = $s:expr; $($r:tt)*) => {
        let mut _handler = prepare_input!{stdin = $s};
        let mut _next = || (_handler.handle)();
        input_inner!{_next, $($r)*}
    };
    (handler = $h: ident; $($r:tt)*) => {
        let mut _next = || ($h.handle)();
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

    ($next:expr, [ $t:tt ; $len1:expr ; $len2:expr ]) => {
        (0..$len1).map(|_| (0..$len2).map(|_| read_value!($next, $t)).collect::<Vec<_>>()).collect::<Vec<_>>()
    };

    ($next:expr, [ $t:tt ; $len:expr ]) => {
        (0..$len).map(|_| read_value!($next, $t)).collect::<Vec<_>>()
    };

    ($next:expr, chars) => {
        (read_value!($next, String).chars().collect::<Vec<char>>()) as Vec<char>
    };

    ($next:expr, bytes) => {
        (read_value!($next, String).into_bytes()) as Vec<u8>
    };

    ($next:expr, usize0) => {
        (read_value!($next, usize)) as usize
    };

    ($next:expr, usize1) => {
        (read_value!($next, usize) - 1) as usize
    };

    ($next:expr, $t:ty) => {
        ($next().parse::<$t>().expect("Parse error")) as $t
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

pub trait Min: PartialMin {
    fn min(&self) -> Self::Result;
}

pub trait PartialMin {
    type Result;
    fn partial_min(&self) -> Option<Self::Result>;
}

impl<T, PT> PartialMin for Option<PT>
where
    T: Ord + Copy,
    PT: PartialMin<Result = T>,
{
    type Result = T;

    #[inline]
    fn partial_min(&self) -> Option<Self::Result> {
        self.as_ref().map(|x| x.partial_min()).flatten()
    }
}

fn iter_partial_min<'a, T, PT, I>(iter: I) -> Option<T>
where
    T: Ord + Copy,
    PT: 'a + PartialMin<Result = T>,
    I: 'a + Iterator<Item = &'a PT>,
{
    iter.filter_map(|x| x.partial_min()).min()
}

impl<T, PT> PartialMin for [PT]
where
    T: Ord + Copy,
    PT: PartialMin<Result = T>,
{
    type Result = T;

    #[inline]
    fn partial_min(&self) -> Option<Self::Result> {
        iter_partial_min(self.iter())
    }
}

impl<T, PT> PartialMin for Vec<PT>
where
    T: Ord + Copy,
    PT: PartialMin<Result = T>,
{
    type Result = T;

    #[inline]
    fn partial_min(&self) -> Option<Self::Result> {
        iter_partial_min(self.iter())
    }
}

impl<T, PT> PartialMin for HashSet<PT>
where
    T: Ord + Copy,
    PT: PartialMin<Result = T>,
{
    type Result = T;

    #[inline]
    fn partial_min(&self) -> Option<Self::Result> {
        iter_partial_min(self.iter())
    }
}

pub fn min_with_partial<T>(o1: Option<T>, o2: Option<T>) -> Option<T>
where
    T: Ord,
{
    match (o1, o2) {
        (Some(v1), Some(v2)) => min(v1, v2).into(),
        (o1, None) => o1,
        (None, o2) => o2,
    }
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! min {
    ($x: expr) => (Min::min(&$x));
    ($x: expr, $($z: expr),+) => (::std::cmp::min(Min::min(&$x), min!($($z),*)));
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! partial_min {
    ($x: expr) => (PartialMin::partial_min(&$x));
    ($x: expr, $($z: expr),+) => (min_with_partial(PartialMin::partial_min(&$x), partial_min!($($z),*)));
}

pub trait Max: PartialMax {
    fn max(&self) -> Self::Result;
}

pub trait PartialMax {
    type Result;
    fn partial_max(&self) -> Option<Self::Result>;
}

impl<T, PT> PartialMax for Option<PT>
where
    T: Ord + Copy,
    PT: PartialMax<Result = T>,
{
    type Result = T;

    #[inline]
    fn partial_max(&self) -> Option<Self::Result> {
        self.as_ref().map(|x| x.partial_max()).flatten()
    }
}

fn iter_partial_max<'a, T, PT, I>(iter: I) -> Option<T>
where
    T: Ord + Copy,
    PT: 'a + PartialMax<Result = T>,
    I: 'a + Iterator<Item = &'a PT>,
{
    iter.filter_map(|x| x.partial_max()).max()
}

impl<T, PT> PartialMax for [PT]
where
    T: Ord + Copy,
    PT: PartialMax<Result = T>,
{
    type Result = T;

    #[inline]
    fn partial_max(&self) -> Option<Self::Result> {
        iter_partial_max(self.iter())
    }
}

impl<T, PT> PartialMax for Vec<PT>
where
    T: Ord + Copy,
    PT: PartialMax<Result = T>,
{
    type Result = T;

    #[inline]
    fn partial_max(&self) -> Option<Self::Result> {
        iter_partial_max(self.iter())
    }
}

impl<T, PT> PartialMax for HashSet<PT>
where
    T: Ord + Copy,
    PT: PartialMax<Result = T>,
{
    type Result = T;

    #[inline]
    fn partial_max(&self) -> Option<Self::Result> {
        iter_partial_max(self.iter())
    }
}

pub fn max_with_partial<T>(o1: Option<T>, o2: Option<T>) -> Option<T>
where
    T: Ord,
{
    match (o1, o2) {
        (Some(v1), Some(v2)) => max(v1, v2).into(),
        (o1, None) => o1,
        (None, o2) => o2,
    }
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! max {
    ($x: expr) => (Max::max(&$x));
    ($x: expr, $($z: expr),+) => (::std::cmp::max(Max::max(&$x), max!($($z),*)));
}

#[allow(unused_macros)]
#[macro_export]
macro_rules! partial_max {
    ($x: expr) => (PartialMax::partial_max(&$x));
    ($x: expr, $($z: expr),+) => (max_with_partial(PartialMax::partial_max(&$x), partial_max!($($z),*)));
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
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + MulAssign
    + Div<Output = Self>
    + DivAssign
    + Rem<Output = Self>
    + RemAssign
{
    fn zero() -> Self;
    fn one() -> Self;
}

#[doc(hidden)]
macro_rules! implement_generic_integer {
    () => {};
    ($t:ty $(, $r:ty)*) => {
        impl GenericInteger for $t {
            #[inline]
            fn zero() -> Self { 0 }

            #[inline]
            fn one() -> Self { 1 }
        }

        impl PartialMin for $t {
            type Result = $t;

            #[inline]
            fn partial_min(&self) -> Option<Self::Result> {
                self.clone().into()
            }
        }

        impl Min for $t {
            #[inline]
            fn min(&self) -> Self::Result {
                self.clone()
            }
        }

        impl PartialMax for $t {
            type Result = $t;

            #[inline]
            fn partial_max(&self) -> Option<Self::Result> {
                self.clone().into()
            }
        }

        impl Max for $t {
            #[inline]
            fn max(&self) -> Self::Result {
                self.clone()
            }
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

/// O(√N)
#[allow(dead_code)]
pub fn prime_factorize(n: usize) -> HashMap<usize, usize> {
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

const INC: [usize; 8] = [4, 2, 4, 2, 4, 6, 2, 6];

// https://memo.sugyan.com/entry/2021/02/06/021949
/// O(N log(logN) )
#[allow(dead_code)]
pub fn eratosthenes_sieve(n: usize) -> Vec<usize> {
    if n < 7 {
        return [2, 3, 5]
            .iter()
            .filter_map(|&x| (x <= n).then_some_(x))
            .collect();
    }
    let nf = n as f64;
    let mut primes = Vec::with_capacity((nf / nf.ln() * 1.2).floor() as usize);
    primes.push(2);
    primes.push(3);
    primes.push(5);
    let mut unmarked_numbers = vec![true; n + 1];

    // Wheel factorization
    let mut p = 7 - INC.last().unwrap();
    for i in INC.len() - 1.. {
        p += INC[i % INC.len()];

        if p > n {
            break;
        }

        if !unmarked_numbers[p] {
            continue;
        }

        primes.push(p);
        for px in (p * p..=n).step_by(p) {
            unmarked_numbers[px] = false;
        }
    }

    primes
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

// From https://qiita.com/hatoo@github/items/fa14ad36a1b568d14f3e
#[derive(PartialEq, PartialOrd)]
struct Total<T>(T);

impl<T: PartialEq> Eq for Total<T> {}

impl<T: PartialOrd> Ord for Total<T> {
    fn cmp(&self, other: &Total<T>) -> Ordering {
        self.0.partial_cmp(&other.0).unwrap()
    }
}

pub mod union_find {
    //! UnionFind
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_union_find.rs

    pub use self::mapped::UnionFindMapped as UnionFind;

    mod core {
        #[derive(Debug)]
        enum Node {
            Root { size: usize, index: usize },
            Children { parent: usize },
        }

        #[derive(Debug)]
        pub struct UnionFindCore {
            nodes: Vec<Node>,
        }

        impl UnionFindCore {
            pub fn new(n: usize) -> Self {
                UnionFindCore {
                    nodes: (0..n).map(|i| Node::Root { size: 1, index: i }).collect(),
                }
            }

            /// O( log(N) )
            /// Due to its immutability, it can't be O( α(N) ) by path compression
            pub fn get_root_of(&self, i: usize) -> Option<usize> {
                match self.nodes.get(i)? {
                    &Node::Root { index, .. } => Some(index),
                    &Node::Children { parent } => self.get_root_of(parent),
                }
            }

            pub fn get_size_of(&self, i: usize) -> Option<usize> {
                match self.nodes[self.get_root_of(i)?] {
                    Node::Root { size, .. } => size.into(),
                    _ => panic!("Illegal condition"),
                }
            }

            /// O( log(N) )
            pub fn connect_between(&mut self, a: usize, b: usize) -> Option<bool> {
                let mut a = self.get_root_of(a)?;
                let mut b = self.get_root_of(b)?;
                if a == b {
                    // already in the same union
                    return Some(false);
                }

                // Nodes with `a` and `b` must exist assured by ? op

                if self.get_size_of(a) < self.get_size_of(b) {
                    swap!(a, b);
                }

                self.nodes[a] = match self.nodes[a] {
                    Node::Root { size, index } => Node::Root {
                        size: size + self.get_size_of(b).unwrap(),
                        index,
                    },
                    _ => panic!("Illegal condition"),
                };
                self.nodes[b] = Node::Children { parent: a };

                return Some(true);
            }

            pub fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &usize> + 'a> {
                Box::new(self.nodes.iter().filter_map(|node| match node {
                    Node::Root { index, .. } => Some(index),
                    Node::Children { .. } => None,
                }))
            }
        }
    }

    mod mapped {
        use super::core::UnionFindCore;
        use std::borrow::Borrow;
        use std::collections::{HashMap, HashSet};
        use std::fmt::{Debug, Formatter};
        use std::hash::Hash;
        use std::iter::FromIterator;

        pub struct UnionFindMapped<'s, N: PartialEq + Hash + Debug> {
            core: UnionFindCore,
            map: HashMap<&'s N, usize>,
            r_map: HashMap<usize, &'s N>,
        }

        impl<'s, N: Hash + Eq + Debug> UnionFindMapped<'s, N> {
            pub fn from_set(set: &'s HashSet<N>) -> Self {
                let labelled_values = set.iter().enumerate();

                Self {
                    core: UnionFindCore::new(set.len()),
                    map: HashMap::from_iter(labelled_values.clone().map(|(i, x)| (x, i))),
                    r_map: HashMap::from_iter(labelled_values),
                }
            }

            /// O( log(N) )
            pub fn get_root_of(&self, node: impl Borrow<N>) -> Option<&N> {
                let core_node = *self.map.get(node.borrow())?;
                let core_root = self.core.get_root_of(core_node)?;
                Some(self.r_map[&core_root])
            }

            pub fn get_size_of(&self, node: impl Borrow<N>) -> Option<usize> {
                let core_node = *self.map.get(node.borrow())?;
                self.core.get_size_of(core_node)
            }

            /// O( log(N) )
            pub fn connect_between(
                &mut self,
                a: impl Borrow<N>,
                b: impl Borrow<N>,
            ) -> Option<bool> {
                let core_a = *self.map.get(a.borrow())?;
                let core_b = *self.map.get(b.borrow())?;
                self.core.connect_between(core_a, core_b)
            }

            pub fn get_roots<'a>(&'a self) -> Box<dyn Iterator<Item = &N> + 'a> {
                Box::new(
                    self.core
                        .get_roots()
                        .map(move |core_root| self.r_map[core_root]),
                )
            }

            #[inline]
            #[allow(dead_code)]
            fn union(&mut self, a: impl Borrow<N>, b: impl Borrow<N>) -> Option<bool> {
                self.connect_between(a, b)
            }
            #[inline]
            #[allow(dead_code)]
            fn find(&self, node: impl Borrow<N>) -> Option<&N> {
                self.get_root_of(node)
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
    }
}

// -- end of helpers

fn main() {
    use std::io::*;

    let stdio = stdin();
    let input = stdio.lock();

    let mut stdout = stdout();
    let output = BufWriter::new(stdout.lock());

    process(input, output).expect("Should not emit error");
    stdout.flush().unwrap();
}

#[allow(non_snake_case, unused_mut, unused_variables)]
fn process<R, W>(reader: R, mut writer: W) -> std::io::Result<()>
where
    R: std::io::BufRead,
    W: std::io::Write,
{
    let mut _handler = prepare_input! { stdin = reader };
    #[allow(unused_macros)]
    macro_rules! input {
        ($($r:tt)*) => {
            input_original! { handler = _handler; $($r)* }
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
        input! {
            n: usize,
            mut uvw: [(usize1, usize1, usize); n - 1],
        }

        uvw.sort_by_key(|x| x.2);

        let nodes = HashSet::from_iter((0..n).into_iter());
        let mut uf = union_find::UnionFind::from_set(&nodes);

        let mut result = 0;
        for &(u, v, w) in uvw.iter() {
            let prev_u_size = uf.get_size_of(u).unwrap();
            let prev_v_size = uf.get_size_of(v).unwrap();
            uf.connect_between(u, v);
            result += (prev_u_size * prev_v_size) * w;
        }

        println!("{}", result);
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
3
1 2 10
2 3 20
",
            "50"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
5
1 2 1
2 3 2
4 2 5
3 5 14
",
            "76"
        );
    }
}
