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

pub mod adjacent {
    //! Adjacent
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_adjacent.rs

    use std::ops::Range;

    pub struct Adjacent2d<I> {
        current: (isize, isize),
        vertical_range: Range<isize>,
        horizontal_range: Range<isize>,
        iter: I,
    }

    mod adjacent_range {
        use std::ops::{Bound, Range, RangeBounds, RangeInclusive, RangeTo, RangeToInclusive};

        /// The range that unbounded ends are prohibited.
        pub trait AdjacentRange: RangeBounds<usize> {
            fn to_range(&self) -> Range<isize> {
                let start = match self.start_bound() {
                    Bound::Unbounded => 0,
                    Bound::Included(&n) => n,
                    Bound::Excluded(&n) => n + 1,
                } as isize;
                let end = match self.end_bound() {
                    Bound::Unbounded => panic!("Should not reach"),
                    Bound::Included(&n) => n + 1,
                    Bound::Excluded(&n) => n,
                } as isize;

                start..end
            }
        }
        impl AdjacentRange for RangeTo<usize> {}
        impl AdjacentRange for RangeToInclusive<usize> {}
        impl AdjacentRange for Range<usize> {}
        impl AdjacentRange for RangeInclusive<usize> {}
        impl AdjacentRange for (Bound<usize>, Bound<usize>) {}
        impl AdjacentRange for RangeTo<&usize> {}
        impl AdjacentRange for RangeToInclusive<&usize> {}
        impl AdjacentRange for Range<&usize> {}
        impl AdjacentRange for RangeInclusive<&usize> {}
        impl<'a> AdjacentRange for (Bound<&'a usize>, Bound<&'a usize>) {}
    }

    impl<'a, I> Adjacent2d<I>
    where
        I: Iterator<Item = &'a (isize, isize)>,
    {
        /// Arguments
        ///
        /// * `current`: (y, x)
        /// * `vertical_range`: y range
        /// * `horizontal_range`: x range
        pub fn new(
            current: (usize, usize),
            vertical_range: impl adjacent_range::AdjacentRange,
            horizontal_range: impl adjacent_range::AdjacentRange,
            iter: I,
        ) -> Self {
            Self {
                current: (current.0 as isize, current.1 as isize),
                vertical_range: vertical_range.to_range(),
                horizontal_range: horizontal_range.to_range(),
                iter,
            }
        }
    }

    // From https://poyopoyoyon.hatenablog.com/entry/2020/11/08/183212
    impl<'a, I> Iterator for Adjacent2d<I>
    where
        I: Iterator<Item = &'a (isize, isize)>,
    {
        type Item = (usize, usize);

        /// Returns (y, x)
        fn next(&mut self) -> Option<(usize, usize)> {
            while let Some((dy, dx)) = self.iter.next() {
                let ny = self.current.0 + dy;
                let nx = self.current.1 + dx;
                if self.vertical_range.contains(&ny) && self.horizontal_range.contains(&nx) {
                    return Some((ny as usize, nx as usize));
                }
            }
            None
        }
    }

    const A2D_4: &'static [(isize, isize)] = &[(-1, 0), (0, 1), (1, 0), (0, -1)];

    /// Arguments
    ///
    /// * `current`: (y, x)
    /// * `vertical_range`: y range
    /// * `horizontal_range`: x range
    pub fn adjacent2d_4neighbors(
        current: (usize, usize),
        vertical_range: impl adjacent_range::AdjacentRange,
        horizontal_range: impl adjacent_range::AdjacentRange,
    ) -> Adjacent2d<std::slice::Iter<'static, (isize, isize)>> {
        Adjacent2d {
            current: (current.0 as isize, current.1 as isize),
            vertical_range: vertical_range.to_range(),
            horizontal_range: horizontal_range.to_range(),
            iter: A2D_4.iter(),
        }
    }

    const A2D_8: &'static [(isize, isize)] = &[
        (-1, 0),
        (-1, 1),
        (0, 1),
        (1, 1),
        (1, 0),
        (1, -1),
        (0, -1),
        (-1, -1),
    ];

    /// Arguments
    ///
    /// * `current`: (y, x)
    /// * `vertical_range`: y range
    /// * `horizontal_range`: x range
    pub fn adjacent2d_8neighbors(
        current: (usize, usize),
        vertical_range: impl adjacent_range::AdjacentRange,
        horizontal_range: impl adjacent_range::AdjacentRange,
    ) -> Adjacent2d<std::slice::Iter<'static, (isize, isize)>> {
        Adjacent2d {
            current: (current.0 as isize, current.1 as isize),
            vertical_range: vertical_range.to_range(),
            horizontal_range: horizontal_range.to_range(),
            iter: A2D_8.iter(),
        }
    }
}

pub mod graph {
    //! Graph
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_graph.rs

    use std::collections::HashMap;
    use std::hash::Hash;
    use std::ops::Add;

    pub struct Graph<'a, Node, Cost> {
        edges: &'a HashMap<Node, Vec<(Node, Cost)>>,
    }

    impl<'a, Node, Cost> Graph<'a, Node, Cost> {
        pub fn new(edges: &'a HashMap<Node, Vec<(Node, Cost)>>) -> Self {
            Self { edges }
        }

        pub fn dijkstra(
            &self,
            start_node: Node,
            initial_cost: Cost,
        ) -> dijkstra::Dijkstra<Node, Cost>
        where
            Node: Clone + Hash + Eq,
            Cost: Clone + Ord + Add<Cost, Output = Cost>,
        {
            let mut memo = dijkstra::Dijkstra::new(self);
            memo.run(start_node, initial_cost);
            memo
        }
    }

    mod dijkstra {
        use super::Graph;
        use std::cmp::Ordering;
        use std::collections::{BinaryHeap, HashMap};
        use std::hash::Hash;
        use std::ops::Add;

        struct VisitedNodeInfo<Node, Cost> {
            cost: Cost,
            previous_node: Option<Node>,
        }

        pub struct Dijkstra<'a, Node, Cost> {
            heap: BinaryHeap<DijkstraQuery<Node, Cost>>,
            visited_nodes: HashMap<Node, VisitedNodeInfo<Node, Cost>>,
            graph: &'a Graph<'a, Node, Cost>,
        }

        impl<'a, Node, Cost> Dijkstra<'a, Node, Cost>
        where
            Node: Clone + Hash + Eq,
            Cost: Clone + Ord + Add<Cost, Output = Cost>,
        {
            pub fn new(graph: &'a Graph<'a, Node, Cost>) -> Self {
                Self {
                    heap: BinaryHeap::new(),
                    visited_nodes: HashMap::new(),
                    graph,
                }
            }

            pub fn run(&mut self, start_node: Node, initial_cost: Cost) {
                self.heap.push(DijkstraQuery {
                    cost: initial_cost,
                    node: start_node,
                    previous_node: None,
                });

                while let Some(DijkstraQuery {
                    cost,
                    node,
                    previous_node,
                }) = self.heap.pop()
                {
                    if self.visited_nodes.contains_key(&node) {
                        continue;
                    }
                    self.visited_nodes.insert(
                        node.clone(),
                        VisitedNodeInfo {
                            cost: cost.clone(),
                            previous_node,
                        },
                    );

                    if let Some(edges) = self.graph.edges.get(&node) {
                        for (dest, move_cost) in edges.iter() {
                            self.heap.push(DijkstraQuery {
                                cost: cost.clone() + move_cost.clone(),
                                node: dest.clone(),
                                previous_node: node.clone().into(),
                            });
                        }
                    }
                }
            }

            pub fn cost_to(&self, node: Node) -> Option<Cost> {
                let info = self.visited_nodes.get(&node)?;
                info.cost.clone().into()
            }

            pub fn path_to(&self, node: Node) -> Option<Vec<Node>> {
                let mut info = self.visited_nodes.get(&node)?;

                let mut v = vec![node.clone()];
                while let Some(prev) = info.previous_node.clone() {
                    v.push(prev.clone());
                    info = &self.visited_nodes[&prev]
                }

                v.reverse();
                v.into()
            }
        }

        pub struct DijkstraQuery<Node, Cost> {
            cost: Cost,
            node: Node,
            previous_node: Option<Node>,
        }

        impl<Node, Cost> PartialEq for DijkstraQuery<Node, Cost>
        where
            Cost: PartialEq,
        {
            fn eq(&self, other: &Self) -> bool {
                self.cost.eq(&other.cost)
            }
        }

        impl<Node, Cost> PartialOrd for DijkstraQuery<Node, Cost>
        where
            Cost: Ord,
        {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.cmp(&other).into()
            }
        }

        impl<Node, Cost> Eq for DijkstraQuery<Node, Cost> where Cost: PartialEq {}

        impl<Node, Cost> Ord for DijkstraQuery<Node, Cost>
        where
            Cost: Ord,
        {
            fn cmp(&self, other: &Self) -> Ordering {
                self.cost.cmp(&other.cost).reverse() // ascending
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
            h: usize, w: usize,
            s: [chars; h],
        }

        let mut punch_area = Vec::with_capacity(20);
        for i in 0..5 {
            for j in 0..5 {
                match (i == 0 || i == 4, j == 0 || j == 4) {
                    (true, true) => {}
                    _ => {
                        if !(i == 2 && j == 2) {
                            punch_area.push((i - 2, j - 2));
                        }
                    }
                }
            }
        }

        let mut edges = HashMap::new();
        for i in 0..h {
            for j in 0..w {
                edges.insert((i, j), vec![]);
            }
        }
        for i in 0..h {
            for j in 0..w {
                let edges = edges.get_mut(&(i, j)).unwrap();
                for p in adjacent::adjacent2d_4neighbors((i, j), ..h, ..w) {
                    if s[p.0][p.1] == '.' {
                        edges.push((p, 0));
                    }
                }
                for p in adjacent::Adjacent2d::new((i, j), ..h, ..w, punch_area.iter()) {
                    edges.push((p, 1));
                }
            }
        }

        let graph = graph::Graph::new(&edges);
        let result = graph.dijkstra((0, 0), 0).cost_to((h - 1, w - 1)).unwrap();
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
5 5
..#..
#.#.#
##.##
#.#.#
..#..
",
            "1"
        );
    }

    #[test]
    fn sample2() {
        assert_judge!(
            process,
            "
8 8
.#######
########
########
########
########
########
########
#######.
",
            "5"
        );
    }
}
