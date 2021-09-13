// Macro by MasuqaT (occar421)
// https://github.com/occar421/ProgrammingContest/tree/master/templates/src/standard_io.rs

use std::cmp::*;
use std::collections::*;
use std::fmt::{Debug, Display};
use std::hash::Hash;
#[allow(unused_imports)]
use std::iter::FromIterator;
use std::iter::{Product, Sum};
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

    ($next:expr, (Point2d<$t:tt>)) => {
        {
            let x = read_value!($next, $t);
            let y = read_value!($next, $t);
            Point2d { x, y }
        }
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

macro_rules! impl_collection_util {
    ($tr: tt :: $met: ident -> $ret: tt where $req: tt { $proc: ident }, []) => {};
    ($tr: tt :: $met: ident -> $ret: tt where $req: tt { $proc: ident }, [ $t: tt $(, $r:tt)* ]) => {
        impl<T, PT> $tr for $t<PT>
        where
            T: $req,
            PT: $tr<Result = T>,
        {
            type Result = T;

            #[inline]
            fn $met(&self) -> $ret<Self::Result> {
                $proc(self)
            }
        }

        impl<T, PT> $tr for &$t<PT>
        where
            T: $req,
            PT: $tr<Result = T>,
        {
            type Result = T;

            #[inline]
            fn $met(&self) -> $ret<Self::Result> {
                $proc(*self)
            }
        }

        impl_collection_util!($tr::$met -> $ret where $req {$proc}, [ $( $r ),* ]);
    };
}

type Slice<T> = [T];
type Id<T> = T;

pub trait Min: PartialMin {
    fn min(&self) -> Self::Result;
}

pub trait PartialMin {
    type Result;
    fn partial_min(&self) -> Option<Self::Result>;
}

fn iter_partial_min<'a, T, PT, I>(iter: I) -> Option<T>
where
    T: Ord,
    PT: 'a + PartialMin<Result = T>,
    I: 'a + IntoIterator<Item = &'a PT>,
{
    iter.into_iter().filter_map(|x| x.partial_min()).min()
}

impl_collection_util!(
    PartialMin::partial_min -> Option where Ord { iter_partial_min },
    [Option, Slice, Vec, HashSet]
);

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

fn iter_partial_max<'a, T, PT, I>(iter: I) -> Option<T>
where
    T: Ord,
    PT: 'a + PartialMax<Result = T>,
    I: 'a + IntoIterator<Item = &'a PT>,
{
    iter.into_iter().filter_map(|x| x.partial_max()).max()
}

impl_collection_util!(
    PartialMax::partial_max -> Option where Ord { iter_partial_max },
    [Option, Slice, Vec, HashSet]
);

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

pub trait AutoSum {
    type Result;
    fn sum(&self) -> Self::Result;
}

fn iter_auto_sum<'a, T, ST, I>(iter: I) -> T
where
    T: Sum,
    ST: 'a + AutoSum<Result = T>,
    I: 'a + IntoIterator<Item = &'a ST>,
{
    iter.into_iter().map(|x| x.sum()).sum()
}

impl_collection_util!(
    AutoSum::sum -> Id where Sum { iter_auto_sum },
    [Option, Slice, Vec, HashSet]
);

#[allow(unused_macros)]
#[macro_export]
macro_rules! sum {
    ($x: expr) => (AutoSum::sum(&$x));
    ($x: expr, $($z: expr),+) => (AutoSum::sum(&$x) + sum!($($z),*));
}

pub trait AutoProduct {
    type Result;
    fn product(&self) -> Self::Result;
}

fn iter_auto_product<'a, T, ST, I>(iter: I) -> T
where
    T: Product,
    ST: 'a + AutoProduct<Result = T>,
    I: 'a + IntoIterator<Item = &'a ST>,
{
    iter.into_iter().map(|x| x.product()).product()
}

impl_collection_util!(
    AutoProduct::product -> Id where Product { iter_auto_product },
    [Option, Slice, Vec, HashSet]
);

#[allow(unused_macros)]
#[macro_export]
macro_rules! product {
    ($x: expr) => (AutoProduct::product(&$x));
    ($x: expr, $($z: expr),+) => (AutoProduct::product(&$x) * product!($($z),*));
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
    fn is_odd(&self) -> bool;
    fn is_even(&self) -> bool;
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

            #[inline]
            fn is_odd(&self) -> bool { self % 2 == 1 }

            #[inline]
            fn is_even(&self) -> bool { self % 2 == 0 }
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

        impl AutoSum for $t {
            type Result = $t;

            #[inline]
            fn sum(&self) -> Self {
                self.clone()
            }
        }

        impl AutoProduct for $t {
            type Result = $t;

            #[inline]
            fn product(&self) -> Self {
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
    gcd_lcm(a, b).1
}

#[inline]
pub fn gcd_lcm<T>(a: T, b: T) -> (T, T)
where
    T: GenericInteger,
{
    if a == T::zero() && b == T::zero() {
        return (T::zero(), T::zero());
    }
    let gcd = gcd(a, b);
    let lcm = a * (b / gcd);
    return (gcd, lcm);
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

pub trait Then: Into<bool> {
    fn then_<T, F>(self, f: F) -> Option<T>
    where
        F: Fn() -> T,
    {
        if self.into() {
            Some(f())
        } else {
            None
        }
    }
}

impl Then for bool {}

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

#[allow(unused_macros)]
macro_rules! dbg_raw {
    () => {
        #[cfg(debug_assertions)]
        eprintln!();
    };
    ($a:expr) => {
        #[cfg(debug_assertions)]
        eprintln!("{:?}", $a);
    };
    ($a:expr, $($b:expr),+ $(,)*) => {
        #[cfg(debug_assertions)]
        eprint!("{:?}", $a);

        dbg_raw!($($b),+);
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

pub fn index_to_ascii_gen(base: char) -> impl Fn(usize) -> char {
    move |index| (index as u8 + base as u8) as char
}

pub fn ascii_to_index_gen(base: char) -> impl Fn(char) -> usize {
    move |ascii| ascii as usize - base as usize
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default)]
pub struct Point2d<T> {
    pub x: T,
    pub y: T,
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
            t: usize,
        }

        for _ in 0..t {
            input! {
                n: usize, k: usize,
                a: [usize; n],
            }

            let mut nums = HashMap::new();
            for (i, &a_i) in a.iter().enumerate() {
                nums.entry(a_i).or_insert(vec![]).push(i);
            }

            let mut result = vec![0; n];

            for pos_s in nums.values().filter(|nums| nums.len() >= k) {
                for i in 0..k {
                    let color = i + 1;
                    result[pos_s[i]] = color;
                }
            }

            let less_s: Vec<_> = nums.values().filter(|num| num.len() < k).collect();
            let less_num: usize = less_s.iter().map(|num| num.len()).sum();

            let mut i = 0;
            'a: for pos_s in less_s.iter() {
                for &pos in pos_s.iter() {
                    let color = i % k + 1;
                    result[pos] = color;

                    i += 1;
                    if i >= less_num / k * k {
                        break 'a;
                    }
                }
            }

            for x in result.iter() {
                print!("{} ", x);
            }

            println!();
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    //     #[test]
    //     fn sample1() {
    //         assert_judge!(
    //             process,
    //             "
    // 6
    // 10 3
    // 3 1 1 1 1 10 3 10 10 2
    // 4 4
    // 1 1 1 1
    // 1 1
    // 1
    // 13 1
    // 3 1 4 1 5 9 2 6 5 3 5 8 9
    // 13 2
    // 3 1 4 1 5 9 2 6 5 3 5 8 9
    // 13 3
    // 3 1 4 1 5 9 2 6 5 3 5 8 9
    // ",
    //             "
    // 1 1 0 2 3 2 2 1 3 3
    // 4 2 1 3
    // 1
    // 0 0 1 1 0 1 1 1 0 1 1 1 0
    // 2 1 2 2 1 1 1 1 2 1 0 2 2
    // 1 1 3 2 1 3 3 1 2 2 3 2 0
    // "
    //         );
    //     }

    #[test]
    fn ex1() {
        assert_judge!(
            process,
            "
6
10 3
3 1 1 1 1 10 3 10 10 2
4 4
1 1 1 1
1 1
1
13 1
3 1 4 1 5 9 2 6 5 3 5 8 9
13 2
3 1 4 1 5 9 2 6 5 3 5 8 9
13 3
3 1 4 1 5 9 2 6 5 3 5 8 9
",
            "
2 1 2 3 0 1 3 2 3 1
1 2 3 4
1
1 1 1 0 1 1 1 1 0 0 0 1 0
1 1 2 2 1 1 1 1 2 2 0 2 2
1 1 3 2 1 3 3 1 2 2 3 2 0
"
        );
    }

    #[test]
    fn ex2() {
        assert_judge!(
            process,
            "
1
10 3
1 1 1 1 1 1 1 1 1 1
",
            "
1 2 3 0 0 0 0 0 0 0
"
        );
    }
}
