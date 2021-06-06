use crate::standard_io::{GenericInteger, Length};

macro_rules! nested_vec {
  ($e:expr; $n:expr) => {
    vec![$e; $n]
  };
  ($e:expr; $n:expr $(; $m:expr)+) => {
    vec![nested_vec!($e $(; $m)+); $n]
  };
}

pub mod cumulative_sum {
    //! CumulativeSum
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_cumulative_sum.rs

    use super::{GenericInteger, Length};
    use std::ops::RangeBounds;

    pub struct CumulativeSum1d<T>
    where
        T: GenericInteger,
    {
        cum_sum: Vec<T>,
        source_length: Length,
    }

    impl<GI> CumulativeSum1d<GI>
    where
        GI: GenericInteger,
    {
        /// O( N )
        #[inline]
        pub fn new(source_length: Length, source: &Vec<GI>) -> Self {
            Self::new_with_evaluator(source_length, |i| source[i])
        }

        /// O( N )
        pub fn new_with_evaluator<F>(source_length: Length, evaluator: F) -> Self
        where
            F: Fn(usize) -> GI,
        {
            let mut cum_sum = nested_vec![GI::zero(); source_length + 1];

            for i in 0..source_length {
                cum_sum[i + 1] = cum_sum[i] + evaluator(i);
            }

            Self {
                cum_sum,
                source_length,
            }
        }

        /// O(1)
        ///
        /// # Examples
        ///
        ///     source: a b c
        ///     range: 0 1 2 3
        ///
        /// `0..2` => `a + b`
        ///
        pub fn sum_in(&self, range: impl RangeBounds<usize>) -> GI {
            use std::ops::Bound::*;

            let range = {
                let start = match range.start_bound() {
                    Unbounded => 0,
                    Included(&n) => n,
                    Excluded(&n) => n + 1,
                };
                let end = match range.end_bound() {
                    Unbounded => self.source_length,
                    Included(&n) => n + 1,
                    Excluded(&n) => n,
                };

                start..end
            };

            self.cum_sum[range.end] - self.cum_sum[range.start]
        }
    }

    pub struct CumulativeSum2d<T>
    where
        T: GenericInteger,
    {
        cum_sum: Vec<Vec<T>>,
        source_height: Length,
        source_width: Length,
    }

    impl<GI> CumulativeSum2d<GI>
    where
        GI: GenericInteger,
    {
        #[inline]
        /// O(N^2)
        pub fn new(source_height: Length, source_width: Length, source: &Vec<Vec<GI>>) -> Self {
            Self::new_with_evaluator(source_height, source_width, |i, j| source[i][j])
        }

        /// O(N^2)
        pub fn new_with_evaluator<F>(
            source_height: Length,
            source_width: Length,
            evaluator: F,
        ) -> Self
        where
            F: Fn(usize, usize) -> GI,
        {
            let mut cum_sum = nested_vec![GI::zero(); source_height + 1; source_width + 1];

            for i in 0..source_height {
                for j in 0..source_width {
                    cum_sum[i + 1][j + 1] =
                        cum_sum[i + 1][j] + cum_sum[i][j + 1] - cum_sum[i][j] + evaluator(i, j);
                }
            }

            Self {
                cum_sum,
                source_height,
                source_width,
            }
        }

        /// O(1)
        ///
        /// # Examples
        ///     source:   a b c
        ///               d e f
        ///               g h i
        ///     h_range: 0 1 2 3
        ///
        /// `0..2, 0..2` => `a + b + d + e`
        ///
        pub fn sum_in(
            &self,
            vertical_range: impl RangeBounds<usize>,
            horizontal_range: impl RangeBounds<usize>,
        ) -> GI {
            use std::ops::Bound::*;

            let vertical_range = {
                let vertical_start = match vertical_range.start_bound() {
                    Unbounded => 0,
                    Included(&n) => n,
                    Excluded(&n) => n + 1,
                };
                let vertical_end = match vertical_range.end_bound() {
                    Unbounded => self.source_height,
                    Included(&n) => n + 1,
                    Excluded(&n) => n,
                };

                vertical_start..vertical_end
            };

            let horizontal_range = {
                let horizontal_start = match horizontal_range.start_bound() {
                    Unbounded => 0,
                    Included(&n) => n,
                    Excluded(&n) => n + 1,
                };
                let horizontal_end = match horizontal_range.end_bound() {
                    Unbounded => self.source_width,
                    Included(&n) => n + 1,
                    Excluded(&n) => n,
                };

                horizontal_start..horizontal_end
            };

            self.cum_sum[vertical_range.end][horizontal_range.end]
                + self.cum_sum[vertical_range.start][horizontal_range.start]
                - self.cum_sum[vertical_range.end][horizontal_range.start]
                - self.cum_sum[vertical_range.start][horizontal_range.end]
        }
    }
}
