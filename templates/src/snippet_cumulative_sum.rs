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

    pub struct CumulativeSum1dGenerator<T>
    where
        T: GenericInteger,
    {
        cum_sum: Vec<T>,
        data_length: Length,
    }

    impl<GI> CumulativeSum1dGenerator<GI>
    where
        GI: GenericInteger,
    {
        #[inline]
        pub fn new(length: Length, source: &Vec<GI>) -> Self {
            Self::new_with_evaluator(length, |i| source[i])
        }

        pub fn new_with_evaluator<F>(length: Length, evaluator: F) -> Self
        where
            F: Fn(usize) -> GI,
        {
            let mut cum_sum = nested_vec![GI::zero(); length + 1];

            for i in 0..length {
                cum_sum[i + 1] = cum_sum[i] + evaluator(i);
            }

            Self {
                cum_sum: cum_sum,
                data_length: length,
            }
        }

        pub fn sum_in(&self, range: impl RangeBounds<usize>) -> GI {
            use std::ops::Bound::*;

            let range = {
                let start = match range.start_bound() {
                    Unbounded => 0,
                    Included(&n) => n,
                    Excluded(&n) => n + 1,
                };
                let end = match range.end_bound() {
                    Unbounded => self.data_length,
                    Included(&n) => n + 1,
                    Excluded(&n) => n,
                };

                start..end
            };

            debug_assert!(range.start <= range.end);

            self.cum_sum[range.end] - self.cum_sum[range.start]
        }
    }

    pub struct CumulativeSum2dGenerator<T>
    where
        T: GenericInteger,
    {
        cum_sum: Vec<Vec<T>>,
        data_height: Length,
        data_width: Length,
    }

    impl<GI> CumulativeSum2dGenerator<GI>
    where
        GI: GenericInteger,
    {
        #[inline]
        pub fn new(height: Length, width: Length, source: &Vec<Vec<GI>>) -> Self {
            Self::new_with_evaluator(height, width, |i, j| source[i][j])
        }

        pub fn new_with_evaluator<F>(height: Length, width: Length, evaluator: F) -> Self
        where
            F: Fn(usize, usize) -> GI,
        {
            let mut cum_sum = nested_vec![GI::zero(); height + 1; width + 1];

            for i in 0..height {
                for j in 0..width {
                    cum_sum[i + 1][j + 1] =
                        cum_sum[i + 1][j] + cum_sum[i][j + 1] - cum_sum[i][j] + evaluator(i, j);
                }
            }

            Self {
                cum_sum: cum_sum,
                data_height: height,
                data_width: width,
            }
        }

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
                    Unbounded => self.data_height,
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
                    Unbounded => self.data_width,
                    Included(&n) => n + 1,
                    Excluded(&n) => n,
                };

                horizontal_start..horizontal_end
            };

            debug_assert!(vertical_range.start <= vertical_range.end);
            debug_assert!(horizontal_range.start <= horizontal_range.end);

            self.cum_sum[vertical_range.end][horizontal_range.end]
                + self.cum_sum[vertical_range.start][horizontal_range.start]
                - self.cum_sum[vertical_range.end][horizontal_range.start]
                - self.cum_sum[vertical_range.start][horizontal_range.end]
        }
    }
}
