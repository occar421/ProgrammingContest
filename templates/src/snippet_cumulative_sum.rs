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

    pub struct CumulativeSum2d<T>
    where
        T: GenericInteger,
    {
        transformed_data: Vec<Vec<T>>,
        data_height: Length,
        data_width: Length,
    }

    impl<GI> CumulativeSum2d<GI>
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
                transformed_data: cum_sum,
                data_height: height,
                data_width: width,
            }
        }

        pub fn value_in(
            &self,
            vertical: impl RangeBounds<usize>,
            horizontal: impl RangeBounds<usize>,
        ) -> GI {
            use std::ops::Bound::*;

            let vertical = {
                let vertical_start = match vertical.start_bound() {
                    Unbounded => 0,
                    Included(&n) => n,
                    Excluded(&n) => n + 1,
                };
                let vertical_end = match vertical.end_bound() {
                    Unbounded => self.data_height,
                    Included(&n) => n + 1,
                    Excluded(&n) => n,
                };

                vertical_start..vertical_end
            };

            let horizontal = {
                let horizontal_start = match horizontal.start_bound() {
                    Unbounded => 0,
                    Included(&n) => n,
                    Excluded(&n) => n + 1,
                };
                let horizontal_end = match horizontal.end_bound() {
                    Unbounded => self.data_width,
                    Included(&n) => n + 1,
                    Excluded(&n) => n,
                };

                horizontal_start..horizontal_end
            };

            debug_assert!(vertical.start <= vertical.end);
            debug_assert!(horizontal.start <= horizontal.end);

            self.transformed_data[vertical.end][horizontal.end]
                + self.transformed_data[vertical.start][horizontal.start]
                - self.transformed_data[vertical.end][horizontal.start]
                - self.transformed_data[vertical.start][horizontal.end]
        }
    }
}
