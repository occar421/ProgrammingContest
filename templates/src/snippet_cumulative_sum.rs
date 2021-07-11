use crate::standard_io::GenericInteger;

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

    mod range {
        use std::ops::{Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeTo};

        /// The range that inclusive bounds are prohibited.
        pub trait CumulativeSumRange: RangeBounds<usize> {
            fn to_range(&self, unbounded_end: usize) -> Range<usize> {
                let start = match self.start_bound() {
                    Bound::Unbounded => 0,
                    Bound::Included(&n) => n,
                    Bound::Excluded(&n) => n + 1,
                };
                let end = match self.end_bound() {
                    Bound::Unbounded => unbounded_end,
                    Bound::Included(&n) => n + 1,
                    Bound::Excluded(&n) => n,
                };

                start..end
            }
        }
        impl CumulativeSumRange for RangeFull {}
        impl CumulativeSumRange for RangeFrom<usize> {}
        impl CumulativeSumRange for RangeTo<usize> {}
        impl CumulativeSumRange for Range<usize> {}
        impl CumulativeSumRange for (Bound<usize>, Bound<usize>) {}
        impl CumulativeSumRange for RangeFrom<&usize> {}
        impl CumulativeSumRange for RangeTo<&usize> {}
        impl CumulativeSumRange for Range<&usize> {}
        impl<'a> CumulativeSumRange for (Bound<&'a usize>, Bound<&'a usize>) {}
    }

    use super::GenericInteger;

    pub struct CumulativeSum1d<GI>
    where
        GI: GenericInteger,
    {
        cum_sum: Vec<GI>,
        source_length: usize,
    }

    impl<GI> CumulativeSum1d<GI>
    where
        GI: GenericInteger,
    {
        /// O( N )
        #[inline]
        pub fn new(source_length: usize, source: &Vec<GI>) -> Self {
            Self::new_with_evaluator(source_length, |i| source[i])
        }

        /// O( N )
        pub fn new_with_evaluator<F>(source_length: usize, evaluator: F) -> Self
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
        pub fn sum_in(&self, range: impl range::CumulativeSumRange) -> GI {
            let range = range.to_range(self.source_length);

            self.cum_sum[range.end] - self.cum_sum[range.start]
        }

        pub fn dump(&self) -> &[GI] {
            &self.cum_sum
        }
    }

    pub struct CumulativeSum2d<GI>
    where
        GI: GenericInteger,
    {
        cum_sum: Vec<Vec<GI>>,
        source_height: usize,
        source_width: usize,
    }

    impl<GI> CumulativeSum2d<GI>
    where
        GI: GenericInteger,
    {
        #[inline]
        /// O(N^2)
        pub fn new(source_height: usize, source_width: usize, source: &Vec<Vec<GI>>) -> Self {
            Self::new_with_evaluator(source_height, source_width, |i, j| source[i][j])
        }

        /// O(N^2)
        pub fn new_with_evaluator<F>(
            source_height: usize,
            source_width: usize,
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
            vertical_range: impl range::CumulativeSumRange,
            horizontal_range: impl range::CumulativeSumRange,
        ) -> GI {
            let vertical_range = vertical_range.to_range(self.source_height);
            let horizontal_range = horizontal_range.to_range(self.source_width);

            self.cum_sum[vertical_range.end][horizontal_range.end]
                + self.cum_sum[vertical_range.start][horizontal_range.start]
                - self.cum_sum[vertical_range.end][horizontal_range.start]
                - self.cum_sum[vertical_range.start][horizontal_range.end]
        }
    }
}
