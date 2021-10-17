use crate::standard_io::GenericInteger;

pub mod binary_indexed_tree {
    //! BinaryIndexedTree
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_binary_indexed_tree.rs

    use super::GenericInteger;
    use std::ops::{Bound, Range, RangeBounds};

    pub struct BinaryIndexedTree1d<GI: GenericInteger>(Vec<GI>);

    impl<GI: GenericInteger> BinaryIndexedTree1d<GI> {
        pub fn new_with_zeros(size: usize) -> Self {
            Self(vec![GI::zero(); size])
        }

        /// O( N logN )
        pub fn new_with_slice(data: &[GI]) -> Self {
            let mut s = Self::new_with_zeros(data.len());

            for (i, data_i) in data.iter().enumerate() {
                s.add_value_at(i, *data_i);
            }

            s
        }

        /// O(logN)
        pub fn add_value_at(&mut self, index: usize, value: GI) {
            assert!(index < self.0.len());

            let mut current = index;
            while current < self.0.len() {
                self.0[current] += value;
                current |= current + 1 // move to parent
            }
        }

        /// O(logN)
        pub fn sum_in(&self, range: impl RangeBounds<usize>) -> GI {
            let range = Self::normalize_range(range, self.0.len());

            self.sum_until(range.end) - self.sum_until(range.start)
        }

        #[inline]
        fn normalize_range(range: impl RangeBounds<usize>, unbounded_end: usize) -> Range<usize> {
            let start = match range.start_bound() {
                Bound::Unbounded => 0,
                Bound::Included(&n) => n,
                Bound::Excluded(&n) => n + 1,
            };
            let end = match range.end_bound() {
                Bound::Unbounded => unbounded_end,
                Bound::Included(&n) => n + 1,
                Bound::Excluded(&n) => n,
            };

            start..end
        }

        fn sum_until(&self, to: usize) -> GI {
            if to == 0 {
                return GI::zero();
            }

            let mut result = GI::zero();
            let mut current = to;
            while {
                current -= 1;
                result += self.0[current];

                current &= current + 1; // to parent's elder sibling

                current > 0
            } {}

            result
        }
    }
}
