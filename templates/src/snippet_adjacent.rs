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
}
