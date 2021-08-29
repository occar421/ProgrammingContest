use crate::standard_io::Point2d;

pub mod adjacent {
    //! Adjacent
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_adjacent.rs

    use super::Point2d;
    use std::ops::Range;

    pub struct Adjacent2d<I> {
        current: Point2d<isize>,
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
        I: Iterator<Item = &'a Point2d<isize>>,
    {
        pub fn new(
            current: Point2d<usize>,
            vertical_range: impl adjacent_range::AdjacentRange,
            horizontal_range: impl adjacent_range::AdjacentRange,
            iter: I,
        ) -> Self {
            Self {
                current: Point2d {
                    x: current.x as isize,
                    y: current.y as isize,
                },
                vertical_range: vertical_range.to_range(),
                horizontal_range: horizontal_range.to_range(),
                iter,
            }
        }
    }

    // From https://poyopoyoyon.hatenablog.com/entry/2020/11/08/183212
    impl<'a, I> Iterator for Adjacent2d<I>
    where
        I: Iterator<Item = &'a Point2d<isize>>,
    {
        type Item = Point2d<usize>;

        fn next(&mut self) -> Option<Self::Item> {
            while let Some(Point2d { x: dx, y: dy }) = self.iter.next() {
                let ny = self.current.y + dy;
                let nx = self.current.x + dx;
                if self.vertical_range.contains(&ny) && self.horizontal_range.contains(&nx) {
                    return Some(Point2d {
                        x: nx as usize,
                        y: ny as usize,
                    });
                }
            }
            None
        }
    }

    const A2D_4: &'static [Point2d<isize>] = &[
        Point2d { x: 0, y: -1 },
        Point2d { x: 1, y: 0 },
        Point2d { x: 0, y: 1 },
        Point2d { x: -1, y: 0 },
    ];

    pub fn adjacent2d_4neighbors(
        current: Point2d<usize>,
        vertical_range: impl adjacent_range::AdjacentRange,
        horizontal_range: impl adjacent_range::AdjacentRange,
    ) -> Adjacent2d<std::slice::Iter<'static, Point2d<isize>>> {
        Adjacent2d {
            current: Point2d {
                x: current.x as isize,
                y: current.y as isize,
            },
            vertical_range: vertical_range.to_range(),
            horizontal_range: horizontal_range.to_range(),
            iter: A2D_4.iter(),
        }
    }

    const A2D_8: &'static [Point2d<isize>] = &[
        Point2d { x: 0, y: -1 },
        Point2d { x: 1, y: -1 },
        Point2d { x: 1, y: 0 },
        Point2d { x: 1, y: 1 },
        Point2d { x: 0, y: 1 },
        Point2d { x: -1, y: 1 },
        Point2d { x: -1, y: 0 },
        Point2d { x: -1, y: -1 },
    ];

    pub fn adjacent2d_8neighbors(
        current: Point2d<usize>,
        vertical_range: impl adjacent_range::AdjacentRange,
        horizontal_range: impl adjacent_range::AdjacentRange,
    ) -> Adjacent2d<std::slice::Iter<'static, Point2d<isize>>> {
        Adjacent2d {
            current: Point2d {
                x: current.x as isize,
                y: current.y as isize,
            },
            vertical_range: vertical_range.to_range(),
            horizontal_range: horizontal_range.to_range(),
            iter: A2D_8.iter(),
        }
    }
}
