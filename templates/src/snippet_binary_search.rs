use crate::standard_io::GenericInteger;

pub mod binary_search {
    use super::GenericInteger;
    use std::ops::{Range, RangeInclusive};

    pub struct TFBorderResult<GI: GenericInteger> {
        pub max_true: Option<GI>,
        pub min_false: Option<GI>,
    }

    pub struct FTBorderResult<GI: GenericInteger> {
        pub max_false: Option<GI>,
        pub min_true: Option<GI>,
    }

    pub trait BinaryBorderSearch<T, GI: GenericInteger> {
        /// O( log(N) )
        /// Should be sorted
        fn search_true_false_border(&self, predicate: impl Fn(&T) -> bool) -> TFBorderResult<GI>;

        /// O( log(N) )
        /// Should be sorted
        #[inline]
        fn search_false_true_border(&self, predicate: impl Fn(&T) -> bool) -> FTBorderResult<GI> {
            let result = self.search_true_false_border(|item| !predicate(item));
            FTBorderResult {
                max_false: result.max_true,
                min_true: result.min_false,
            }
        }
    }

    impl<T: Ord> BinaryBorderSearch<T, usize> for [T] {
        /// ```
        /// let vec = vec![1, 2, 3];
        /// let result = vec.search_true_false_border(|&x| x > 1);
        /// assert_eq!(result.max_true, 0);
        /// assert_eq!(result.min_false, 1);
        /// ```
        fn search_true_false_border(
            &self,
            predicate: impl Fn(&T) -> bool,
        ) -> TFBorderResult<usize> {
            if self.is_empty() {
                return TFBorderResult {
                    max_true: None,
                    min_false: None,
                };
            }

            let first = &self[0];
            if !predicate(first) {
                return TFBorderResult {
                    max_true: None,
                    min_false: 0.into(),
                };
            }

            let mut known_max_true = 0;
            let mut known_min_false = self.len();
            while known_min_false - known_max_true > 1 {
                let mid = known_max_true + (known_min_false - known_max_true) / 2;
                if predicate(&self[mid]) {
                    known_max_true = mid;
                } else {
                    known_min_false = mid;
                }
            }

            // all true
            if known_min_false == self.len() {
                TFBorderResult {
                    max_true: (self.len() - 1).into(),
                    min_false: None,
                }
            } else {
                TFBorderResult {
                    max_true: known_max_true.into(),
                    min_false: known_min_false.into(),
                }
            }
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for Range<GI> {
        /// ```
        /// let range = 1..4;
        /// let result = range.search_true_false_border(|&x| x <= 1);
        /// assert_eq!(result.max_true, 1);
        /// assert_eq!(result.min_false, 2);
        /// ```
        fn search_true_false_border(&self, predicate: impl Fn(&GI) -> bool) -> TFBorderResult<GI> {
            if self.start >= self.end {
                return TFBorderResult {
                    max_true: None,
                    min_false: None,
                };
            }

            let first = self.start;
            if !predicate(&first) {
                return TFBorderResult {
                    max_true: None,
                    min_false: first.into(),
                };
            }

            let mut known_max_true = first;
            let mut known_min_false = self.end;
            while known_min_false - known_max_true > GI::one() {
                let mid =
                    known_max_true + (known_min_false - known_max_true) / (GI::one() + GI::one());
                if predicate(&mid) {
                    known_max_true = mid;
                } else {
                    known_min_false = mid;
                }
            }

            // all true
            if known_min_false == self.end {
                TFBorderResult {
                    max_true: (self.end - GI::one()).into(),
                    min_false: None,
                }
            } else {
                TFBorderResult {
                    max_true: known_max_true.into(),
                    min_false: known_min_false.into(),
                }
            }
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for Range<&GI> {
        #[inline]
        fn search_true_false_border(&self, predicate: impl Fn(&GI) -> bool) -> TFBorderResult<GI> {
            (*self.start..*self.end).search_true_false_border(predicate)
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for RangeInclusive<GI> {
        /// ```
        /// let range = -1..=1;
        /// let result = range.search_true_false_border(|&x| x <= 1);
        /// assert_eq!(result.max_true, 1);
        /// assert_eq!(result.min_false, None);
        /// ```
        #[inline]
        fn search_true_false_border(&self, predicate: impl Fn(&GI) -> bool) -> TFBorderResult<GI> {
            (*self.start()..(*self.end() + GI::one())).search_true_false_border(predicate)
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for RangeInclusive<&GI> {
        #[inline]
        fn search_true_false_border(&self, predicate: impl Fn(&GI) -> bool) -> TFBorderResult<GI> {
            (**self.start()..(**self.end() + GI::one())).search_true_false_border(predicate)
        }
    }
}
