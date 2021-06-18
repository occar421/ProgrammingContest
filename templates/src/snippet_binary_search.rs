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

    pub trait BinaryBorderSearch<Item, GI: GenericInteger> {
        /// O( log(N) )
        /// Should be sorted
        fn search_true_false_border(&self, predicate: impl Fn(&Item) -> bool)
            -> TFBorderResult<GI>;

        /// O( log(N) )
        /// Should be sorted
        #[inline]
        fn search_false_true_border(
            &self,
            predicate: impl Fn(&Item) -> bool,
        ) -> FTBorderResult<GI> {
            let result = self.search_true_false_border(|item| !predicate(item));
            FTBorderResult {
                max_false: result.max_true,
                min_true: result.min_false,
            }
        }
    }

    impl<Item> BinaryBorderSearch<Item, usize> for [Item] {
        /// O( log(N) )
        /// ```
        /// # use templates::snippet_binary_search::binary_search::BinaryBorderSearch;
        /// let vec = vec![1, 2, 3];
        /// let result = vec.search_true_false_border(|&x| x > 1);
        /// assert_eq!(result.max_true, 0);
        /// assert_eq!(result.min_false, 1);
        /// ```
        #[inline]
        fn search_true_false_border(
            &self,
            predicate: impl Fn(&Item) -> bool,
        ) -> TFBorderResult<usize> {
            (0..self.len()).search_true_false_border(|&i| predicate(&self[i]))
        }
    }

    impl<GI: GenericInteger> BinaryBorderSearch<GI, GI> for Range<GI> {
        /// O( log(high-low) )
        /// ```
        /// # use templates::snippet_binary_search::binary_search::BinaryBorderSearch;
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
        /// O( log(high-low) )
        /// ```
        /// # use templates::snippet_binary_search::binary_search::BinaryBorderSearch;
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
