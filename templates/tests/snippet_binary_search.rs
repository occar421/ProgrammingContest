#[cfg(test)]
mod tests {
    use templates::snippet_binary_search::binary_search::BinaryBorderSearch;
    use test_case::test_case;

    #[test]
    fn tfb_empty_slice() {
        let result = Vec::<usize>::new().search_true_false_border(|_| true);
        assert_eq!(result.max_true, None);
        assert_eq!(result.min_false, None);
    }

    #[test]
    fn tfb_single_true_slice() {
        let result = vec![1].search_true_false_border(|_| true);
        assert_eq!(result.max_true, Some(0));
        assert_eq!(result.min_false, None);
    }

    #[test]
    fn tfb_single_false_slice() {
        let result = vec![1].search_true_false_border(|_| false);
        assert_eq!(result.max_true, None);
        assert_eq!(result.min_false, Some(0));
    }

    #[test_case(vec![false, false] => (None, Some(0)))]
    #[test_case(vec![true, false] => (Some(0), Some(1)))]
    #[test_case(vec![true, true] => (Some(1), None))]
    fn tfb_two_values_slice(value: Vec<bool>) -> (Option<usize>, Option<usize>) {
        let result = value.search_true_false_border(|&x| x);
        (result.max_true, result.min_false)
    }

    #[test_case(vec![false, false, false] => (None, Some(0)))]
    #[test_case(vec![true, false, false] => (Some(0), Some(1)))]
    #[test_case(vec![true, true, false] => (Some(1), Some(2)))]
    #[test_case(vec![true, true, true] => (Some(2), None))]
    fn tfb_three_values_slice(value: Vec<bool>) -> (Option<usize>, Option<usize>) {
        let result = value.search_true_false_border(|&x| x);
        (result.max_true, result.min_false)
    }

    #[test]
    fn ftb_empty_slice_slice() {
        let result = Vec::<usize>::new().search_false_true_border(|_| true);
        assert_eq!(result.max_false, None);
        assert_eq!(result.min_true, None);
    }

    #[test]
    fn ftb_single_true_slice() {
        let result = vec![1].search_false_true_border(|_| true);
        assert_eq!(result.max_false, None);
        assert_eq!(result.min_true, Some(0));
    }

    #[test]
    fn ftb_single_false_slice() {
        let result = vec![1].search_false_true_border(|_| false);
        assert_eq!(result.max_false, Some(0));
        assert_eq!(result.min_true, None);
    }

    #[test_case(vec![false, false] => (Some(1), None))]
    #[test_case(vec![false, true] => (Some(0), Some(1)))]
    #[test_case(vec![true, true] => (None, Some(0)))]
    fn ftb_two_values_slice(value: Vec<bool>) -> (Option<usize>, Option<usize>) {
        let result = value.search_false_true_border(|&x| x);
        (result.max_false, result.min_true)
    }

    #[test_case(vec![false, false, false] => (Some(2), None))]
    #[test_case(vec![false, false, true] => (Some(1), Some(2)))]
    #[test_case(vec![false, true, true] => (Some(0), Some(1)))]
    #[test_case(vec![true, true, true] => (None, Some(0)))]
    fn ftb_three_values_slice(value: Vec<bool>) -> (Option<usize>, Option<usize>) {
        let result = value.search_false_true_border(|&x| x);
        (result.max_false, result.min_true)
    }
}
