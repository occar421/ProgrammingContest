#[cfg(test)]
mod tests {
    use templates::snippet_cumulative_sum::cumulative_sum::CumulativeSum2d;

    #[test]
    fn check_2d_one_line() {
        // 1 2 3
        let data = vec![vec![1, 2, 3]];
        let cum_sum = CumulativeSum2d::new(data.len(), data[0].len(), &data);

        assert_eq!(cum_sum.value_in(0..1, 0..1), 1);
        assert_eq!(cum_sum.value_in(0..1, 0..2), 3);
        assert_eq!(cum_sum.value_in(0..1, 0..3), 6);
        assert_eq!(cum_sum.value_in(0..1, 1..3), 5);
    }

    #[test]
    fn check_2d_square() {
        // 1 2
        // 4 8
        let data = vec![vec![1, 2], vec![4, 8]];
        let cum_sum = CumulativeSum2d::new(data.len(), data[0].len(), &data);

        assert_eq!(cum_sum.value_in(0..0, 0..0), 0);
        assert_eq!(cum_sum.value_in(0..0, 0..1), 0);
        assert_eq!(cum_sum.value_in(0..1, 0..0), 0);

        assert_eq!(cum_sum.value_in(0..1, 0..1), 1);
        assert_eq!(cum_sum.value_in(0..1, 0..2), 3);
        assert_eq!(cum_sum.value_in(0..2, 0..1), 5);
        assert_eq!(cum_sum.value_in(1..2, 1..2), 8);

        assert_eq!(cum_sum.value_in(0..2, 0..2), 15);
        assert_eq!(cum_sum.value_in(.., ..), 15);
        assert_eq!(cum_sum.value_in(0.., 0..), 15);
        assert_eq!(cum_sum.value_in(..2, ..2), 15);
        assert_eq!(cum_sum.value_in(..=1, ..=1), 15);
        assert_eq!(cum_sum.value_in(0..=0, 0..=0), 1);
        assert_eq!(cum_sum.value_in(1..=1, 1..=1), 8);
    }

    #[test]
    fn check_2d_with_evaluator() {
        // 1 2
        // 4 8
        let data: Vec<Vec<usize>> = vec![vec![1, 2], vec![4, 8]];
        let cum_sum = CumulativeSum2d::new_with_evaluator(data.len(), data[0].len(), |i, j| {
            data[i][j].pow(2)
        });

        assert_eq!(cum_sum.value_in(.., ..), 85);
    }
}
