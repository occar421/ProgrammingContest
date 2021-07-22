#[cfg(test)]
mod tests {
    use templates::snippet_binary_indexed_tree::binary_indexed_tree::BinaryIndexedTree1d;

    #[test]
    fn check_1d_static() {
        // same with cum_sum

        let data = vec![1, 2, 3];
        let bit = BinaryIndexedTree1d::new_with_slice(&data);

        assert_eq!(bit.sum_in(0..0), 0);
        assert_eq!(bit.sum_in(0..1), 1);
        assert_eq!(bit.sum_in(0..2), 3);
        assert_eq!(bit.sum_in(1..2), 2);

        assert_eq!(bit.sum_in(0..3), 6);
        assert_eq!(bit.sum_in(..), 6);
    }

    #[test]
    fn check_1d_dynamic() {
        let data = vec![1, 2, 3];
        let mut bit = BinaryIndexedTree1d::new_with_slice(&data);

        bit.add_value_at(1, 5);

        assert_eq!(bit.sum_in(0..0), 0);
        assert_eq!(bit.sum_in(0..1), 1);
        assert_eq!(bit.sum_in(0..2), 8);
        assert_eq!(bit.sum_in(1..2), 7);

        assert_eq!(bit.sum_in(0..3), 11);
        assert_eq!(bit.sum_in(..), 11);

        bit.add_value_at(2, 12);

        assert_eq!(bit.sum_in(0..0), 0);
        assert_eq!(bit.sum_in(0..1), 1);
        assert_eq!(bit.sum_in(0..2), 8);
        assert_eq!(bit.sum_in(1..2), 7);

        assert_eq!(bit.sum_in(0..3), 23);
        assert_eq!(bit.sum_in(..), 23);
    }
}
