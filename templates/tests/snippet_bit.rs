#[cfg(test)]
mod tests {
    mod bit_set {
        use templates::snippet_bit::bit::BitSet;
        use test_case::test_case;

        fn bit_set_to_usize<const SIZE: usize>(bits: BitSet<SIZE>, max_bit: u32) -> u128 {
            (0..=max_bit)
                .map(|b| if bits[b as usize] { 2u128.pow(b) } else { 0 })
                .sum()
        }

        type BitSet2 = BitSet<2>;

        #[test_case(0b000 => (false, false, false))]
        #[test_case(0b001 => (false, false, true))]
        #[test_case(0b010 => (false, true, false))]
        #[test_case(0b011 => (false, true, true))]
        #[test_case(0b100 => (false, false, false))]
        fn new_bit2(n: u8) -> (bool, bool, bool) {
            let bits = BitSet2::new(n);
            (bits[2], bits[1], bits[0])
        }

        #[test_case(0b000, 0 => 0b001)]
        #[test_case(0b001, 0 => 0b001)]
        #[test_case(0b001, 1 => 0b011)]
        #[test_case(0b010, 0 => 0b011)]
        #[test_case(0b010, 1 => 0b010)]
        #[test_case(0b010, 2 => panics)]
        #[test_case(0b011, 0 => 0b011)]
        #[test_case(0b011, 1 => 0b011)]
        #[test_case(0b100, 0 => 0b001)]
        #[test_case(0b100, 1 => 0b010)]
        fn bit2_set_true(target: u8, bit_index: usize) -> u128 {
            let mut bits = BitSet2::new(target);
            bits.set(bit_index, true);
            bit_set_to_usize(bits, 5)
        }

        #[test_case(0b000, 0 => 0b000)]
        #[test_case(0b001, 0 => 0b000)]
        #[test_case(0b001, 1 => 0b001)]
        #[test_case(0b010, 0 => 0b010)]
        #[test_case(0b010, 1 => 0b000)]
        #[test_case(0b010, 2 => panics)]
        #[test_case(0b011, 0 => 0b010)]
        #[test_case(0b011, 1 => 0b001)]
        #[test_case(0b100, 0 => 0b000)]
        fn bit2_set_false(target: u8, bit_index: usize) -> u128 {
            let mut bits = BitSet2::new(target);
            bits.set(bit_index, false);
            bit_set_to_usize(bits, 5)
        }

        #[test_case(0b000 => 0)]
        #[test_case(0b001 => 1)]
        #[test_case(0b010 => 1)]
        #[test_case(0b011 => 2)]
        #[test_case(0b100 => 0)]
        fn bit2_count_ones(n: u8) -> u32 {
            let bits = BitSet2::new(n);
            bits.count_ones()
        }

        #[test_case(0b000 => 0b011)]
        #[test_case(0b001 => 0b010)]
        #[test_case(0b010 => 0b001)]
        #[test_case(0b011 => 0b000)]
        #[test_case(0b100 => 0b011)]
        fn bit2_not(n: u8) -> u128 {
            let bits = BitSet2::new(n);
            bit_set_to_usize(!bits, 5)
        }

        #[test_case(0b000, 0b000 => 0b000)]
        #[test_case(0b001, 0b001 => 0b001)]
        #[test_case(0b001, 0b010 => 0b000)]
        #[test_case(0b010, 0b001 => 0b000)]
        #[test_case(0b010, 0b010 => 0b010)]
        #[test_case(0b011, 0b000 => 0b000)]
        #[test_case(0b011, 0b011 => 0b011)]
        #[test_case(0b100, 0b011 => 0b000)]
        fn bit2_and(l: u8, r: u8) -> u128 {
            let l = BitSet2::new(l);
            let r = BitSet2::new(r);
            bit_set_to_usize(l & r, 5)
        }

        #[test_case(0b000, 0b000 => 0b000)]
        #[test_case(0b001, 0b001 => 0b001)]
        #[test_case(0b001, 0b010 => 0b011)]
        #[test_case(0b010, 0b001 => 0b011)]
        #[test_case(0b010, 0b010 => 0b010)]
        #[test_case(0b011, 0b000 => 0b011)]
        #[test_case(0b011, 0b011 => 0b011)]
        #[test_case(0b100, 0b011 => 0b011)]
        fn bit2_or(l: u8, r: u8) -> u128 {
            let l = BitSet2::new(l);
            let r = BitSet2::new(r);
            bit_set_to_usize(l | r, 5)
        }

        #[test_case(0b000, 0b000 => 0b000)]
        #[test_case(0b001, 0b001 => 0b000)]
        #[test_case(0b001, 0b010 => 0b011)]
        #[test_case(0b010, 0b001 => 0b011)]
        #[test_case(0b010, 0b010 => 0b000)]
        #[test_case(0b011, 0b000 => 0b011)]
        #[test_case(0b011, 0b011 => 0b000)]
        #[test_case(0b100, 0b011 => 0b011)]
        fn bit2_xor(l: u8, r: u8) -> u128 {
            let l = BitSet2::new(l);
            let r = BitSet2::new(r);
            bit_set_to_usize(l ^ r, 5)
        }

        #[test_case(0b000, 0 => 0b000)]
        #[test_case(0b001, 0 => 0b001)]
        #[test_case(0b001, 1 => 0b010)]
        #[test_case(0b010, 0 => 0b010)]
        #[test_case(0b010, 1 => 0b000)]
        #[test_case(0b010, 2 => 0b000)]
        #[test_case(0b011, 0 => 0b011)]
        #[test_case(0b011, 1 => 0b010)]
        #[test_case(0b100, 0 => 0b000)]
        fn bit2_shl(target: u8, amount: usize) -> u128 {
            let bits = BitSet2::new(target);
            bit_set_to_usize(bits << amount, 5)
        }

        #[test_case(0b000, 0 => 0b000)]
        #[test_case(0b001, 0 => 0b001)]
        #[test_case(0b001, 1 => 0b000)]
        #[test_case(0b010, 0 => 0b010)]
        #[test_case(0b010, 1 => 0b001)]
        #[test_case(0b010, 2 => 0b000)]
        #[test_case(0b011, 0 => 0b011)]
        #[test_case(0b011, 1 => 0b001)]
        #[test_case(0b100, 0 => 0b000)]
        fn bit2_shr(target: u8, amount: usize) -> u128 {
            let bits = BitSet2::new(target);
            bit_set_to_usize(bits >> amount, 5)
        }
    }

    mod bit_based_set {
        use templates::snippet_bit::bit::BitBasedSet;
        use test_case::test_case;

        type Bbs2 = BitBasedSet<2>;
        type Bbs4 = BitBasedSet<4>;
        type Bbs8 = BitBasedSet<8>;

        #[test]
        fn bbs2_static() {
            assert_eq!(Bbs2::universal_set().dump(), 0b011);
            assert_eq!(Bbs2::empty_set().dump(), 0b000);
            assert_eq!(Bbs2::combination(), 4);
        }

        #[test]
        fn bbs8_by_nodes_iter() {
            let bbs = Bbs8::by_indices_iter(vec![1, 2, 4].into_iter());
            assert_eq!(bbs.dump(), 0b0010110)
        }

        #[test_case(0 => false)]
        #[test_case(1 => true)]
        fn bbs2_includes(index: usize) -> bool {
            let bbs = Bbs2::empty_set().appended_set(1);
            bbs.includes(index)
        }

        #[test]
        fn bbs2_is_empty() {
            assert_eq!(Bbs2::empty_set().is_empty(), true);
            assert_eq!(Bbs2::empty_set().appended_set(1).is_empty(), false);
        }

        #[test_case(0 => true)]
        #[test_case(1 => false)]
        fn bbs2_complement(index: usize) -> bool {
            let bbs = Bbs2::empty_set().appended_set(1).complement();
            bbs.includes(index)
        }

        #[test]
        fn bbs2_excluded_set() {
            let bbs = Bbs2::empty_set().excluded_set(1);
            assert_eq!(bbs.includes(0), false);
            assert_eq!(bbs.includes(1), false);

            let bbs = Bbs2::universal_set().excluded_set(1);
            assert_eq!(bbs.includes(0), true);
            assert_eq!(bbs.includes(1), false);
        }

        #[test]
        fn bbs2_appended_set() {
            let bbs = Bbs2::empty_set().appended_set(1);
            assert_eq!(bbs.includes(0), false);
            assert_eq!(bbs.includes(1), true);

            let bbs = Bbs2::universal_set().appended_set(1);
            assert_eq!(bbs.includes(0), true);
            assert_eq!(bbs.includes(1), true);
        }

        #[test]
        fn bbs4_into_iter() {
            let bbs = Bbs4::empty_set().appended_set(2).appended_set(1);
            let mut bbs_iter = bbs.into_iter();
            assert_eq!(bbs_iter.next(), Some(1));
            assert_eq!(bbs_iter.next(), Some(2));
            assert_eq!(bbs_iter.next(), None);
        }

        #[test]
        fn bbs4_from() {
            let bbs = Bbs4::from(0b1001);
            assert!(bbs.includes(0));
            assert!(!bbs.includes(1));
            assert!(!bbs.includes(2));
            assert!(bbs.includes(3));
        }
    }
}
