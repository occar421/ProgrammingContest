#[cfg(test)]
mod tests {
    use templates::bit_set;
    use templates::snippet_bit::bit::{BitBasedSet, BitSet, BitSizeExt};
    use test_case::test_case;

    macro_rules! bit_set_test {
        ($num: literal as $alias: ident) => {
            bit_set!($num in templates::snippet_bit::bit as $alias);
        };
    }

    fn bit_set_to_usize<S>(bits: BitSet<S>, max_bit: u32) -> u128
    where
        S: BitSizeExt,
    {
        (0..=max_bit)
            .map(|b| if bits[b as usize] { 2u128.pow(b) } else { 0 })
            .sum()
    }

    #[test_case(0b000 => (false, false, false))]
    #[test_case(0b001 => (false, false, true))]
    #[test_case(0b010 => (false, true, false))]
    #[test_case(0b011 => (false, true, true))]
    #[test_case(0b100 => (false, false, false))]
    fn new_bit2(n: u8) -> (bool, bool, bool) {
        bit_set_test!(2 as BitSet2);

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
        bit_set_test!(2 as BitSet2);

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
        bit_set_test!(2 as BitSet2);

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
        bit_set_test!(2 as BitSet2);

        let bits = BitSet2::new(n);
        bits.count_ones()
    }

    #[test_case(0b000 => 0b011)]
    #[test_case(0b001 => 0b010)]
    #[test_case(0b010 => 0b001)]
    #[test_case(0b011 => 0b000)]
    #[test_case(0b100 => 0b011)]
    fn bit2_not(n: u8) -> u128 {
        bit_set_test!(2 as BitSet2);

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
        bit_set_test!(2 as BitSet2);

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
        bit_set_test!(2 as BitSet2);

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
        bit_set_test!(2 as BitSet2);

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
        bit_set_test!(2 as BitSet2);

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
        bit_set_test!(2 as BitSet2);

        let bits = BitSet2::new(target);
        bit_set_to_usize(bits >> amount, 5)
    }

    #[test]
    fn bbs2gen_static() {
        let bbs2gen = BitBasedSet::generator_of(2);

        assert_eq!(bbs2gen.universal_set().dump(), 0b011);
        assert_eq!(bbs2gen.empty_set().dump(), 0b000);
        assert_eq!(bbs2gen.combination(), 4);
    }

    #[test]
    fn bbs8_from_nodes_iter() {
        let bbs8gen = BitBasedSet::generator_of(8);

        let bbs = bbs8gen.from_indices_iter(vec![1, 2, 4].into_iter());
        assert_eq!(bbs.dump(), 0b0010110)
    }

    #[test_case(0 => false)]
    #[test_case(1 => true)]
    fn bbs2_includes(index: usize) -> bool {
        let bbs2gen = BitBasedSet::generator_of(2);

        let bbs = bbs2gen.empty_set().appended_set(1);
        bbs.includes(index)
    }

    #[test]
    fn bbs2_is_empty() {
        let bbs2gen = BitBasedSet::generator_of(2);

        assert_eq!(bbs2gen.empty_set().is_empty(), true);
        assert_eq!(bbs2gen.empty_set().appended_set(1).is_empty(), false);
    }

    #[test_case(0 => true)]
    #[test_case(1 => false)]
    fn bbs2_complement(index: usize) -> bool {
        let bbs2gen = BitBasedSet::generator_of(2);

        let bbs = bbs2gen.empty_set().appended_set(1).complement();
        bbs.includes(index)
    }

    #[test]
    fn bbs2_excluded_set() {
        let bbs2gen = BitBasedSet::generator_of(2);

        let bbs = bbs2gen.empty_set().excluded_set(1);
        assert_eq!(bbs.includes(0), false);
        assert_eq!(bbs.includes(1), false);

        let bbs = bbs2gen.universal_set().excluded_set(1);
        assert_eq!(bbs.includes(0), true);
        assert_eq!(bbs.includes(1), false);
    }

    #[test]
    fn bbs2_appended_set() {
        let bbs2gen = BitBasedSet::generator_of(2);

        let bbs = bbs2gen.empty_set().appended_set(1);
        assert_eq!(bbs.includes(0), false);
        assert_eq!(bbs.includes(1), true);

        let bbs = bbs2gen.universal_set().appended_set(1);
        assert_eq!(bbs.includes(0), true);
        assert_eq!(bbs.includes(1), true);
    }
}
