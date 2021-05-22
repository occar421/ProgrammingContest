#[cfg(test)]
mod tests {
    use templates::bit_size;
    use templates::snippet_bit::bit::{BitSet, BitSizeExt};
    use test_case::test_case;

    macro_rules! bit_size_test {
        ($num: literal as $alias: ident) => {
            bit_size!($num in templates::snippet_bit::bit as $alias);
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
        bit_size_test!(2 as BitSet2);

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
        bit_size_test!(2 as BitSet2);

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
        bit_size_test!(2 as BitSet2);

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
        bit_size_test!(2 as BitSet2);

        let bits = BitSet2::new(n);
        bits.count_ones()
    }

    #[test_case(0b000 => 0b011)]
    #[test_case(0b001 => 0b010)]
    #[test_case(0b010 => 0b001)]
    #[test_case(0b011 => 0b000)]
    #[test_case(0b100 => 0b011)]
    fn bit2_not(n: u8) -> u128 {
        bit_size_test!(2 as BitSet2);

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
        bit_size_test!(2 as BitSet2);

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
        bit_size_test!(2 as BitSet2);

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
        bit_size_test!(2 as BitSet2);

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
        bit_size_test!(2 as BitSet2);

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
        bit_size_test!(2 as BitSet2);

        let bits = BitSet2::new(target);
        bit_set_to_usize(bits >> amount, 5)
    }
}
