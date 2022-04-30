pub mod bit {
    //! Bit
    //! https://github.com/occar421/ProgrammingContest/tree/master/templates/src/snippet_bit.rs

    use std::ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Index, Not, Shl, ShlAssign,
        Shr, ShrAssign,
    };

    /// ```
    /// # use templates::snippet_bit::bit::BitSet;
    /// type BitSet2 = BitSet<2>;
    /// ```
    #[derive(Clone)]
    pub struct BitSet<const SIZE: usize> {
        // little endian
        chunks: Vec<u64>,
    }

    const CHUNK_BIT_SIZE: usize = 64;
    const CHUNK_INDEX_MASK: usize = 63;
    // 2 ^ 6 = 64
    const CHUNK_BIT_LENGTH: usize = 6;

    impl<const SIZE: usize> BitSet<SIZE> {
        pub fn zero() -> Self {
            Self {
                chunks: vec![0; (SIZE + (CHUNK_BIT_SIZE - 1)) / CHUNK_BIT_SIZE],
            }
        }

        pub fn new(value: impl Into<u64>) -> Self {
            let value = value.into();

            let mut v = Self::zero().clone();

            v.chunks[0] = value;

            v.chomp();
            v
        }

        pub fn set(&mut self, index: usize, value: bool) {
            assert!(index < SIZE);

            let target_bit = 1 << (index & CHUNK_INDEX_MASK);

            if value {
                self.chunks[index >> CHUNK_BIT_LENGTH] |= target_bit;
            } else {
                self.chunks[index >> CHUNK_BIT_LENGTH] &= !target_bit;
            }
        }

        pub fn count_ones(&self) -> u32 {
            self.chunks.iter().map(|x| x.count_ones()).sum()
        }

        const R: usize = SIZE & CHUNK_INDEX_MASK;

        fn chomp(&mut self) {
            if let Some(bits) = self.chunks.last_mut() {
                let d = CHUNK_BIT_SIZE - Self::R;
                // erase "overflowed" bits
                *bits = (*bits << d) >> d;
            }
        }
    }

    impl<const SIZE: usize> Not for BitSet<SIZE> {
        type Output = Self;

        fn not(self) -> Self::Output {
            let mut v = self.clone();
            for piece in v.chunks.iter_mut() {
                *piece = !*piece;
            }
            v.chomp();
            v
        }
    }

    impl<const SIZE: usize> BitAnd<BitSet<SIZE>> for BitSet<SIZE> {
        type Output = Self;

        fn bitand(self, rhs: BitSet<SIZE>) -> Self::Output {
            let mut v = self.clone();
            v &= rhs;
            v
        }
    }

    impl<const SIZE: usize> BitAndAssign<BitSet<SIZE>> for BitSet<SIZE> {
        fn bitand_assign(&mut self, rhs: BitSet<SIZE>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece &= rhs_piece;
            }
        }
    }

    impl<const SIZE: usize> BitOr<BitSet<SIZE>> for BitSet<SIZE> {
        type Output = Self;

        fn bitor(self, rhs: BitSet<SIZE>) -> Self::Output {
            let mut v = self.clone();
            v |= rhs;
            v
        }
    }

    impl<const SIZE: usize> BitOrAssign<BitSet<SIZE>> for BitSet<SIZE> {
        fn bitor_assign(&mut self, rhs: BitSet<SIZE>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece |= rhs_piece;
            }
            self.chomp();
        }
    }

    impl<const SIZE: usize> BitXor<BitSet<SIZE>> for BitSet<SIZE> {
        type Output = Self;

        fn bitxor(self, rhs: BitSet<SIZE>) -> Self::Output {
            let mut v = self.clone();
            v ^= rhs;
            v
        }
    }

    impl<const SIZE: usize> BitXorAssign<BitSet<SIZE>> for BitSet<SIZE> {
        fn bitxor_assign(&mut self, rhs: BitSet<SIZE>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece ^= rhs_piece;
            }
        }
    }

    impl<const SIZE: usize> Shl<usize> for BitSet<SIZE> {
        type Output = Self;

        fn shl(self, rhs: usize) -> Self::Output {
            let mut v = self.clone();
            v <<= rhs;
            v
        }
    }

    impl<const SIZE: usize> ShlAssign<usize> for BitSet<SIZE> {
        fn shl_assign(&mut self, rhs: usize) {
            let chunk_shifts = rhs >> CHUNK_BIT_LENGTH;
            let shifts_in_chunk = rhs & CHUNK_INDEX_MASK;

            let chunks_length = self.chunks.len();

            if chunk_shifts >= chunks_length {
                // "overflow"
                for x in &mut self.chunks {
                    *x = 0;
                }
                return;
            }

            if shifts_in_chunk == 0 {
                for i in (chunk_shifts..chunks_length).rev() {
                    self.chunks[i] = self.chunks[i - chunk_shifts];
                }
            } else {
                for i in (chunk_shifts + 1..chunks_length).rev() {
                    self.chunks[i] = (self.chunks[i - chunk_shifts] << shifts_in_chunk)
                        | (self.chunks[i - chunk_shifts - 1] >> (CHUNK_BIT_SIZE - shifts_in_chunk));
                }
                self.chunks[chunk_shifts] = self.chunks[0] << shifts_in_chunk;
            }

            // jack up
            for x in &mut self.chunks[..chunk_shifts] {
                *x = 0;
            }

            self.chomp();
        }
    }

    impl<const SIZE: usize> Shr<usize> for BitSet<SIZE> {
        type Output = Self;

        fn shr(self, rhs: usize) -> Self::Output {
            let mut v = self.clone();
            v >>= rhs;
            v
        }
    }

    impl<const SIZE: usize> ShrAssign<usize> for BitSet<SIZE> {
        fn shr_assign(&mut self, rhs: usize) {
            let chunk_shifts = rhs >> CHUNK_BIT_LENGTH;
            let shifts_in_chunk = rhs & CHUNK_INDEX_MASK;

            let chunks_length = self.chunks.len();

            if chunk_shifts >= chunks_length {
                // 0b1's disappear
                for x in &mut self.chunks {
                    *x = 0;
                }
                return;
            }

            if shifts_in_chunk == 0 {
                for i in 0..(chunks_length - chunk_shifts) {
                    self.chunks[i] = self.chunks[i + chunk_shifts];
                }
            } else {
                for i in 0..(chunks_length - chunk_shifts - 1) {
                    self.chunks[i] = (self.chunks[i + chunk_shifts] >> shifts_in_chunk)
                        | (self.chunks[i + chunk_shifts + 1] << (CHUNK_BIT_SIZE - shifts_in_chunk));
                }
                self.chunks[chunks_length - chunk_shifts - 1] =
                    self.chunks[chunks_length - 1] >> shifts_in_chunk;
            }

            for x in &mut self.chunks[(chunks_length - chunk_shifts)..] {
                *x = 0;
            }
        }
    }

    const TRUE_REF: &bool = &true;
    const FALSE_REF: &bool = &false;

    impl<const SIZE: usize> Index<usize> for BitSet<SIZE> {
        type Output = bool;

        fn index(&self, index: usize) -> &Self::Output {
            [FALSE_REF, TRUE_REF][((self.chunks[index >> 6] >> (index & 63)) & 0b1) as usize]
        }
    }

    #[derive(Copy, Clone)]
    pub struct BitBasedSet {
        size: usize,
        value: usize,
    }

    impl BitBasedSet {
        fn new(size: usize, value: usize) -> Self {
            Self { size, value }
        }

        pub fn generator_of(size: usize) -> BitBasedSetGenerator {
            BitBasedSetGenerator::new(size)
        }

        #[inline]
        pub fn dump(&self) -> usize {
            self.value
        }

        #[inline]
        pub fn includes(&self, index: usize) -> bool {
            self.value & (0b1 << index) > 0
        }

        #[inline]
        pub fn is_empty(&self) -> bool {
            self.value.count_ones() == 0
        }

        #[inline]
        pub fn complement(&self) -> Self {
            Self::new(
                self.size,
                self.value ^ BitBasedSetGenerator::new(self.size).universal_set().value,
            )
        }

        #[inline]
        pub fn excluded_set(&self, index: usize) -> Self {
            Self::new(self.size, self.value & !(0b1 << index))
        }

        #[inline]
        pub fn appended_set(&self, index: usize) -> Self {
            Self::new(self.size, self.value | (0b1 << index))
        }
    }

    pub struct BitBasedSetIntoIter {
        set: BitBasedSet,
        current: usize,
    }

    impl Iterator for BitBasedSetIntoIter {
        type Item = usize;

        fn next(&mut self) -> Option<Self::Item> {
            let mut current = self.current;
            while self.set.size >= current {
                if self.set.includes(current) {
                    self.current = current + 1;
                    return Some(current);
                }
                current += 1;
            }
            return None;
        }
    }

    impl IntoIterator for BitBasedSet {
        type Item = usize;
        type IntoIter = BitBasedSetIntoIter;

        fn into_iter(self) -> Self::IntoIter {
            BitBasedSetIntoIter {
                set: self,
                current: 0,
            }
        }
    }

    pub struct BitBasedSetGenerator {
        size: usize,
    }

    impl BitBasedSetGenerator {
        fn new(size: usize) -> Self {
            Self { size }
        }

        #[inline]
        pub fn universal_set(&self) -> BitBasedSet {
            BitBasedSet::new(self.size, (0b1 << self.size) - 1)
        }

        #[inline]
        pub fn empty_set(&self) -> BitBasedSet {
            BitBasedSet::new(self.size, 0)
        }

        #[inline]
        pub fn combination(&self) -> usize {
            0b1 << self.size as u32
        }

        #[inline]
        pub fn from(&self, v: usize) -> BitBasedSet {
            BitBasedSet::new(self.size, v)
        }

        pub fn by_indices_iter<I>(&self, iter: I) -> BitBasedSet
        where
            I: Iterator<Item = usize>,
        {
            let mut v = 0;
            for i in iter {
                v |= 0b1 << i;
            }
            BitBasedSet::new(self.size, v)
        }
    }
}
