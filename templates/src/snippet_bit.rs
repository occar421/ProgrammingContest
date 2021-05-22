use crate::standard_io::{NodeIndex0Based, Quantity};

pub mod bit {
    use super::{NodeIndex0Based, Quantity};
    use std::marker::PhantomData;
    use std::ops::{
        BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Index, Not, Shl, ShlAssign,
        Shr, ShrAssign,
    };

    pub trait BitSizeExt: Clone + Copy {
        fn size() -> usize;
    }

    #[macro_export]
    macro_rules! bit_set {
        ($num: literal as $alias: ident) => {
            bit_size!($num in bit as $alias);
        };
        ($num: literal in $module_base: path as $alias: ident) => {
            #[derive(Debug, Clone, Copy, Default, PartialOrd, Ord, PartialEq, Eq)]
            pub struct BitSize;

            use $module_base as base;

            impl base::BitSizeExt for BitSize {
                #[inline]
                fn size() -> usize {
                    $num
                }
            }

            type $alias = base::BitSet<BitSize>;
        };
    }

    #[derive(Clone)]
    pub struct BitSet<S>
    where
        S: BitSizeExt,
    {
        // little endian
        chunks: Vec<u64>,
        size: PhantomData<S>,
    }

    const CHUNK_BIT_SIZE: usize = 64;
    const CHUNK_INDEX_MASK: usize = 63;
    // 2 ^ 6 = 64
    const CHUNK_BIT_LENGTH: usize = 6;

    impl<S> BitSet<S>
    where
        S: BitSizeExt,
    {
        pub fn zero() -> Self {
            Self {
                chunks: vec![0; (S::size() + (CHUNK_BIT_SIZE - 1)) / CHUNK_BIT_SIZE],
                size: PhantomData,
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
            assert!(index < S::size());

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

        fn chomp(&mut self) {
            let r = S::size() & CHUNK_INDEX_MASK;
            if let Some(bits) = self.chunks.last_mut() {
                let d = CHUNK_BIT_SIZE - r;
                // erase "overflowed" bits
                *bits = (*bits << d) >> d;
            }
        }
    }

    impl<S> Not for BitSet<S>
    where
        S: BitSizeExt,
    {
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

    impl<S> BitAnd<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn bitand(self, rhs: BitSet<S>) -> Self::Output {
            let mut v = self.clone();
            v &= rhs;
            v
        }
    }

    impl<S> BitAndAssign<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        fn bitand_assign(&mut self, rhs: BitSet<S>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece &= rhs_piece;
            }
        }
    }

    impl<S> BitOr<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn bitor(self, rhs: BitSet<S>) -> Self::Output {
            let mut v = self.clone();
            v |= rhs;
            v
        }
    }

    impl<S> BitOrAssign<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        fn bitor_assign(&mut self, rhs: BitSet<S>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece |= rhs_piece;
            }
            self.chomp();
        }
    }

    impl<S> BitXor<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn bitxor(self, rhs: BitSet<S>) -> Self::Output {
            let mut v = self.clone();
            v ^= rhs;
            v
        }
    }

    impl<S> BitXorAssign<BitSet<S>> for BitSet<S>
    where
        S: BitSizeExt,
    {
        fn bitxor_assign(&mut self, rhs: BitSet<S>) {
            for (self_piece, rhs_piece) in self.chunks.iter_mut().zip(rhs.chunks.iter()) {
                *self_piece ^= rhs_piece;
            }
        }
    }

    impl<S> Shl<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn shl(self, rhs: usize) -> Self::Output {
            let mut v = self.clone();
            v <<= rhs;
            v
        }
    }

    impl<S> ShlAssign<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
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

    impl<S> Shr<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
        type Output = Self;

        fn shr(self, rhs: usize) -> Self::Output {
            let mut v = self.clone();
            v >>= rhs;
            v
        }
    }

    impl<S> ShrAssign<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
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

    impl<S> Index<usize> for BitSet<S>
    where
        S: BitSizeExt,
    {
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
        pub fn includes(&self, index: NodeIndex0Based) -> bool {
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
        pub fn excluded_set(&self, index: NodeIndex0Based) -> Self {
            Self::new(self.size, self.value & !(0b1 << index))
        }

        #[inline]
        pub fn appended_set(&self, index: NodeIndex0Based) -> Self {
            Self::new(self.size, self.value | (0b1 << index))
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
        pub fn combination(&self) -> Quantity {
            0b1 << self.size as u32
        }

        pub fn from_indices_iter<I>(&self, iter: I) -> BitBasedSet
        where
            I: Iterator<Item = NodeIndex0Based>,
        {
            let mut v = 0;
            for i in iter {
                v |= 0b1 << i;
            }
            BitBasedSet::new(self.size, v)
        }
    }
}
