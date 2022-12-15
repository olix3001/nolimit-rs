use bitvec::vec::BitVec;

use crate::InfUInt;
use bitvec::prelude::Lsb0;
use std::{
    cmp::Ordering,
    ops::{
        Add, AddAssign, Div, DivAssign, Mul, MulAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
};

#[derive(Clone)]
pub struct InfInt {
    sign: bool, // true for positive, false for negative
    value: InfUInt,
}

#[macro_export]
macro_rules! infint {
    (-$value:expr) => {
        InfInt {
            sign: false,
            value: crate::infuint!($value),
        }
    };
    ($value:expr) => {
        InfInt {
            sign: true,
            value: crate::infuint!($value),
        }
    };
}

impl InfInt {
    fn new(sign: bool, bits: BitVec<u8, Lsb0>) -> Self {
        Self {
            sign: true,
            value: InfUInt::new(bits),
        }
    }

    pub fn from_vec(sign: bool, bits: Vec<bool>) -> Self {
        Self {
            sign: sign,
            value: InfUInt::from_vec(bits),
        }
    }

    pub fn zero() -> Self {
        Self {
            sign: true,
            value: InfUInt::zero(),
        }
    }

    pub fn to_usize(&self) -> usize {
        self.value.to_usize()
    }

    pub fn to_isize(&self) -> isize {
        if self.sign {
            self.value.to_usize() as isize
        } else {
            -(self.value.to_usize() as isize)
        }
    }
}

// ====< Debug >====
impl std::fmt::Display for InfInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.sign {
            write!(f, "{}", self.value)
        } else {
            write!(f, "-{}", self.value)
        }
    }
}

impl std::fmt::Debug for InfInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.sign {
            write!(f, "{}", self.value)
        } else {
            write!(f, "-{}", self.value)
        }
    }
}

// ====< Macros >====
macro_rules! create_assign_operator {
    ($assign:ty, $assign_method:ident, $method:ident, $rhst:ty) => {
        impl $assign for InfInt {
            fn $assign_method(&mut self, rhs: $rhst) {
                *self = self.clone().$method(rhs);
            }
        }
    };
    ($assign:ty, $assign_method:ident, $method:ident) => {
        create_assign_operator!($assign, $assign_method, $method, Self);
    };
}

// ====< Arithmetic >====
impl Add for InfInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.sign == rhs.sign {
            Self {
                sign: self.sign,
                value: self.value + rhs.value,
            }
        } else {
            if self.value > rhs.value {
                Self {
                    sign: self.sign,
                    value: self.value - rhs.value,
                }
            } else if self.value < rhs.value {
                Self {
                    sign: rhs.sign,
                    value: rhs.value - self.value,
                }
            } else {
                Self::zero()
            }
        }
    }
}
create_assign_operator!(AddAssign, add_assign, add);

impl std::ops::Sub for InfInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        if self.sign != rhs.sign {
            Self {
                sign: self.sign,
                value: self.value + rhs.value,
            }
        } else {
            if self.value > rhs.value {
                Self {
                    sign: self.sign,
                    value: self.value - rhs.value,
                }
            } else if self.value < rhs.value {
                Self {
                    sign: !rhs.sign,
                    value: rhs.value - self.value,
                }
            } else {
                Self::zero()
            }
        }
    }
}
create_assign_operator!(SubAssign, sub_assign, sub);

impl Mul for InfInt {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            sign: self.sign == rhs.sign,
            value: self.value * rhs.value,
        }
    }
}
create_assign_operator!(MulAssign, mul_assign, mul);

impl Div for InfInt {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        Self {
            sign: self.sign == rhs.sign,
            value: self.value / rhs.value,
        }
    }
}
create_assign_operator!(DivAssign, div_assign, div);

// ====< Bitwise >====
impl std::ops::BitAnd for InfInt {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            sign: self.sign && rhs.sign,
            value: self.value & rhs.value,
        }
    }
}

impl std::ops::BitOr for InfInt {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self {
            sign: self.sign || rhs.sign,
            value: self.value | rhs.value,
        }
    }
}

impl std::ops::BitXor for InfInt {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        Self {
            sign: self.sign ^ rhs.sign,
            value: self.value ^ rhs.value,
        }
    }
}

impl std::ops::Not for InfInt {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self {
            sign: !self.sign,
            value: !self.value,
        }
    }
}

impl Shl<usize> for InfInt {
    type Output = Self;

    fn shl(self, rhs: usize) -> Self::Output {
        Self {
            sign: self.sign,
            value: self.value << rhs,
        }
    }
}
create_assign_operator!(ShlAssign<usize>, shl_assign, shl, usize);

impl Shr<usize> for InfInt {
    type Output = Self;

    fn shr(self, rhs: usize) -> Self::Output {
        Self {
            sign: self.sign,
            value: self.value >> rhs,
        }
    }
}
create_assign_operator!(ShrAssign<usize>, shr_assign, shr, usize);

// ====< Comparison >====
impl PartialEq for InfInt {
    fn eq(&self, other: &Self) -> bool {
        self.sign == other.sign && self.value == other.value
    }
}
impl Eq for InfInt {}
impl PartialOrd for InfInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.sign != other.sign {
            if self.sign {
                Some(Ordering::Greater)
            } else {
                Some(Ordering::Less)
            }
        } else {
            if self.sign {
                self.value.partial_cmp(&other.value)
            } else {
                other.value.partial_cmp(&self.value)
            }
        }
    }

    fn lt(&self, other: &Self) -> bool {
        if self.sign != other.sign {
            self.sign
        } else {
            if self.sign {
                self.value < other.value
            } else {
                other.value < self.value
            }
        }
    }

    fn le(&self, other: &Self) -> bool {
        if self.sign != other.sign {
            self.sign
        } else {
            if self.sign {
                self.value <= other.value
            } else {
                other.value <= self.value
            }
        }
    }

    fn gt(&self, other: &Self) -> bool {
        if self.sign != other.sign {
            !self.sign
        } else {
            if self.sign {
                self.value > other.value
            } else {
                other.value > self.value
            }
        }
    }

    fn ge(&self, other: &Self) -> bool {
        if self.sign != other.sign {
            !self.sign
        } else {
            if self.sign {
                self.value >= other.value
            } else {
                other.value >= self.value
            }
        }
    }
}
impl Ord for InfInt {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.sign != other.sign {
            if self.sign {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        } else {
            if self.sign {
                self.value.cmp(&other.value)
            } else {
                other.value.cmp(&self.value)
            }
        }
    }
}

#[cfg(test)]
mod inf_int_tests {
    use super::*;

    #[cfg(feature = "benchmark")]
    extern crate test;

    #[test]
    fn test_inf_int_macro() {
        let a = infint!(109);
        let b = infint!(-109);
        assert_eq!(
            a,
            InfInt::from_vec(true, vec![true, true, false, true, true, false, true])
        );
        assert_eq!(
            b,
            InfInt::from_vec(false, vec![true, true, false, true, true, false, true])
        );
    }

    #[test]
    fn test_inf_int_add() {
        let a = infint!(109);
        let b = infint!(-109);
        let c = infint!(109);
        let d = infint!(-109);
        assert_eq!(a.clone() + b.clone(), InfInt::zero());
        assert_eq!(a.clone() + c.clone(), infint!(218));
        assert_eq!(a.clone() + d.clone(), InfInt::zero());
        assert_eq!(b.clone() + c.clone(), InfInt::zero());
        assert_eq!(b.clone() + d.clone(), infint!(-218));
    }

    #[test]
    fn test_inf_int_sub() {
        let a = infint!(109);
        let b = infint!(-109);
        let c = infint!(109);
        let d = infint!(-109);
        assert_eq!(a.clone() - b.clone(), infint!(218));
        assert_eq!(a.clone() - c.clone(), InfInt::zero());
        assert_eq!(a.clone() - d.clone(), infint!(218));
        assert_eq!(b.clone() - c.clone(), infint!(-218));
        assert_eq!(b.clone() - d.clone(), InfInt::zero());
    }

    #[test]
    fn test_inf_int_mul() {
        let a = infint!(109);
        let b = infint!(-109);
        let c = infint!(109);
        let d = infint!(-109);
        assert_eq!(a.clone() * b.clone(), infint!(-11881));
        assert_eq!(a.clone() * c.clone(), infint!(11881));
        assert_eq!(a.clone() * d.clone(), infint!(-11881));
        assert_eq!(b.clone() * c.clone(), infint!(-11881));
        assert_eq!(b.clone() * d.clone(), infint!(11881));
    }

    #[test]
    fn test_inf_int_div() {
        let a = infint!(109);
        let b = infint!(-109);
        let c = infint!(109);
        let d = infint!(-109);
        assert_eq!(a.clone() / b.clone(), infint!(-1));
        assert_eq!(a.clone() / c.clone(), infint!(1));
        assert_eq!(a.clone() / d.clone(), infint!(-1));
        assert_eq!(b.clone() / c.clone(), infint!(-1));
        assert_eq!(b.clone() / d.clone(), infint!(1));
    }

    // #[test]
    // fn test_inf_int_bitand() {
    //     let a = infint!(109);
    //     let b = infint!(-109);
    //     let c = infint!(109);
    //     let d = infint!(-109);
    //     assert_eq!(a.clone() & b.clone(), infint!(1));
    //     assert_eq!(a.clone() & c.clone(), infint!(109));
    //     assert_eq!(a.clone() & d.clone(), infint!(1));
    //     assert_eq!(b.clone() & c.clone(), infint!(1));
    //     assert_eq!(b.clone() & d.clone(), infint!(-109));
    // }

    // #[test]
    // fn test_inf_int_bitor() {
    //     let a = infint!(109);
    //     let b = infint!(-109);
    //     let c = infint!(109);
    //     let d = infint!(-109);
    //     assert_eq!(a.clone() | b.clone(), infint!(-1));
    //     assert_eq!(a.clone() | c.clone(), infint!(-1));
    //     assert_eq!(a.clone() | d.clone(), infint!(-1));
    //     assert_eq!(b.clone() | c.clone(), infint!(-1));
    //     assert_eq!(b.clone() | d.clone(), infint!(-109));
    // }

    // #[test]
    // fn test_inf_int_bitxor() {
    //     let a = infint!(109);
    //     let b = infint!(-109);
    //     let c = infint!(109);
    //     let d = infint!(-109);
    //     assert_eq!(a.clone() ^ b.clone(), infint!(-2));
    //     assert_eq!(a.clone() ^ c.clone(), infint!(0));
    //     assert_eq!(a.clone() ^ d.clone(), infint!(-2));
    //     assert_eq!(b.clone() ^ c.clone(), infint!(-2));
    //     assert_eq!(b.clone() ^ d.clone(), infint!(0));
    // }

    // #[test]
    // fn test_inf_int_not() {
    //     let a = infint!(109);
    //     let b = infint!(-109);
    //     assert_eq!(!a.clone(), infint!(-110));
    //     assert_eq!(!b.clone(), infint!(108));
    // }

    #[test]
    fn test_inf_int_shl() {
        let a = infint!(109);
        assert_eq!(a.clone() << 1, infint!(218));
        assert_eq!(a.clone() << 2, infint!(436));
        assert_eq!(a.clone() << 3, infint!(872));
        assert_eq!(a.clone() << 4, infint!(1744));
        assert_eq!(a.clone() << 5, infint!(3488));
        assert_eq!(a.clone() << 6, infint!(6976));
        assert_eq!(a.clone() << 7, infint!(13952));
        assert_eq!(a.clone() << 8, infint!(27904));
    }

    #[test]
    fn test_inf_int_shr() {
        let a = infint!(109);
        assert_eq!(a.clone() >> 1, infint!(54));
        assert_eq!(a.clone() >> 2, infint!(27));
        assert_eq!(a.clone() >> 3, infint!(13));
        assert_eq!(a.clone() >> 4, infint!(6));
    }

    #[test]
    fn test_inf_int_cmp() {
        let a = infint!(109);
        let b = infint!(-109);
        let c = infint!(109);
        let d = infint!(-109);
        assert_eq!(a.clone().cmp(&b.clone()), Ordering::Greater);
        assert_eq!(a.clone().cmp(&c.clone()), Ordering::Equal);
        assert_eq!(a.clone().cmp(&d.clone()), Ordering::Greater);
        assert_eq!(b.clone().cmp(&c.clone()), Ordering::Less);
        assert_eq!(b.clone().cmp(&d.clone()), Ordering::Equal);
    }

    #[cfg(feature = "benchmark")]
    use test::Bencher;

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_int_add(b: &mut Bencher) {
        let a = infint!(109);
        let c = infint!(-109);
        b.iter(|| a.clone() + c.clone());
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_int_sub(b: &mut Bencher) {
        let a = infint!(109);
        let c = infint!(-109);
        b.iter(|| a.clone() - c.clone());
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_int_mul(b: &mut Bencher) {
        let a = infint!(109);
        let c = infint!(-109);
        b.iter(|| a.clone() * c.clone());
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_int_div(b: &mut Bencher) {
        let a = infint!(109);
        let c = infint!(-109);
        b.iter(|| a.clone() / c.clone());
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_int_cmp(b: &mut Bencher) {
        let a = infint!(109);
        let c = infint!(-109);
        b.iter(|| a.clone().cmp(&c.clone()));
    }
}
