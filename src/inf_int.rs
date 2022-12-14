use bitvec::vec::BitVec;

use crate::InfUInt;
use bitvec::prelude::Lsb0;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

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

    fn zero() -> Self {
        Self {
            sign: true,
            value: InfUInt::zero(),
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

// ====< Comparison >====
impl PartialEq for InfInt {
    fn eq(&self, other: &Self) -> bool {
        self.sign == other.sign && self.value == other.value
    }
}
impl Eq for InfInt {}

#[cfg(test)]
mod tests {
    use super::*;

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
}
