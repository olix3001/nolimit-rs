use bitvec::vec::BitVec;

use crate::InfUInt;
use bitvec::prelude::Lsb0;

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
}
