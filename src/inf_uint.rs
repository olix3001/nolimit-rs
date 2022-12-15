// TODO: Optimize this using SIMD

use core::fmt;
use std::{
    cmp::Ordering,
    ops::{
        Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div,
        DivAssign, Mul, MulAssign, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
    },
};

use bitvec::{prelude::*, vec::BitVec};

use crate::{
    fit_bits, fit_together,
    utils::{power_2, BitVecDebug},
};

#[derive(Clone)]
pub struct InfUInt {
    bits: BitVec<u8, Lsb0>,
}

// ====< Macros >====
#[macro_export]
macro_rules! infuint {
    ($value:tt) => {
        crate::infuint!(stringify!($value))
    };
    ($value:expr) => {{
        use bitvec::{prelude::*, bitvec};

        let mut s = $value.to_string();
        let mut bits = bitvec![u8, Lsb0; 0; 0];

        while s != "0" && s != "" {
            let mut t = 0;
            let mut old_t = 0;
            let mut i = 0;
            for ch in s.clone().chars() {
                let mut c = ch.to_digit(10).unwrap();
                t = ((old_t * 10 + c) & 1);
                c = (c + old_t * 10) >> 1;
                old_t = t;
                s = crate::utils::replace_nth_char(&s, i, c.to_string().chars().next().unwrap());
                i += 1;
            }
            bits.push(t == 1);

            if s.chars().next().unwrap().to_digit(10).unwrap() == 0 {
                s = s[1..].to_string();
            }
        }

        crate::InfUInt::new(
            bits
        )
    }};
}

macro_rules! create_assign_operator {
    ($assign:ty, $assign_method:ident, $method:ident, $rhst:ty) => {
        impl $assign for InfUInt {
            fn $assign_method(&mut self, rhs: $rhst) {
                *self = self.clone().$method(rhs);
            }
        }
    };
    ($assign:ident, $assign_method:ident, $method:ident) => {
        create_assign_operator!($assign, $assign_method, $method, Self);
    };
}

// ====< Constructors >====
impl InfUInt {
    pub fn new(bits: BitVec<u8, Lsb0>) -> Self {
        Self { bits }
    }

    pub fn from_vec(bits: Vec<bool>) -> Self {
        Self {
            bits: bits.into_iter().rev().collect(),
        }
    }

    pub fn to_usize(&self) -> usize {
        let mut n = 0;
        for (i, bit) in self.bits.iter().enumerate() {
            if *bit {
                n += 2usize.pow(i as u32);
            }
        }
        n
    }

    pub fn zero() -> Self {
        Self::new(BitVec::new())
    }

    pub fn num_bits(&self) -> usize {
        self.bits.len()
    }

    pub fn fit(&mut self) -> &mut Self {
        fit_bits!(self.bits);
        self
    }
}

// ====< Display >====
impl fmt::Display for InfUInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        let mut powers: Vec<String> = vec![];
        let bits = self.bits.clone();

        for (i, bit) in bits.iter().enumerate() {
            if *bit {
                powers.push(power_2(i.to_string()));
            }
        }

        s = powers.iter().fold("0".to_string(), |acc, x| {
            crate::utils::add_decimal_strings(acc, x.to_string())
        });

        write!(f, "{}", s)
    }
}

impl fmt::Debug for InfUInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        let bits = self.bits.clone();

        for bit in bits.iter() {
            s = format!("{}{}", if *bit { "1" } else { "0" }, s);
        }

        write!(f, "0b{}", s)
    }
}

// ====< Operations >====
impl Add for InfUInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut bits = self.bits.clone();
        let mut rhs_bits = rhs.bits.clone();

        let mut carry = false;

        if bits.len() < rhs_bits.len() {
            bits.resize(rhs_bits.len(), false);
        } else {
            rhs_bits.resize(bits.len(), false);
        }

        for (i, mut bit) in bits.iter_mut().enumerate() {
            let sum = *bit ^ rhs_bits[i] ^ carry;
            carry = (*bit && rhs_bits[i]) || (carry && (*bit ^ rhs_bits[i]));
            *bit = sum;
        }

        if carry {
            bits.push(true);
        }

        Self::new(bits)
    }
}
create_assign_operator!(AddAssign, add_assign, add);

impl Sub for InfUInt {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut bits = self.bits.clone();
        let mut rhs_bits = rhs.bits.clone();

        let mut carry = false;

        if bits.len() < rhs_bits.len() {
            bits.resize(rhs_bits.len(), false);
        } else {
            rhs_bits.resize(bits.len(), false);
        }

        for (i, mut bit) in bits.iter_mut().enumerate() {
            let sum = *bit ^ rhs_bits[i] ^ carry;
            carry = (!*bit && rhs_bits[i]) || (carry && !(*bit ^ rhs_bits[i]));
            *bit = sum;
        }

        Self::new(bits)
    }
}
create_assign_operator!(SubAssign, sub_assign, sub);

impl Mul for InfUInt {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut bits = self.bits.clone();
        let mut rhs_bits = rhs.bits.clone();

        // Opt for 2
        #[cfg(feature = "opt")]
        {
            if rhs == infuint!(2) {
                bits.push(false);
                return Self::new(bits);
            }
            if self == infuint!(2) {
                rhs_bits.push(false);
                return Self::new(rhs_bits);
            }
        }

        if bits.len() < rhs_bits.len() {
            bits.resize(rhs_bits.len(), false);
        } else {
            rhs_bits.resize(bits.len(), false);
        }

        let mut temp: Vec<BitVec<u8, Lsb0>> = Vec::new();
        for bit in rhs_bits.iter() {
            let mut temp_bits = BitVec::new();
            for rbit in bits.iter() {
                let mr = *bit && *rbit;
                temp_bits.push(mr);
            }
            temp_bits.reverse();
            temp.push(temp_bits);
        }

        let mut result = Self::new(BitVec::new());

        for (i, bits) in temp.iter_mut().enumerate() {
            bits.resize(bits.len() + i, false);
            bits.reverse();
            result += Self::new(bits.clone());
        }

        result
    }
}
create_assign_operator!(MulAssign, mul_assign, mul);

impl Div for InfUInt {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        if self < rhs {
            return Self::new(BitVec::new());
        }
        if self == rhs {
            return infuint!(1);
        }

        let mut a = if self > rhs {
            self.clone()
        } else {
            rhs.clone()
        };
        let b = if self > rhs {
            rhs.clone()
        } else {
            self.clone()
        };

        // Opt for 2
        #[cfg(feature = "opt")]
        {
            if rhs == infuint!(2) {
                bits.pop();
                return Self::new(bits);
            }
            if self == infuint!(2) {
                rhs_bits.pop();
                return Self::new(rhs_bits);
            }
        }

        // TODO: Optimize
        let mut result = infuint!(0);

        while a >= b {
            a -= b.clone();
            result += infuint!(1);
        }

        result
    }
}
create_assign_operator!(DivAssign, div_assign, div);

// ====< Bit Manipulation >====
impl Not for InfUInt {
    type Output = Self;

    fn not(self) -> Self::Output {
        let mut bits = self.bits.clone();
        for mut bit in bits.iter_mut() {
            *bit = !*bit;
        }
        Self::new(bits)
    }
}

impl BitAnd for InfUInt {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let mut bits = self.bits.clone();
        let mut rhs_bits = rhs.bits.clone();

        if bits.len() < rhs_bits.len() {
            bits.resize(rhs_bits.len(), false);
        } else {
            rhs_bits.resize(bits.len(), false);
        }

        for (i, mut bit) in bits.iter_mut().enumerate() {
            *bit = *bit && rhs_bits[i];
        }

        Self::new(bits)
    }
}
create_assign_operator!(BitAndAssign, bitand_assign, bitand);

impl BitOr for InfUInt {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let mut bits = self.bits.clone();
        let mut rhs_bits = rhs.bits.clone();

        if bits.len() < rhs_bits.len() {
            bits.resize(rhs_bits.len(), false);
        } else {
            rhs_bits.resize(bits.len(), false);
        }

        for (i, mut bit) in bits.iter_mut().enumerate() {
            *bit = *bit || rhs_bits[i];
        }

        Self::new(bits)
    }
}
create_assign_operator!(BitOrAssign, bitor_assign, bitor);

impl BitXor for InfUInt {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut bits = self.bits.clone();
        let mut rhs_bits = rhs.bits.clone();

        if bits.len() < rhs_bits.len() {
            bits.resize(rhs_bits.len(), false);
        } else {
            rhs_bits.resize(bits.len(), false);
        }

        for (i, mut bit) in bits.iter_mut().enumerate() {
            *bit = *bit ^ rhs_bits[i];
        }

        Self::new(bits)
    }
}
create_assign_operator!(BitXorAssign, bitxor_assign, bitxor);

impl Shl<usize> for InfUInt {
    type Output = Self;

    fn shl(self, rhs: usize) -> Self::Output {
        let mut bits = self.bits.clone();
        bits.reverse();
        bits.resize(bits.len() + rhs, false);
        bits.reverse();
        Self::new(bits)
    }
}
create_assign_operator!(ShlAssign<usize>, shl_assign, shl, usize);

impl Shr<usize> for InfUInt {
    type Output = Self;

    fn shr(self, rhs: usize) -> Self::Output {
        let mut bits = self.bits.clone();
        bits.reverse();
        bits.resize(bits.len() - rhs, false);
        bits.reverse();
        Self::new(bits)
    }
}
create_assign_operator!(ShrAssign<usize>, shr_assign, shr, usize);

// ====< Comparisons >====
impl PartialEq for InfUInt {
    fn eq(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_together!(a, b);
        for i in 0..a.len() {
            if a[i] != b[i] {
                return false;
            }
        }
        return true;
    }
}
impl Eq for InfUInt {}
impl PartialOrd for InfUInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        a.partial_cmp(&b)
    }

    fn lt(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        if a.len() < b.len() {
            return true;
        } else if a.len() > b.len() {
            return false;
        } else {
            for i in (0..a.len()).rev() {
                if a[i] && !b[i] {
                    return false;
                } else if !a[i] && b[i] {
                    return true;
                }
            }
            return false;
        }
    }

    fn le(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        if a == b {
            return true;
        } else {
            return self.lt(other);
        }
    }

    fn gt(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        if a.len() > b.len() {
            return true;
        } else if a.len() < b.len() {
            return false;
        } else {
            for i in (0..a.len()).rev() {
                if a[i] && !b[i] {
                    return true;
                } else if !a[i] && b[i] {
                    return false;
                }
            }
            return false;
        }
    }

    fn ge(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        if a == b {
            return true;
        } else {
            return self.gt(other);
        }
    }
}
impl Ord for InfUInt {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        a.cmp(&b)
    }
}

// ====< Tests >====
#[cfg(test)]
mod inf_uint_tests {
    use crate::InfUInt;

    #[cfg(feature = "benchmark")]
    extern crate test;

    #[test]
    fn test_inf_uint_fit() {
        assert!(
            *InfUInt::from_vec(vec![true, false, true, false]).fit()
                == InfUInt::from_vec(vec![true, false, true, false])
        );

        assert!(
            *InfUInt::from_vec(vec![false, false, false, false]).fit() == InfUInt::from_vec(vec![])
        );

        assert!(
            *InfUInt::from_vec(vec![true, true, true, true]).fit()
                == InfUInt::from_vec(vec![true, true, true, true])
        );

        assert!(
            *InfUInt::from_vec(vec![false, false, false, true]).fit()
                == InfUInt::from_vec(vec![true]),
            "Got {:?}",
            InfUInt::from_vec(vec![false, false, false, true]).fit()
        );
    }

    #[test]
    fn test_inf_uint_display() {
        assert!(
            format!("{}", infuint!(1234567891011121314151617181920))
                == "1234567891011121314151617181920"
        );
        assert!(format!("{}", infuint!(900)) == "900");
    }

    #[test]
    fn test_inf_uint_debug() {
        assert!(format!("{:?}", infuint!(12345)) == "0b11000000111001");
    }

    #[test]
    fn test_inf_uint_eq() {
        assert!(
            infuint!(1234567891011121314151617181920) == infuint!(1234567891011121314151617181920)
        );

        assert!(
            infuint!(1234567891011121314151617181920) != infuint!(1234567891011121314151617181921)
        );
    }

    #[test]
    fn test_inf_uint_add() {
        assert!(
            infuint!(1234567891011121314151617181920) + infuint!(1234567891011121314151617181920)
                == infuint!(2469135782022242628303234363840),
            "{}",
            infuint!(1234567891011121314151617181920) + infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn test_inf_uint_sub() {
        assert!(
            infuint!(1234567891011121314151617181920) - infuint!(1234567891011121314151617181920)
                == infuint!(0),
            "1: {}",
            infuint!(1234567891011121314151617181920) - infuint!(1234567891011121314151617181920)
        );

        assert!(
            infuint!(1000) - infuint!(100) == infuint!(900),
            "2: {}",
            infuint!(1000) - infuint!(100)
        );
        assert!(
            infuint!(8200) - infuint!(100) == infuint!(8100),
            "3: {:?} ({:?})",
            infuint!(8200) - infuint!(100),
            infuint!(8100)
        );
    }

    #[test]
    fn test_inf_uint_mul() {
        assert!(
            infuint!(1234567891011121314151617181920) * infuint!(1234567891011121314151617181920)
                == infuint!(1524157877515647915714744640673134422038842655613362374886400),
            "{}",
            infuint!(1234567891011121314151617181920) * infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn test_inf_uint_div() {
        assert!(
            infuint!(1234567891011121314151617181920) / infuint!(1234567891011121314151617181920)
                == infuint!(1),
            "1: {}",
            infuint!(1234567891011121314151617181920) / infuint!(1234567891011121314151617181920)
        );
        assert!(
            infuint!(10000) / infuint!(100) == infuint!(100),
            "2: {}",
            infuint!(10000) / infuint!(100)
        );
    }

    #[test]
    fn test_inf_uint_assign() {
        let mut a = infuint!(1234567891011121314151617181920);
        a += infuint!(1234567891011121314151617181920);
        assert!(a == infuint!(2469135782022242628303234363840));
    }

    #[test]
    fn test_inf_uint_cmp() {
        assert!(
            infuint!(1234567891011121314151617181920) > infuint!(1234567891011121314151617181919)
        );
        assert!(
            infuint!(1234567891011121314151617181920) < infuint!(1234567891011121314151617181921)
        );
        assert!(
            infuint!(1234567891011121314151617181920) >= infuint!(1234567891011121314151617181919)
        );
        assert!(
            infuint!(1234567891011121314151617181920) <= infuint!(1234567891011121314151617181921)
        );
        assert!(
            infuint!(1234567891011121314151617181920) >= infuint!(1234567891011121314151617181920)
        );
        assert!(
            infuint!(1234567891011121314151617181920) <= infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn test_inf_uint_and() {
        assert!(
            infuint!(1234567891011121314151617181920) & infuint!(1234567891011121314151617181920)
                == infuint!(1234567891011121314151617181920),
            "{}",
            infuint!(1234567891011121314151617181920) & infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn test_inf_uint_or() {
        assert!(
            infuint!(1234567891011121314151617181920) | infuint!(1234567891011121314151617181920)
                == infuint!(1234567891011121314151617181920),
            "{}",
            infuint!(1234567891011121314151617181920) | infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn test_inf_uint_xor() {
        assert!(
            infuint!(1234567891011121314151617181920) ^ infuint!(1234567891011121314151617181920)
                == infuint!(0),
            "{}",
            infuint!(1234567891011121314151617181920) ^ infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn test_inf_uint_shl() {
        assert!(
            infuint!(1234567891011121314151617181920) << 1
                == infuint!(2469135782022242628303234363840),
            "{}",
            infuint!(1234567891011121314151617181920) << 1
        );
    }

    #[test]
    fn test_inf_uint_shr() {
        assert!(
            infuint!(1234567891011121314151617181920) >> 1
                == infuint!(617283945505560657075808590960),
            "{}",
            infuint!(1234567891011121314151617181920) >> 1
        );
    }

    #[test]
    fn test_inf_uint_not() {
        assert!(
            !infuint!(1234567891011121314151617181920) == infuint!(33082709217108087345086023455),
            "\nL: !{:?}\nR:  {:?}",
            infuint!(1234567891011121314151617181920),
            !infuint!(1234567891011121314151617181920)
        );
    }

    // ====< Benchmarks >====
    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_uint_add(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(1234567891011121314151617181920);
            a + b
        });
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_uint_sub(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(1234567891011121314151617181920);
            a - b
        });
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_uint_mul(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(1234567891011121314151617181920);
            a * b
        });
    }

    #[cfg(all(feature = "benchmark", feature = "opt"))]
    #[bench]
    fn bench_inf_uint_mul_2_opt(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(2);
            a * b
        });
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_inf_uint_div(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(100000);
            let b = infuint!(100);
            a / b
        });
    }

    #[cfg(all(feature = "benchmark", feature = "opt"))]
    #[bench]
    fn bench_inf_uint_div_2_opt(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(2);
            a / b
        });
    }
}
