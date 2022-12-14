// TODO: Optimize this using SIMD

use core::fmt;
use std::{
    cmp::Ordering,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
    process::Output,
};

use bitvec::{prelude::*, vec::BitVec};

use crate::{
    fit_bits,
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
        infuint!(stringify!($value))
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
    ($assign:ident, $assign_method:ident, $method:ident) => {
        impl $assign for InfUInt {
            fn $assign_method(&mut self, rhs: Self) {
                *self = self.clone().$method(rhs);
            }
        }
    };
}

// ====< Constructors >====
impl InfUInt {
    pub fn new(bits: BitVec<u8, Lsb0>) -> Self {
        Self { bits }
    }

    pub fn num_bits(&self) -> usize {
        self.bits.len()
    }

    pub fn fit(&mut self) -> &mut Self {
        self.bits
            .resize(self.bits.len() - self.bits.leading_zeros(), false);
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

        write!(f, "{}", s)
    }
}

// ====< Operations >====
impl Add for InfUInt {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut bits = self.bits.clone();
        let mut rhs_bits = rhs.bits.clone();

        #[cfg(feature = "size-opt")]
        {
            fit_bits!(bits);
            fit_bits!(rhs_bits);
        }

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

        #[cfg(feature = "size-opt")]
        {
            fit_bits!(bits);
            fit_bits!(rhs_bits);
        }

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

        fit_bits!(bits);
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

        #[cfg(feature = "size-opt")]
        {
            fit_bits!(bits);
            fit_bits!(rhs_bits);
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
        let mut bits = self.bits.clone();
        let mut rhs_bits = rhs.bits.clone();

        #[cfg(feature = "size-opt")]
        {
            fit_bits!(bits);
            fit_bits!(rhs_bits);
        }

        if bits.len() < rhs_bits.len() {
            bits.resize(rhs_bits.len(), false);
        } else {
            rhs_bits.resize(bits.len(), false);
        }

        let mut result = Self::new(BitVec::new());
        let mut temp = Self::new(BitVec::new());

        for bit in bits.iter() {
            temp.bits.push(*bit);
            if temp >= rhs {
                temp -= rhs.clone();
                result.bits.push(true);
            } else {
                result.bits.push(false);
            }
        }

        fit_bits!(result.bits);
        result
    }
}

// ====< Comparisons >====
impl PartialEq for InfUInt {
    fn eq(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        a == b
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
        a < b
    }

    fn le(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        a <= b
    }

    fn gt(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        a > b
    }

    fn ge(&self, other: &Self) -> bool {
        let mut a = self.bits.clone();
        let mut b = other.bits.clone();
        fit_bits!(a);
        fit_bits!(b);
        a >= b
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
mod tests {

    #[cfg(feature = "benchmark")]
    extern crate test;

    #[test]
    fn display_infuint() {
        assert!(
            format!("{}", infuint!(1234567891011121314151617181920))
                == "1234567891011121314151617181920"
        );
    }

    #[test]
    fn debug_infuint() {
        assert!(format!("{:?}", infuint!(12345)) == "11000000111001");
    }

    #[test]
    fn eq_infuint() {
        assert!(
            infuint!(1234567891011121314151617181920) == infuint!(1234567891011121314151617181920)
        );

        assert!(
            infuint!(1234567891011121314151617181920) != infuint!(1234567891011121314151617181921)
        );
    }

    #[test]
    fn add_infuint() {
        assert!(
            infuint!(1234567891011121314151617181920) + infuint!(1234567891011121314151617181920)
                == infuint!(2469135782022242628303234363840),
            "{}",
            infuint!(1234567891011121314151617181920) + infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn sub_infuint() {
        assert!(
            infuint!(1234567891011121314151617181920) - infuint!(1234567891011121314151617181920)
                == infuint!(0),
            "{}",
            infuint!(1234567891011121314151617181920) - infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn mul_infuint() {
        assert!(
            infuint!(1234567891011121314151617181920) * infuint!(1234567891011121314151617181920)
                == infuint!(1524157877515647915714744640673134422038842655613362374886400),
            "{}",
            infuint!(1234567891011121314151617181920) * infuint!(1234567891011121314151617181920)
        );
    }

    #[test]
    fn div_infuint() {
        assert!(
            infuint!(1234567891011121314151617181920) / infuint!(1234567891011121314151617181920)
                == infuint!(1)
        );
        assert!(
            infuint!(100000) / infuint!(100) == infuint!(1000),
            "{}",
            infuint!(100000) / infuint!(100)
        );
    }

    #[test]
    fn assign_infuint() {
        let mut a = infuint!(1234567891011121314151617181920);
        a += infuint!(1234567891011121314151617181920);
        assert!(a == infuint!(1234567891011121314151617181920));
    }

    // ====< Benchmarks >====
    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_add(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(1234567891011121314151617181920);
            a + b
        });
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_sub(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(1234567891011121314151617181920);
            a - b
        });
    }

    #[cfg(feature = "benchmark")]
    #[bench]
    fn bench_mul(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(1234567891011121314151617181920);
            a * b
        });
    }

    #[cfg(all(feature = "benchmark", feature = "opt"))]
    #[bench]
    fn bench_mul_2_opt(b: &mut test::Bencher) {
        b.iter(|| {
            let a = infuint!(1234567891011121314151617181920);
            let b = infuint!(2);
            a * b
        });
    }
}
