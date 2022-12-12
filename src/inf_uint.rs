use core::fmt;

use bitvec::{bitvec, prelude::*, vec::BitVec};

use crate::utils::power_2;

pub struct InfUInt {
    bits: BitVec<u8, Lsb0>,
}

#[macro_export]
macro_rules! infuint {
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
                s = crate::utils::replace_nth_char_safe(&s, i, c.to_string().chars().next().unwrap());
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

impl InfUInt {
    pub fn new(bits: BitVec<u8, Lsb0>) -> Self {
        Self { bits }
    }

    pub fn num_bits(&self) -> usize {
        self.bits.len()
    }
}

impl fmt::Display for InfUInt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        let mut powers: Vec<String> = vec![];
        let mut bits = self.bits.clone();

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
