use std::fmt::Display;

use bitvec::vec::BitVec;

pub fn add_decimal_strings(a: String, b: String) -> String {
    let mut s = String::new();
    let mut carry = 0;
    let mut i = 0;
    let mut j = 0;
    let mut a = a;
    let mut b = b;
    while i < a.len() || j < b.len() {
        let mut x = 0;
        let mut y = 0;
        if i < a.len() {
            x = a
                .chars()
                .nth(a.len() - i - 1)
                .unwrap()
                .to_digit(10)
                .unwrap();
        }
        if j < b.len() {
            y = b
                .chars()
                .nth(b.len() - j - 1)
                .unwrap()
                .to_digit(10)
                .unwrap();
        }
        let mut sum = x + y + carry;
        carry = sum / 10;
        sum = sum % 10;
        s = format!("{}{}", sum, s);
        i += 1;
        j += 1;
    }
    if carry != 0 {
        s = format!("{}{}", carry, s);
    }
    s
}

pub fn multiply_decimal_strings(a: String, b: String) -> String {
    if a.len() + b.len() == 0 {
        return "0".to_string();
    }

    let mut result: Vec<i32> = vec![0; a.len() + b.len()];

    let mut i_n1 = 0;
    let mut i_n2: usize;

    for i in (0..a.len()).rev() {
        let mut carry = 0;
        let n1 = a.chars().nth(i).unwrap().to_digit(10).unwrap() as i32;

        i_n2 = 0;

        for j in (0..b.len()).rev() {
            let n2 = b.chars().nth(j).unwrap().to_digit(10).unwrap() as i32;

            let sum = n1 * n2 + result[i_n1 + i_n2] + carry;

            carry = sum / 10;

            result[i_n1 + i_n2] = sum % 10;

            i_n2 += 1;
        }

        if carry > 0 {
            result[i_n1 + i_n2] += carry;
        }

        i_n1 += 1;
    }

    let mut i = result.len() as i64 - 1;
    while i >= 0 && result[i as usize] == 0 {
        i -= 1;
    }

    if i == -1 {
        return "0".to_string();
    }

    let mut s = String::new();

    while i >= 0 {
        s = format!("{}{}", s, result[i as usize]);
        i -= 1;
    }

    s
}

pub fn power_2(n: String) -> String {
    let mut s = "1".to_string();
    for _ in 0..n.parse::<i32>().unwrap() {
        s = multiply_decimal_strings(s, "2".to_string());
    }
    s
}

pub fn replace_nth_char(s: &String, idx: usize, newchar: char) -> String {
    s.chars()
        .enumerate()
        .map(|(i, c)| if i == idx { newchar } else { c })
        .collect()
}

// ====< Macros >====
#[macro_export]
macro_rules! fit_bits {
    ($bits:expr) => {
        $bits.resize($bits.len() - $bits.trailing_zeros(), false);
    };
}

#[macro_export]
macro_rules! fit_together {
    ($a:expr, $b: expr) => {
        #[cfg(not(feature = "size-opt"))]
        {
            fit_bits!($a);
            fit_bits!($b);
        }

        if $a.len() > $b.len() {
            $b.resize($a.len(), false);
        } else if $b.len() > $a.len() {
            $a.resize($b.len(), false);
        }
    };
}

// ====< Debug >====
pub trait BitVecDebug {
    fn debug(&self) -> String;
}
impl BitVecDebug for BitVec<u8> {
    fn debug(&self) -> String {
        let mut s = String::new();
        for i in 0..self.len() {
            if self[i] {
                s = format!("{}1", s);
            } else {
                s = format!("{}0", s);
            }
        }
        s
    }
}
