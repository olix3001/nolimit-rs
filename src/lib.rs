mod inf_uint;
pub use inf_uint::InfUInt;
mod utils;

#[cfg(test)]
mod tests {
    use crate::{
        infuint,
        utils::{add_decimal_strings, multiply_decimal_strings, power_2},
    };

    #[test]
    fn display() {
        assert!(
            format!("{}", infuint!("1234567891011121314151617181920"))
                == "1234567891011121314151617181920"
        );
    }

    #[test]
    fn debug() {
        assert!(format!("{:?}", infuint!("12345")) == "11000000111001");
    }
}
