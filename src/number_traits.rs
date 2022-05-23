use core::fmt::{
    Debug, Display,
    LowerExp, UpperExp,
    LowerHex, UpperHex,
    Binary, Octal,
};
use core::num::{ParseIntError, FpCategory};
use core::iter::{Product, Sum};
use core::str::FromStr;
use core::hash::Hash;
use core::ops::*;

/// A number.
pub trait Number:
    Sized + Copy + Clone + Default +
    Debug + Display + LowerExp + UpperExp +
    PartialEq + PartialOrd +
    
    FromStr +

    Add<Output = Self> + AddAssign +
    Sub<Output = Self> + SubAssign +
    Mul<Output = Self> + MulAssign +
    Div<Output = Self> + DivAssign +
    Rem<Output = Self> + RemAssign +
    Product + Sum +
{
    /// The smallest value that can be represented by this type.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(<u16 as Number>::MIN, 0);
    /// assert_eq!(<i32 as Number>::MIN, -2147483648);
    /// ```
    const MIN: Self;

    /// The largest value that can be represented by this type.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(<u16 as Number>::MAX, 65535);
    /// assert_eq!(<i32 as Number>::MAX, 2147483647);
    /// ```
    const MAX: Self;

    /// The size of this type in bits.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(<u16 as Number>::BITS, 16);
    /// assert_eq!(<i32 as Number>::BITS, 32);
    /// ```
    const BITS: u32;

    /// The value zero.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(<u16 as Number>::ZERO, 0);
    /// assert_eq!(<f32 as Number>::ZERO, 0.0);
    /// ```
    const ZERO: Self;

    /// The value one.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(<u16 as Number>::ONE, 1);
    /// assert_eq!(<f32 as Number>::ONE, 1.0);
    /// ```
    const ONE: Self;

    /// Calculates the quotient of Euclidean division of `self` by `rhs`.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::div_euclid(7, 4), 1); // 7 >= 4 * 1
    /// assert_eq!(Number::div_euclid(7, -4), -1); // 7 >= -4 * -1
    /// assert_eq!(Number::div_euclid(-7, 4), -2); // -7 >= 4 * -2
    /// assert_eq!(Number::div_euclid(-7, -4), 2); // -7 >= -4 * 2
    /// ```
    fn div_euclid(self, rhs: Self) -> Self;

    /// Calculates the least nonnegative remainder of `self (mod rhs)`.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::rem_euclid(7, 4), 3);
    /// assert_eq!(Number::rem_euclid(7, -4), 3);
    /// assert_eq!(Number::rem_euclid(-7, 4), 1);
    /// assert_eq!(Number::rem_euclid(-7, -4), 1);
    /// ```
    fn rem_euclid(self, rhs: Self) -> Self;

    /// Computes the absolute value of `self`.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::abs(7), 7);
    /// assert_eq!(Number::abs(-7), 7);
    /// assert_eq!(Number::abs(-7.0), 7.0);
    /// assert_eq!(Number::abs(-7.0), 7.0);
    /// ```
    fn abs(self) -> Self;

    /// Computes the absolute difference between self and other.
    /// 
    /// If `self < other` then the result is `other - self`, otherwise it is `self - other`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::abs_diff(7, 4), 3);
    /// assert_eq!(Number::abs_diff(7, -4), 11);
    /// assert_eq!(Number::abs_diff(-7.5, 4.2), 11.7);
    /// assert_eq!(Number::abs_diff(-7.1, -4.6), 2.5);
    /// ```
    fn abs_diff(self, other: Self) -> Self;

    /// Returns a number representing sign of self.
    ///
    /// - `0` if the number is zero
    /// - `1` if the number is positive
    /// - `-1` if the number is negative.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::signum(0), 0);
    /// assert_eq!(Number::signum(-541), -1);
    /// assert_eq!(Number::signum(35.14), 1.0);
    /// assert_eq!(Number::signum(-6.2), -1.0);
    /// ```
    fn signum(self) -> Self;

    /// Returns `true` if `self` is positive and `false` if the number is zero or negative.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::is_positive(0), false);
    /// assert_eq!(Number::is_positive(-541), false);
    /// assert_eq!(Number::is_positive(35.14), true);
    /// assert_eq!(Number::is_positive(-6.2), false);
    /// ```
    fn is_positive(self) -> bool;

    /// Returns `true` if `self` is negative and `false` if the number is zero or positive.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::is_negative(0), false);
    /// assert_eq!(Number::is_negative(-541), true);
    /// assert_eq!(Number::is_negative(35.14), false);
    /// assert_eq!(Number::is_negative(-6.2), true);
    /// ```
    fn is_negative(self) -> bool;

    /// Compares and returns the maximum of two values.
    /// 
    /// Returns the second argument if the comparison determines them to be equal.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::max(7, 4), 7);
    /// assert_eq!(Number::max(-7, -4), -4);
    /// assert_eq!(Number::max(-7.2, 4.4), 4.4);
    /// assert_eq!(Number::max(-7.2, -4.1), -4.1);
    /// ```
    fn max(self, other: Self) -> Self;

    /// Compares and returns the minimum of two values.
    ///
    /// Returns the first argument if the comparison determines them to be equal.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// assert_eq!(Number::min(7, 4), 4);
    /// assert_eq!(Number::min(-7, -4), -7);
    /// assert_eq!(Number::min(-7.2, 4.4), -7.2);
    /// assert_eq!(Number::min(-7.2, -4.1), -7.2);
    /// ```
    fn min(self, other: Self) -> Self;

    /// Restrict a value to a certain interval.
    /// 
    /// Returns `max` if `self` is greater than `max`, and `min` if `self` is less than `min`. Otherwise this returns `self`.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// Panics if `min > max`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Number;
    /// 
    /// fn test<T: Number>(a: T, min: T, max: T, r: T) {
    ///     assert_eq!(a.clamp(min, max), r);
    /// }
    /// 
    /// assert_eq!(Number::clamp(7, 4, 6), 6);
    /// assert_eq!(Number::clamp(-7, -4, 8), -4);
    /// assert_eq!(Number::clamp(-7.2, 4.4, 6.0), 4.4);
    /// assert_eq!(Number::clamp(-7.2, -4.1, 8.0), -4.1);
    /// ```
    fn clamp(self, min: Self, max: Self) -> Self;
}

/// An unsigned number.
pub trait Unsigned: Number {}

/// A signed number.
pub trait Signed: Number + Neg<Output = Self> {}

/// An integer.
pub trait Integer:
    Number +
    Hash + Ord + Eq +
    Binary + Octal + LowerHex + UpperHex +

    From<bool> +
    TryFrom<u8> + TryFrom<u16> + TryFrom<u32> + TryFrom<u64> + TryFrom<u128> + TryFrom<usize> +
    TryFrom<i8> + TryFrom<i16> + TryFrom<u16> + TryFrom<i64> + TryFrom<i128> + TryFrom<isize> +

    BitAnd<Output = Self> + BitAndAssign +
    BitOr<Output = Self> + BitOrAssign +
    BitXor<Output = Self> + BitXorAssign +
    Shl<u8, Output = Self> + ShlAssign<u8> +
    Shl<i8, Output = Self> + ShlAssign<i8> +
    Shl<u16, Output = Self> + ShlAssign<u16> +
    Shl<i16, Output = Self> + ShlAssign<i16> +
    Shl<u32, Output = Self> + ShlAssign<u32> +
    Shl<u16, Output = Self> + ShlAssign<u16> +
    Shl<u64, Output = Self> + ShlAssign<u64> +
    Shl<i64, Output = Self> + ShlAssign<i64> +
    Shl<u128, Output = Self> + ShlAssign<u128> +
    Shl<i128, Output = Self> + ShlAssign<i128> +
    Shl<usize, Output = Self> + ShlAssign<usize> +
    Shl<isize, Output = Self> + ShlAssign<isize> +
    Shr<u8, Output = Self> + ShrAssign<u8> +
    Shr<i8, Output = Self> + ShrAssign<i8> +
    Shr<u16, Output = Self> + ShrAssign<u16> +
    Shr<i16, Output = Self> + ShrAssign<i16> +
    Shr<u32, Output = Self> + ShrAssign<u32> +
    Shr<u16, Output = Self> + ShrAssign<u16> +
    Shr<u64, Output = Self> + ShrAssign<u64> +
    Shr<i64, Output = Self> + ShrAssign<i64> +
    Shr<u128, Output = Self> + ShrAssign<u128> +
    Shr<i128, Output = Self> + ShrAssign<i128> +
    Shr<usize, Output = Self> + ShrAssign<usize> +
    Shr<isize, Output = Self> + ShrAssign<isize> +
    Not<Output = Self> +
{
    /// Converts a string slice in a given base to an integer.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::from_str_radix("A", 16), Ok(10));
    /// ```
    fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError>;
    
    /// Returns the number of ones in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// // 532 = 00000000 00000000 00000010 00010100 in binary
    /// //                               ^     ^ ^ -> 3 ones
    /// 
    /// assert_eq!(Integer::count_ones(532), 3);
    /// ```
    fn count_ones(self) -> u32;

    /// Returns the number of zeros in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// // 532 = 00000000 00000000 00000010 00010100 in binary
    /// //       ^^^^^^^^ ^^^^^^^^ ^^^^^^ ^ ^^^ ^ ^^ -> 29 zeros
    /// 
    /// assert_eq!(Integer::count_zeros(532), 29);
    /// ```
    fn count_zeros(self) -> u32;

    /// Returns the number of leading zeros in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// // 532 = 00000000 00000000 00000010 00010100 in binary
    /// //       ^^^^^^^^ ^^^^^^^^ ^^^^^^ -> 22 leading zeros
    /// 
    /// assert_eq!(Integer::leading_zeros(532), 22);
    /// ```
    fn leading_zeros(self) -> u32;

    /// Returns the number of trailing zeros in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// // 532 = 00000000 00000000 00000010 00010100 in binary
    /// //                                        ^^ -> 2 trailing zeros
    /// 
    /// assert_eq!(Integer::trailing_zeros(532), 2);
    /// ```
    fn trailing_zeros(self) -> u32;

    /// Returns the number of leading ones in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// // -268434921 = 11110000 00000000 00000010 00010111 in binary
    /// //              ^^^^ -> 4 leading ones
    /// 
    /// assert_eq!(Integer::leading_ones(-268434921), 4);
    /// ```
    fn leading_ones(self) -> u32;

    /// Returns the number of trailing ones in the binary representation of `self`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// // -268434921 = 11110000 00000000 00000010 00010111 in binary
    /// //                                              ^^^ -> 3 trailing ones
    /// 
    /// assert_eq!(Integer::trailing_ones(-268434921), 3);
    /// ```
    fn trailing_ones(self) -> u32;

    /// Shifts the bits to the left by a specified amount, `n`, wrapping the truncated bits to the end of the resulting integer.
    /// 
    /// Please note this isn’t the same operation as the `<<` shifting operator!
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// //             ╭─←─╮
    /// // 538968064 = │ 00100000 00100000 00000000 00000000 in binary
    /// //             │      ╭──←──╯
    /// // 67108868  = │ 00000100 00000000 00000000 00000100 in binary
    /// //             ╰────────────────→────────────────╯
    /// 
    /// assert_eq!(Integer::rotate_left(538968064, 5), 67108868);
    /// ```
    fn rotate_left(self, n: u32) -> Self;

    /// Shifts the bits to the right by a specified amount, `n`, wrapping the truncated bits to the beginning of the resulting integer.
    /// 
    /// Please note this isn’t the same operation as the `>>` shifting operator!
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// //                                              ╭──────→─────╮
    /// // 8388610   = 00000000 10000000 00000000 00000010 in binary │
    /// //                      ╰─→─╮                                │
    /// // 537395200 = 00100000 00001000 00000000 00000000 in binary │
    /// //               ╰─────────────────────←─────────────────────╯
    /// 
    /// assert_eq!(Integer::rotate_right(8388610, 4), 537395200);
    /// ```
    fn rotate_right(self, n: u32) -> Self;

    /// Reverses the byte order of the integer.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// // 1879048215 = 01110000 00000000 00000000 00010111 in binary
    /// //               ──┬───   ──┬───   ───┬──   ───┬── 
    /// //                 ╰────────│────→────│───────╮│
    /// //                          ╰────→───╮│       ││
    /// //                           ╭───←───│╯       ││
    /// //                  ╭────────│───←───│────────│╯
    /// //               ───┴──   ───┴──   ──┴───   ──┴─── 
    /// // 385876080  = 00010111 00000000 00000000 01110000 in binary
    /// 
    /// assert_eq!(Integer::swap_bytes(1879048215), 385876080);
    /// ```
    fn swap_bytes(self) -> Self;

    /// Reverses the order of bits in the integer. The least significant bit becomes the most significant bit,
    /// second least-significant bit becomes second most-significant bit, etc.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// //                ╭─────────────────────→────────────────────╮
    /// // 268436480 = 00010000 00000000 00000100 00000000 in binary │
    /// //                        ╭─────←─────╯                      │
    /// // 2097160   = 00000000 00100000 00000000 00001000 in binary │
    /// //                                            ╰───────←──────╯
    /// 
    /// assert_eq!(Integer::reverse_bits(268436480), 2097160);
    /// ```
    fn reverse_bits(self) -> Self;

    /// Converts an integer from big endian to the target’s endianness.
    /// 
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// let n = 0x1Ai32;
    /// 
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(Integer::from_be(n), n);
    /// } else {
    ///     assert_eq!(Integer::from_be(n), Integer::swap_bytes(n));
    /// }
    /// ```
    fn from_be(x: Self) -> Self;

    /// Converts an integer from little endian to the target’s endianness.
    /// 
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// let n = 0x1Ai32;
    /// 
    /// if cfg!(target_endian = "little") {
    ///     assert_eq!(Integer::from_le(n), n);
    /// } else {
    ///     assert_eq!(Integer::from_le(n), Integer::swap_bytes(n));
    /// }
    /// ```
    fn from_le(x: Self) -> Self;
    
    /// Converts `self` to big endian from the target’s endianness.
    /// 
    /// On big endian this is a no-op. On little endian the bytes are swapped.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// let n = 0x1Ai32;
    /// 
    /// if cfg!(target_endian = "big") {
    ///     assert_eq!(Integer::to_be(n), n);
    /// } else {
    ///     assert_eq!(Integer::to_be(n), Integer::swap_bytes(n));
    /// }
    /// ```
    fn to_be(self) -> Self;

    /// Converts `self` to little endian from the target’s endianness.
    /// 
    /// On little endian this is a no-op. On big endian the bytes are swapped.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// let n = 0x1Ai32;
    /// 
    /// if cfg!(target_endian = "little") {
    ///     assert_eq!(Integer::to_le(n), n);
    /// } else {
    ///     assert_eq!(Integer::to_le(n), Integer::swap_bytes(n));
    /// }
    /// ```
    fn to_le(self) -> Self;

    /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_add(5, 2), Some(7));
    /// assert_eq!(Integer::checked_add(250u8, 24), None);
    /// ```
    fn checked_add(self, rhs: Self) -> Option<Self>;

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if underflow occurred.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_sub(5, 2), Some(3));
    /// assert_eq!(Integer::checked_sub(1u8, 12), None);
    /// ```
    fn checked_sub(self, rhs: Self) -> Option<Self>;

    /// Checked integer multiplication. Computes `self * rhs`, returning `None` if underflow occurred.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_mul(5, 2), Some(10));
    /// assert_eq!(Integer::checked_mul(200u8, 12), None);
    /// ```
    fn checked_mul(self, rhs: Self) -> Option<Self>;

    /// Checked integer division. Computes `self / rhs`, returning `None` if `rhs == 0` or the division results in overflow.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_div(128, 2), Some(64));
    /// assert_eq!(Integer::checked_div(1u8, 0), None);
    /// ```
    fn checked_div(self, rhs: Self) -> Option<Self>;

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if `rhs == 0` or the division results in overflow.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_rem(128, 2), Some(0));
    /// assert_eq!(Integer::checked_rem(1u8, 0), None);
    /// ```
    fn checked_rem(self, rhs: Self) -> Option<Self>;

    /// Checked Euclidean division. Computes `self.div_euclid(rhs)`, returning `None` if `rhs == 0` or the division results in overflow.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_div_euclid(128, 2), Some(64));
    /// assert_eq!(Integer::checked_div_euclid(1u8, 0), None);
    /// ```
    fn checked_div_euclid(self, rhs: Self) -> Option<Self>;

    /// Checked Euclidean remainder. Computes `self.rem_euclid(rhs)`, returning `None` if `rhs == 0` or the division results in overflow.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_rem_euclid(128, 2), Some(0));
    /// assert_eq!(Integer::checked_rem_euclid(1u8, 0), None);
    /// ```
    fn checked_rem_euclid(self, rhs: Self) -> Option<Self>;

    /// Checked shift left. Computes `self << rhs`, returning `None` if `rhs` is larger than or equal to the number of bits in `self`.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_shl(0x10, 4), Some(0x100));
    /// assert_eq!(Integer::checked_shl(0x10, 200), None);
    /// ```
    fn checked_shl(self, rhs: u32) -> Option<Self>;

    /// Checked shift right. Computes `self >> rhs`, returning `None` if `rhs` is larger than or equal to the number of bits in `self`.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_shr(0x100, 4), Some(0x10));
    /// assert_eq!(Integer::checked_shr(0x100, 200), None);
    /// ```
    fn checked_shr(self, rhs: u32) -> Option<Self>;

    /// Checked negation. Computes `-self`, returning `None` if overflow occurred.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_neg(10), Some(-10));
    /// assert_eq!(Integer::checked_neg(-128i8), None);
    /// ```
    fn checked_neg(self) -> Option<Self>;

    /// Checked absolute value. Computes `self.abs()`, returning `None` if overflow occurred.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_abs(-10), Some(10));
    /// assert_eq!(Integer::checked_abs(-128i8), None);
    /// ```
    fn checked_abs(self) -> Option<Self>;

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None` if overflow occurred.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::checked_pow(2, 4), Some(16));
    /// assert_eq!(Integer::checked_pow(2, 200), None);
    /// ```
    fn checked_pow(self, exp: u32) -> Option<Self>;

    /// Saturating integer addition. Computes `self + rhs`, saturating at the numeric bounds instead of overflowing.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::saturating_add(10, 4), 14);
    /// assert_eq!(Integer::saturating_add(230u8, 200), 255);
    /// ```
    fn saturating_add(self, rhs: Self) -> Self;

    /// Saturating integer subtraction. Computes `self - rhs`, saturating at the numeric bounds instead of overflowing.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::saturating_sub(10, 4), 6);
    /// assert_eq!(Integer::saturating_sub(1u8, 200), 0);
    /// ```
    fn saturating_sub(self, rhs: Self) -> Self;

    /// Saturating integer multiplication. Computes `self * rhs`, saturating at the numeric bounds instead of overflowing.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::saturating_mul(2, 4), 8);
    /// assert_eq!(Integer::saturating_mul(2u8, 230), 255);
    /// ```
    fn saturating_mul(self, rhs: Self) -> Self;

    /// Saturating integer division. Computes `self / rhs`, saturating at the numeric bounds instead of overflowing.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::saturating_div(10, 2), 5);
    /// assert_eq!(Integer::saturating_div(-128i8, -1), 127);
    /// ```
    fn saturating_div(self, rhs: Self) -> Self;

    /// Saturating integer negation. Computes `-self`, saturating at the numeric bounds instead of overflowing.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::saturating_neg(10), -10);
    /// assert_eq!(Integer::saturating_neg(-128i8), 127);
    /// ```
    fn saturating_neg(self) -> Self;

    /// Saturating absolute value. Computes `self.abs()`, saturating at the numeric bounds instead of overflowing.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::saturating_abs(-10), 10);
    /// assert_eq!(Integer::saturating_abs(-128i8), 127);
    /// ```
    fn saturating_abs(self) -> Self;

    /// Saturating integer exponentiation. Computes `self.pow(exp)`, saturating at the numeric bounds instead of overflowing.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::saturating_pow(2, 4), 16);
    /// assert_eq!(Integer::saturating_pow(2u8, 200), 255);
    /// ```
    fn saturating_pow(self, exp: u32) -> Self;

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_add(10, 4), 14);
    /// assert_eq!(Integer::wrapping_add(250u8, 8), 2);
    /// ```
    fn wrapping_add(self, rhs: Self) -> Self;

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_sub(10, 4), 6);
    /// assert_eq!(Integer::wrapping_sub(4u8, 6), 254);
    /// ```
    fn wrapping_sub(self, rhs: Self) -> Self;

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_mul(2, 4), 8);
    /// assert_eq!(Integer::wrapping_mul(130u8, 2), 4);
    /// ```
    fn wrapping_mul(self, rhs: Self) -> Self;

    /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_div(10, 2), 5);
    /// assert_eq!(Integer::wrapping_div(-128i8, -1), -128);
    /// ```
    fn wrapping_div(self, rhs: Self) -> Self;

    /// Wrapping (modular) remainder. Computes `self % rhs`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_rem(10, 4), 2);
    /// assert_eq!(Integer::wrapping_rem(-128i8, -1), 0);
    /// ```
    fn wrapping_rem(self, rhs: Self) -> Self;

    /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_div_euclid(10, 4), 2);
    /// assert_eq!(Integer::wrapping_div_euclid(-128i8, -1), -128);
    /// ```
    fn wrapping_div_euclid(self, rhs: Self) -> Self;

    /// Wrapping Euclidean remainder. Computes `self.rem_euclid(rhs)`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_rem_euclid(10, 4), 2);
    /// assert_eq!(Integer::wrapping_rem_euclid(-128i8, -1), 0);
    /// ```
    fn wrapping_rem_euclid(self, rhs: Self) -> Self;

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where `mask` removes any high-order
    /// bits of rhs that would cause the shift to exceed the bitwidth of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_shl(-1i32, 7), -128);
    /// assert_eq!(Integer::wrapping_shl(-1i32, 128), -1);
    /// ```
    fn wrapping_shl(self, rhs: u32) -> Self;

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`, where `mask` removes any high-order
    /// bits of rhs that would cause the shift to exceed the bitwidth of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_shr(-128i32, 7), -1);
    /// assert_eq!(Integer::wrapping_shr(-128i32, 64), -128);
    /// ```
    fn wrapping_shr(self, rhs: u32) -> Self;

    /// Wrapping (modular) negation. Computes `-self`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_neg(10), -10);
    /// assert_eq!(Integer::wrapping_neg(-128i8), -128);
    /// ```
    fn wrapping_neg(self) -> Self;

    /// Wrapping (modular) absolute value. Computes `self.abs()`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_abs(-10), 10);
    /// assert_eq!(Integer::wrapping_abs(-128i8), -128);
    /// ```
    fn wrapping_abs(self) -> Self;

    /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`, wrapping around at the boundary of the type.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::wrapping_pow(2, 10), 1024);
    /// assert_eq!(Integer::wrapping_pow(3i8, 5), -13);
    /// ```
    fn wrapping_pow(self, exp: u32) -> Self;

    /// Calculates `self + rhs`
    ///
    /// Returns a tuple of the addition along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_add(10, 4), (14, false));
    /// assert_eq!(Integer::overflowing_add(-128i8, -1), (127, true));
    /// ```
    fn overflowing_add(self, rhs: Self) -> (Self, bool);
    
    /// Calculates `self - rhs`
    /// 
    /// Returns a tuple of the subtraction along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_sub(10, 4), (6, false));
    /// assert_eq!(Integer::overflowing_sub(-128i8, 1), (127, true));
    /// ```
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);

    /// Calculates the multiplication of `self` and `rhs`.
    /// 
    /// Returns a tuple of the multiplication along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would have occurred then the wrapped value is returned.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_mul(10, 4), (40, false));
    /// assert_eq!(Integer::overflowing_mul(-128i8, -1), (-128, true));
    /// ```
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);

    /// Calculates the divisor when `self` is divided by `rhs`.
    /// 
    /// Returns a tuple of the divisor along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would occur then `self` is returned.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_div(10, 4), (2, false));
    /// assert_eq!(Integer::overflowing_div(-128i8, -1), (-128, true));
    /// ```
    fn overflowing_div(self, rhs: Self) -> (Self, bool);

    /// Calculates the remainder when `self` is divided by `rhs`.
    /// 
    /// Returns a tuple of the remainder after dividing along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would occur then `0` is returned.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_rem(10, 4), (2, false));
    /// assert_eq!(Integer::overflowing_rem(-128i8, -1), (0, true));
    /// ```
    fn overflowing_rem(self, rhs: Self) -> (Self, bool);

    /// Calculates the quotient of Euclidean division `self.div_euclid(rhs)`.
    /// 
    /// Returns a tuple of the divisor along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would occur then `self` is returned.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_div_euclid(10, 4), (2, false));
    /// assert_eq!(Integer::overflowing_div_euclid(-128i8, -1), (-128, true));
    /// ```
    fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool);

    /// Overflowing Euclidean remainder. Calculates `self.rem_euclid(rhs)`.
    /// 
    /// Returns a tuple of the remainder after dividing along with a boolean indicating whether an arithmetic overflow would occur.
    /// If an overflow would occur then `0` is returned.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Panics
    /// 
    /// This function will panic if `rhs` is 0.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_rem_euclid(10, 4), (2, false));
    /// assert_eq!(Integer::overflowing_rem_euclid(-128i8, -1), (0, true));
    /// ```
    fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool);

    /// Shifts `self` left by `rhs` bits.
    /// 
    /// Returns a tuple of the shifted version of `self` along with a boolean indicating whether the shift value was larger than or equal to the number of bits.
    /// If the shift value is too large, then value is masked `(N-1)` where `N` is the number of bits, and this value is then used to perform the shift.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_shl(0x10, 4), (0x100, false));
    /// assert_eq!(Integer::overflowing_shl(0x1i32, 36), (0x10, true));
    /// ```
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);

    /// Shifts `self` right by `rhs` bits.
    /// 
    /// Returns a tuple of the shifted version of `self` along with a boolean indicating whether the shift value was larger than or equal to the number of bits.
    /// If the shift value is too large, then value is masked `(N-1)` where `N` is the number of bits, and this value is then used to perform the shift.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_shr(0x10, 4), (0x1, false));
    /// assert_eq!(Integer::overflowing_shr(0x10i32, 36), (0x1, true));
    /// ```
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);

    /// Negates `self`, overflowing if this is equal to the minimum value.
    /// 
    /// Returns a tuple of the negated version of self along with a boolean indicating whether an overflow happened.
    /// If `self` is the minimum value, then the minimum value will be returned again and `true` will be returned for an overflow happening.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_neg(2), (-2, false));
    /// assert_eq!(Integer::overflowing_neg(-128i8), (-128, true));
    /// ```
    fn overflowing_neg(self) -> (Self, bool);

    /// Computes the absolute value of `self`.
    /// 
    /// Returns a tuple of the absolute version of `self` along with a boolean indicating whether an overflow happened.
    /// If `self` is the minimum value, then the minimum value will be returned again and `true` will be returned for an overflow happening.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_abs(-2), (2, false));
    /// assert_eq!(Integer::overflowing_abs(-128i8), (-128, true));
    /// ```
    fn overflowing_abs(self) -> (Self, bool);

    /// Raises `self` to the power of `exp`, using exponentiation by squaring.
    ///
    /// Returns a tuple of the exponentiation along with a bool indicating whether an overflow happened.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::overflowing_pow(3, 4), (81, false));
    /// assert_eq!(Integer::overflowing_pow(3i8, 5), (-13, true));
    /// ```
    fn overflowing_pow(self, exp: u32) -> (Self, bool);

    /// Raises `self` to the power of `exp`, using exponentiation by squaring.
    /// 
    /// More information in [primitives documentation](https://doc.rust-lang.org/std/#primitives).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Integer;
    /// 
    /// assert_eq!(Integer::pow(3, 4), 81);
    /// ```
    fn pow(self, exp: u32) -> Self;
}

/// An unsigned integer.
pub trait UnsignedInteger: Integer + Unsigned {
    /// Returns true if and only if self == 2^k for some k.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::UnsignedInteger;
    /// 
    /// assert_eq!(UnsignedInteger::is_power_of_two(16u8), true);
    /// assert_eq!(UnsignedInteger::is_power_of_two(10u8), false);
    /// ```
    fn is_power_of_two(self) -> bool;

    /// Returns the smallest power of two greater than or equal to `self`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::UnsignedInteger;
    /// 
    /// assert_eq!(UnsignedInteger::next_power_of_two(10u8), 16);
    /// assert_eq!(UnsignedInteger::next_power_of_two(26u8), 32);
    /// ```
    fn next_power_of_two(self) -> Self;

    /// Returns the smallest power of two greater than or equal to `n`. If the next power of two is greater than the type’s maximum value,
    /// `None` is returned, otherwise the power of two is wrapped in `Some`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::UnsignedInteger;
    /// 
    /// assert_eq!(UnsignedInteger::checked_next_power_of_two(10u8), Some(16));
    /// assert_eq!(UnsignedInteger::checked_next_power_of_two(255u8), None);
    /// ```
    fn checked_next_power_of_two(self) -> Option<Self>;
}

/// A signed integer.
pub trait SignedInteger: Integer + Signed {}

/// A floating point number.
pub trait Float: Number {
    /// The radix or base of the internal representation of f32.
    const RADIX: u32;

    /// Number of significant digits in base 2.
    const MANTISSA_DIGITS: u32;

    /// Approximate number of significant digits in base 10.
    const DIGITS: u32;

    /// [Machine epsilon](https://en.wikipedia.org/wiki/Machine_epsilon) value for f32.
    /// 
    /// This is the difference between `1.0` and the next larger representable number.
    const EPSILON: Self;

    /// Smallest positive normal value.
    const MIN_POSITIVE: Self;

    /// One greater than the minimum possible normal power of 2 exponent.
    const MIN_EXP: i32;

    /// Maximum possible power of 2 exponent.
    const MAX_EXP: i32;

    /// Minimum possible normal power of 10 exponent.
    const MIN_10_EXP: i32;

    /// Maximum possible power of 10 exponent.
    const MAX_10_EXP: i32;

    /// Not a Number (NaN).
    const NAN: Self;
    
    /// Infinity (∞).
    const INFINITY: Self;

    /// Negative infinity (−∞).
    const NEG_INFINITY: Self;

    /// Archimedes' constant (π)
    const PI: Self;

    /// The full circle constant (τ)
    ///
    /// Equal to 2π.
    const TAU: Self;

    /// π/2
    const FRAC_PI_2: Self;

    /// π/3
    const FRAC_PI_3: Self;

    /// π/4
    const FRAC_PI_4: Self;

    /// π/6
    const FRAC_PI_6: Self;

    /// π/8
    const FRAC_PI_8: Self;

    /// 1/π
    const FRAC_1_PI: Self;

    /// 2/π
    const FRAC_2_PI: Self;

    /// 2/sqrt(π)
    const FRAC_2_SQRT_PI: Self;

    /// sqrt(2)
    const SQRT_2: Self;

    /// 1/sqrt(2)
    const FRAC_1_SQRT_2: Self;

    /// Euler's number (e)
    const E: Self;

    /// log<sub>2</sub>(e)
    const LOG2_E: Self;

    /// log<sub>2</sub>(10)
    const LOG2_10: Self;

    /// log<sub>10</sub>(e)
    const LOG10_E: Self;

    /// log<sub>10</sub>(2)
    const LOG10_2: Self;

    /// ln(2)
    const LN_2: Self;

    /// ln(10)
    const LN_10: Self;

    /// Returns `true` if this value is `NaN`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::is_nan(2.0), false);
    /// assert_eq!(Float::is_nan(f32::NAN), true);
    /// ```
    fn is_nan(self) -> bool;

    /// Returns `true` if this value is positive infinity or negative infinity, and `false` otherwise.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::is_infinite(2.0), false);
    /// assert_eq!(Float::is_infinite(f32::INFINITY), true);
    /// assert_eq!(Float::is_infinite(f32::NEG_INFINITY), true);
    /// ```
    fn is_infinite(self) -> bool;

    /// Returns `true` if this value is neither infinite nor `NaN`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::is_finite(2.0), true);
    /// assert_eq!(Float::is_finite(f32::INFINITY), false);
    /// assert_eq!(Float::is_finite(f32::NEG_INFINITY), false);
    /// assert_eq!(Float::is_finite(f32::NAN), false);
    /// ```
    fn is_finite(self) -> bool;

    /// Returns `true` if the number is [subnormal](https://en.wikipedia.org/wiki/Denormal_number).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::is_subnormal(2.0), false);
    /// assert_eq!(Float::is_subnormal(1.0e-40_f32), true);
    /// ```
    fn is_subnormal(self) -> bool;

    /// Returns `true` if the number is neither zero, infinite, [subnormal](https://en.wikipedia.org/wiki/Denormal_number), or `NaN`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::is_normal(2.0), true);
    /// assert_eq!(Float::is_normal(1.0e-40_f32), false);
    /// assert_eq!(Float::is_normal(f32::NAN), false);
    /// assert_eq!(Float::is_normal(f32::INFINITY), false);
    /// ```
    fn is_normal(self) -> bool;

    /// Returns `true` if `self` has a positive sign, including `+0.0`, `NaN`s with positive sign bit and positive infinity.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::is_sign_positive(2.0), true);
    /// assert_eq!(Float::is_sign_positive(f32::NAN), true);
    /// assert_eq!(Float::is_sign_positive(f32::INFINITY), true);
    /// assert_eq!(Float::is_sign_positive(f32::NEG_INFINITY), false);
    /// ```
    fn is_sign_positive(self) -> bool;

    /// Returns `true` if `self` has a negative sign, including `-0.0`, `NaN`s with negative sign bit and negative infinity.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::is_sign_negative(2.0), false);
    /// assert_eq!(Float::is_sign_negative(f32::NAN), false);
    /// assert_eq!(Float::is_sign_negative(f32::INFINITY), false);
    /// assert_eq!(Float::is_sign_negative(f32::NEG_INFINITY), true);
    /// ```
    fn is_sign_negative(self) -> bool;

    /// Returns the floating point category of the number. If only one property is going to be tested, it is generally faster to use the specific predicate instead.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// use core::num::FpCategory;
    /// 
    /// assert_eq!(Float::classify(2.0), FpCategory::Normal);
    /// assert_eq!(Float::classify(f32::NAN), FpCategory::Nan);
    /// assert_eq!(Float::classify(f32::INFINITY), FpCategory::Infinite);
    /// assert_eq!(Float::classify(f32::NEG_INFINITY), FpCategory::Infinite);
    /// ```
    fn classify(self) -> FpCategory;

    /// Takes the reciprocal (inverse) of a number, `1/x`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::recip(2.0), 0.5);
    /// assert!(Float::is_nan(Float::recip(f32::NAN)));
    /// ```
    fn recip(self) -> Self;

    /// Converts radians to degrees.
    fn to_degrees(self) -> Self;

    /// Converts degrees to radians.
    fn to_radians(self) -> Self;

    /// Returns a number that represents the sign of self.
    ///
    /// - `1.0` if the number is positive, `+0.0` or `INFINITY`
    /// - `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
    /// - `NAN` if the number is `NAN`
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::float_signum(2.0), 1.0);
    /// assert_eq!(Float::float_signum(0.0), 1.0);
    /// assert_eq!(Float::float_signum(-0.0), -1.0);
    /// assert!(Float::is_nan(Float::float_signum(f32::NAN)));
    /// ```
    fn float_signum(self) -> Self;

    /// Returns the largest integer less than or equal to a number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::floor(2.8), 2.0);
    /// assert_eq!(Float::floor(3.3), 3.0);
    /// ```
    fn floor(self) -> Self;

    /// Returns the smallest integer greater than or equal to a number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::ceil(2.8), 3.0);
    /// assert_eq!(Float::ceil(3.3), 4.0);
    /// ```
    fn ceil(self) -> Self;

    /// Returns the nearest integer to a number. Round half-way cases away from `0.0`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::round(2.8), 3.0);
    /// assert_eq!(Float::round(3.3), 3.0);
    /// assert_eq!(Float::round(1.5), 2.0);
    /// ```
    fn round(self) -> Self;

    /// Returns the integer part of a number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::trunc(2.8), 2.0);
    /// assert_eq!(Float::trunc(-3.3), -3.0);
    /// ```
    fn trunc(self) -> Self;

    /// Returns the fractional part of a number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::fract(2.5), 0.5);
    /// ```
    fn fract(self) -> Self;

    /// Returns a number composed of the magnitude of self and the sign of sign.
    ///
    /// Equal to `self` if the sign of `self` and sign are the same, otherwise equal to `-self`. If `self` is a `NAN`,
    /// then a `NAN` with the sign of sign is returned.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::copysign(2.0, 1.0), 2.0);
    /// assert_eq!(Float::copysign(2.0, -32.0), -2.0);
    /// ```
    fn copysign(self, sign: Self) -> Self;

    /// Fused multiply-add. Computes `(self * a) + b` with only one rounding error, yielding a more accurate result than an unfused multiply-add.
    ///
    /// Using `mul_add` may be more performant than an unfused multiply-add if the target architecture has a dedicated `fma` CPU instruction.
    /// However, this is not always true, and will be heavily dependant on designing algorithms with specific target hardware in mind.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::mul_add(2.0, 3.0, 4.0), 10.0);
    /// ```
    #[cfg(feature = "std")] fn mul_add(self, a: Self, b: Self) -> Self;

    /// Raises a number to an integer power.
    ///
    /// Using this function is generally faster than using `powf`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::powi(2.0, 3), 8.0);
    /// assert_eq!(Float::powi(2.0, -3), 0.125);
    /// ```
    #[cfg(feature = "std")] fn powi(self, n: i32) -> Self;

    /// Raises a number to a floating point power.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::powf(2.0, 1.5), 2.8284271247461903);
    /// assert_eq!(Float::powf(2.0, -3.0), 0.125);
    /// ```
    #[cfg(feature = "std")] fn powf(self, n: Self) -> Self;

    /// Returns the square root of a number.
    /// 
    /// Returns `NaN` if `self` is a negative number other than `-0.0`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::sqrt(25.0), 5.0);
    /// assert!(Float::is_nan(Float::sqrt(-25.0)));
    /// ```
    #[cfg(feature = "std")] fn sqrt(self) -> Self;

    /// Returns the cube root of a number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::cbrt(8.0), 2.0);
    /// ```
    #[cfg(feature = "std")] fn cbrt(self) -> Self;

    /// Returns `e^(self)`, (the exponential function).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::exp(1.0), 2.718281828459045);
    /// ``` 
    #[cfg(feature = "std")] fn exp(self) -> Self;

    /// Returns `2^(self)`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::exp2(3.0), 8.0);
    /// ```
    #[cfg(feature = "std")] fn exp2(self) -> Self;

    /// Returns `e^(self) - 1` in a way that is accurate even if the number is close to zero.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::exp_m1(1.0), 1.718281828459045);
    /// assert_eq!(Float::exp_m1(0.0), 0.0);
    /// ```
    #[cfg(feature = "std")] fn exp_m1(self) -> Self;

    /// Returns `ln(1+n)` (natural logarithm) more accurately than if the operations were performed separately.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::ln_1p(0.5), 0.4054651081081644);
    /// assert_eq!(Float::ln_1p(-0.5), -0.6931471805599453);
    /// ```
    #[cfg(feature = "std")] fn ln_1p(self) -> Self;

    /// Returns the natural logarithm of the number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::ln(2.0), 0.6931471805599453);
    /// ```
    #[cfg(feature = "std")] fn ln(self) -> Self;

    /// Returns the logarithm of the number with respect to an arbitrary base.
    ///
    /// The result might not be correctly rounded owing to implementation details; `self.log2()` can produce more
    /// accurate results for base 2, and `self.log10()` can produce more accurate results for base 10.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::log(2.0, 10.0), 0.30102999566398114);
    /// ```
    #[cfg(feature = "std")] fn log(self, base: Self) -> Self;

    /// Returns the base 2 logarithm of the number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::log2(2.0), 1.0);
    /// assert_eq!(Float::log2(1.0), 0.0);
    /// ```
    #[cfg(feature = "std")] fn log2(self) -> Self;

    /// Returns the base 10 logarithm of the number.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::log10(100.0), 2.0);
    /// assert_eq!(Float::log10(1.0), 0.0);
    /// ```
    #[cfg(feature = "std")] fn log10(self) -> Self;

    /// Calculates the length of the hypotenuse of a right-angle triangle given legs of length `x` and `y`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::hypot(3.0, 4.0), 5.0);
    /// assert_eq!(Float::hypot(5.0, 12.0), 13.0);
    /// ```
    #[cfg(feature = "std")] fn hypot(self, other: Self) -> Self;

    /// Computes the sine of a number (in radians).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::sin(2.0), 0.9092974268256817);
    /// ```
    #[cfg(feature = "std")] fn sin(self) -> Self;

    /// Computes the cosine of a number (in radians).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::cos(2.0), -0.4161468365471424);
    /// ```
    #[cfg(feature = "std")] fn cos(self) -> Self;

    /// Computes the tangent of a number (in radians).
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::tan(2.0), -2.185039863261519);
    /// ```
    #[cfg(feature = "std")] fn tan(self) -> Self;

    /// Computes the arcsine of a number. Return value is in radians in the range [-pi/2, pi/2] or NaN if the number is outside the range [-1, 1].
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::asin(0.5), 0.5235987755982989);
    /// ```
    #[cfg(feature = "std")] fn asin(self) -> Self;

    /// Computes the arccosine of a number. Return value is in radians in the range [0, pi] or NaN if the number is outside the range [-1, 1].
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::acos(0.5), 1.0471975511965979);
    /// ```
    #[cfg(feature = "std")] fn acos(self) -> Self;

    /// Computes the arctangent of a number. Return value is in radians in the range [-pi/2, pi/2];
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::atan(1.0), 0.7853981633974483);
    /// ```
    #[cfg(feature = "std")] fn atan(self) -> Self;

    /// Computes the four quadrant arctangent of self (y) and other (x) in radians.
    ///
    /// - `x = 0`, `y = 0`: `0`
    /// - `x >= 0`: `arctan(y/x)` -> [-pi/2, pi/2]
    /// - `y >= 0`: `arctan(y/x) + pi` -> (pi/2, pi]
    /// - `y < 0`: `arctan(y/x) - pi` -> (-pi, -pi/2)
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::atan2(0.0, 1.0), 0.0);
    /// assert_eq!(Float::atan2(1.0, 1.0), 0.7853981633974483);
    /// ```
    #[cfg(feature = "std")] fn atan2(self, other: Self) -> Self;

    /// Simultaneously computes the sine and cosine of the number, `x`. Returns `(sin(x), cos(x))`.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::sin_cos(2.0), (0.9092974268256817, -0.4161468365471424));
    /// ```
    #[cfg(feature = "std")] fn sin_cos(self) -> (Self, Self);

    /// Hyperbolic sine function.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::sinh(2.0), 3.6268604078470186);
    /// ```
    #[cfg(feature = "std")] fn sinh(self) -> Self;

    /// Hyperbolic cosine function.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::cosh(2.0), 3.7621956910836314);
    /// ```
    #[cfg(feature = "std")] fn cosh(self) -> Self;

    /// Hyperbolic tangent function.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::tanh(2.0), 0.9640275800758169);
    /// ```
    #[cfg(feature = "std")] fn tanh(self) -> Self;

    /// Inverse hyperbolic sine function.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::asinh(2.0), 1.4436354751788103);
    /// ```
    #[cfg(feature = "std")] fn asinh(self) -> Self;

    /// Inverse hyperbolic cosine function.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::acosh(2.0), 1.3169578969248166);
    /// ```
    #[cfg(feature = "std")] fn acosh(self) -> Self;

    /// Inverse hyperbolic tangent function.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use rutil::number_traits::Float;
    /// 
    /// assert_eq!(Float::atanh(0.45), 0.48470027859405174);
    /// ```
    #[cfg(feature = "std")] fn atanh(self) -> Self;
}

/// Implements unsigned integers.
macro_rules! impl_unsigned {
    ($($t:ty),*) => {$(
        impl Number for $t {
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
            const BITS: u32 = Self::BITS;
            const ZERO: Self = 0;
            const ONE: Self = 1;

            #[inline] fn div_euclid(self, rhs: Self) -> Self { self.div_euclid(rhs) }
            #[inline] fn rem_euclid(self, rhs: Self) -> Self { self.rem_euclid(rhs) }
            #[inline] fn abs(self) -> Self { self }
            #[inline] fn abs_diff(self, other: Self) -> Self { self.abs_diff(other) }
            #[inline] fn signum(self) -> Self { if self == 0 { 0 } else { 1 } }
            #[inline] fn is_positive(self) -> bool { self != 0 }
            #[inline] fn is_negative(self) -> bool { false }
            #[inline] fn max(self, other: Self) -> Self { Ord::max(self, other) }
            #[inline] fn min(self, other: Self) -> Self { Ord::min(self, other) }
            #[inline] fn clamp(self, min: Self, max: Self) -> Self { Ord::clamp(self, min, max) }
        }

        impl Unsigned for $t {}

        impl Integer for $t {
            #[inline] fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> { Self::from_str_radix(src, radix) }

            #[inline] fn count_ones(self) -> u32 { self.count_ones() }
            #[inline] fn count_zeros(self) -> u32 { self.count_zeros() }
            #[inline] fn leading_zeros(self) -> u32 { self.leading_zeros() }
            #[inline] fn trailing_zeros(self) -> u32 { self.trailing_zeros() }
            #[inline] fn leading_ones(self) -> u32 { self.leading_ones() }
            #[inline] fn trailing_ones(self) -> u32 { self.trailing_ones() }
            #[inline] fn rotate_left(self, n: u32) -> Self { self.rotate_left(n) }
            #[inline] fn rotate_right(self, n: u32) -> Self { self.rotate_right(n) }
            #[inline] fn swap_bytes(self) -> Self { self.swap_bytes() }
            #[inline] fn reverse_bits(self) -> Self { self.reverse_bits() }
        
            #[inline] fn from_be(x: Self) -> Self { Self::from_be(x) }
            #[inline] fn from_le(x: Self) -> Self { Self::from_le(x) }
            #[inline] fn to_be(self) -> Self { Self::to_be(self) }
            #[inline] fn to_le(self) -> Self { Self::to_le(self) }
        
            #[inline] fn checked_add(self, rhs: Self) -> Option<Self> { self.checked_add(rhs) }
            #[inline] fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }
            #[inline] fn checked_mul(self, rhs: Self) -> Option<Self> { self.checked_mul(rhs) }
            #[inline] fn checked_div(self, rhs: Self) -> Option<Self> { self.checked_div(rhs) }
            #[inline] fn checked_rem(self, rhs: Self) -> Option<Self> { self.checked_rem(rhs) }
            #[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { self.checked_div_euclid(rhs) }
            #[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { self.checked_rem_euclid(rhs) }
            #[inline] fn checked_shl(self, rhs: u32) -> Option<Self> { self.checked_shl(rhs) }
            #[inline] fn checked_shr(self, rhs: u32) -> Option<Self> { self.checked_shr(rhs) }
            #[inline] fn checked_neg(self) -> Option<Self> { self.checked_neg() }
            #[inline] fn checked_abs(self) -> Option<Self> { Some(self) }
            #[inline] fn checked_pow(self, exp: u32) -> Option<Self> { self.checked_pow(exp) }
        
            #[inline] fn saturating_add(self, rhs: Self) -> Self { self.saturating_add(rhs) }
            #[inline] fn saturating_sub(self, rhs: Self) -> Self { self.saturating_sub(rhs) }
            #[inline] fn saturating_mul(self, rhs: Self) -> Self { self.saturating_mul(rhs) }
            #[inline] fn saturating_div(self, rhs: Self) -> Self { self.saturating_div(rhs) }
            #[inline] fn saturating_neg(self) -> Self { 0 }
            #[inline] fn saturating_abs(self) -> Self { self }
            #[inline] fn saturating_pow(self, exp: u32) -> Self { self.saturating_pow(exp) }
        
            #[inline] fn wrapping_add(self, rhs: Self) -> Self { self.wrapping_add(rhs) }
            #[inline] fn wrapping_sub(self, rhs: Self) -> Self { self.wrapping_sub(rhs) }
            #[inline] fn wrapping_mul(self, rhs: Self) -> Self { self.wrapping_mul(rhs) }
            #[inline] fn wrapping_div(self, rhs: Self) -> Self { self.wrapping_div(rhs) }
            #[inline] fn wrapping_rem(self, rhs: Self) -> Self { self.wrapping_rem(rhs) }
            #[inline] fn wrapping_div_euclid(self, rhs: Self) -> Self { self.wrapping_div_euclid(rhs) }
            #[inline] fn wrapping_rem_euclid(self, rhs: Self) -> Self { self.wrapping_rem_euclid(rhs) }
            #[inline] fn wrapping_shl(self, rhs: u32) -> Self { self.wrapping_shl(rhs) }
            #[inline] fn wrapping_shr(self, rhs: u32) -> Self { self.wrapping_shr(rhs) }
            #[inline] fn wrapping_neg(self) -> Self { self.wrapping_neg() }
            #[inline] fn wrapping_abs(self) -> Self { self }
            #[inline] fn wrapping_pow(self, exp: u32) -> Self { self.wrapping_pow(exp) }
        
            #[inline] fn overflowing_add(self, rhs: Self) -> (Self, bool) { self.overflowing_add(rhs) }
            #[inline] fn overflowing_sub(self, rhs: Self) -> (Self, bool) { self.overflowing_sub(rhs) }
            #[inline] fn overflowing_mul(self, rhs: Self) -> (Self, bool) { self.overflowing_mul(rhs) }
            #[inline] fn overflowing_div(self, rhs: Self) -> (Self, bool) { self.overflowing_div(rhs) }
            #[inline] fn overflowing_rem(self, rhs: Self) -> (Self, bool) { self.overflowing_rem(rhs) }
            #[inline] fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) { self.overflowing_div_euclid(rhs) }
            #[inline] fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) { self.overflowing_rem_euclid(rhs) }
            #[inline] fn overflowing_shl(self, rhs: u32) -> (Self, bool) { self.overflowing_shl(rhs) }
            #[inline] fn overflowing_shr(self, rhs: u32) -> (Self, bool) { self.overflowing_shr(rhs) }
            #[inline] fn overflowing_neg(self) -> (Self, bool) { self.overflowing_neg() }
            #[inline] fn overflowing_abs(self) -> (Self, bool) { (self, false) }
            #[inline] fn overflowing_pow(self, exp: u32) -> (Self, bool) { self.overflowing_pow(exp) }
        
            #[inline] fn pow(self, exp: u32) -> Self { self.pow(exp) }
        }

        impl UnsignedInteger for $t {
            #[inline] fn is_power_of_two(self) -> bool { self.is_power_of_two() }
            #[inline] fn next_power_of_two(self) -> Self { self.next_power_of_two() }
            #[inline] fn checked_next_power_of_two(self) -> Option<Self> { self.checked_next_power_of_two() }
        }
    )*};
}

impl_unsigned!(u8, u16, u32, u64, u128, usize);

/// Implements signed integers.
macro_rules! impl_signed {
    ($($t:ty),*) => {$(
        impl Number for $t {
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
            const BITS: u32 = Self::BITS;
            const ZERO: Self = 0;
            const ONE: Self = 1;

            #[inline] fn div_euclid(self, rhs: Self) -> Self { self.div_euclid(rhs) }
            #[inline] fn rem_euclid(self, rhs: Self) -> Self { self.rem_euclid(rhs) }
            #[inline] fn abs(self) -> Self { self.abs() }
            #[inline] fn abs_diff(self, other: Self) -> Self { if self < other { other - self } else { self - other } }
            #[inline] fn signum(self) -> Self { self.signum() }
            #[inline] fn is_positive(self) -> bool { self.is_positive() }
            #[inline] fn is_negative(self) -> bool { self.is_negative() }
            #[inline] fn max(self, other: Self) -> Self { Ord::max(self, other) }
            #[inline] fn min(self, other: Self) -> Self { Ord::min(self, other) }
            #[inline] fn clamp(self, min: Self, max: Self) -> Self { Ord::clamp(self, min, max) }
        }

        impl Signed for $t {}

        impl Integer for $t {
            #[inline] fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> { Self::from_str_radix(src, radix) }

            #[inline] fn count_ones(self) -> u32 { self.count_ones() }
            #[inline] fn count_zeros(self) -> u32 { self.count_zeros() }
            #[inline] fn leading_zeros(self) -> u32 { self.leading_zeros() }
            #[inline] fn trailing_zeros(self) -> u32 { self.trailing_zeros() }
            #[inline] fn leading_ones(self) -> u32 { self.leading_ones() }
            #[inline] fn trailing_ones(self) -> u32 { self.trailing_ones() }
            #[inline] fn rotate_left(self, n: u32) -> Self { self.rotate_left(n) }
            #[inline] fn rotate_right(self, n: u32) -> Self { self.rotate_right(n) }
            #[inline] fn swap_bytes(self) -> Self { self.swap_bytes() }
            #[inline] fn reverse_bits(self) -> Self { self.reverse_bits() }
        
            #[inline] fn from_be(x: Self) -> Self { Self::from_be(x) }
            #[inline] fn from_le(x: Self) -> Self { Self::from_le(x) }
            #[inline] fn to_be(self) -> Self { Self::to_be(self) }
            #[inline] fn to_le(self) -> Self { Self::to_le(self) }
        
            #[inline] fn checked_add(self, rhs: Self) -> Option<Self> { self.checked_add(rhs) }
            #[inline] fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }
            #[inline] fn checked_mul(self, rhs: Self) -> Option<Self> { self.checked_mul(rhs) }
            #[inline] fn checked_div(self, rhs: Self) -> Option<Self> { self.checked_div(rhs) }
            #[inline] fn checked_rem(self, rhs: Self) -> Option<Self> { self.checked_rem(rhs) }
            #[inline] fn checked_div_euclid(self, rhs: Self) -> Option<Self> { self.checked_div_euclid(rhs) }
            #[inline] fn checked_rem_euclid(self, rhs: Self) -> Option<Self> { self.checked_rem_euclid(rhs) }
            #[inline] fn checked_shl(self, rhs: u32) -> Option<Self> { self.checked_shl(rhs) }
            #[inline] fn checked_shr(self, rhs: u32) -> Option<Self> { self.checked_shr(rhs) }
            #[inline] fn checked_neg(self) -> Option<Self> { self.checked_neg() }
            #[inline] fn checked_abs(self) -> Option<Self> { self.checked_abs() }
            #[inline] fn checked_pow(self, exp: u32) -> Option<Self> { self.checked_pow(exp) }
        
            #[inline] fn saturating_add(self, rhs: Self) -> Self { self.saturating_add(rhs) }
            #[inline] fn saturating_sub(self, rhs: Self) -> Self { self.saturating_sub(rhs) }
            #[inline] fn saturating_mul(self, rhs: Self) -> Self { self.saturating_mul(rhs) }
            #[inline] fn saturating_div(self, rhs: Self) -> Self { self.saturating_div(rhs) }
            #[inline] fn saturating_neg(self) -> Self { self.saturating_neg() }
            #[inline] fn saturating_abs(self) -> Self { self.saturating_abs() }
            #[inline] fn saturating_pow(self, exp: u32) -> Self { self.saturating_pow(exp) }
        
            #[inline] fn wrapping_add(self, rhs: Self) -> Self { self.wrapping_add(rhs) }
            #[inline] fn wrapping_sub(self, rhs: Self) -> Self { self.wrapping_sub(rhs) }
            #[inline] fn wrapping_mul(self, rhs: Self) -> Self { self.wrapping_mul(rhs) }
            #[inline] fn wrapping_div(self, rhs: Self) -> Self { self.wrapping_div(rhs) }
            #[inline] fn wrapping_rem(self, rhs: Self) -> Self { self.wrapping_rem(rhs) }
            #[inline] fn wrapping_div_euclid(self, rhs: Self) -> Self { self.wrapping_div_euclid(rhs) }
            #[inline] fn wrapping_rem_euclid(self, rhs: Self) -> Self { self.wrapping_rem_euclid(rhs) }
            #[inline] fn wrapping_shl(self, rhs: u32) -> Self { self.wrapping_shl(rhs) }
            #[inline] fn wrapping_shr(self, rhs: u32) -> Self { self.wrapping_shr(rhs) }
            #[inline] fn wrapping_neg(self) -> Self { self.wrapping_neg() }
            #[inline] fn wrapping_abs(self) -> Self { self.wrapping_abs() }
            #[inline] fn wrapping_pow(self, exp: u32) -> Self { self.wrapping_pow(exp) }
        
            #[inline] fn overflowing_add(self, rhs: Self) -> (Self, bool) { self.overflowing_add(rhs) }
            #[inline] fn overflowing_sub(self, rhs: Self) -> (Self, bool) { self.overflowing_sub(rhs) }
            #[inline] fn overflowing_mul(self, rhs: Self) -> (Self, bool) { self.overflowing_mul(rhs) }
            #[inline] fn overflowing_div(self, rhs: Self) -> (Self, bool) { self.overflowing_div(rhs) }
            #[inline] fn overflowing_rem(self, rhs: Self) -> (Self, bool) { self.overflowing_rem(rhs) }
            #[inline] fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) { self.overflowing_div_euclid(rhs) }
            #[inline] fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) { self.overflowing_rem_euclid(rhs) }
            #[inline] fn overflowing_shl(self, rhs: u32) -> (Self, bool) { self.overflowing_shl(rhs) }
            #[inline] fn overflowing_shr(self, rhs: u32) -> (Self, bool) { self.overflowing_shr(rhs) }
            #[inline] fn overflowing_neg(self) -> (Self, bool) { self.overflowing_neg() }
            #[inline] fn overflowing_abs(self) -> (Self, bool) { self.overflowing_abs() }
            #[inline] fn overflowing_pow(self, exp: u32) -> (Self, bool) { self.overflowing_pow(exp) }
        
            #[inline] fn pow(self, exp: u32) -> Self { self.pow(exp) }
        }

        impl SignedInteger for $t {}
    )*};
}

impl_signed!(i8, i16, i32, i64, i128, isize);

/// Implements floats.
#[cfg(feature = "std")]
macro_rules! impl_float {
    ($($t:ty[$n:ident]: $s:expr),*) => {$(
        impl Number for $t {
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
            const BITS: u32 = $s;
            const ZERO: Self = 0.0;
            const ONE: Self = 1.0;

            #[inline] fn div_euclid(self, rhs: Self) -> Self { self.div_euclid(rhs) }
            #[inline] fn rem_euclid(self, rhs: Self) -> Self { self.rem_euclid(rhs) }
            #[inline] fn abs(self) -> Self { self.abs() }
            #[inline] fn abs_diff(self, other: Self) -> Self { if self < other { other - self } else { self - other } }
            #[inline] fn signum(self) -> Self { self.signum() }
            #[inline] fn is_positive(self) -> bool { self.is_sign_positive() && self != 0.0 }
            #[inline] fn is_negative(self) -> bool { self.is_sign_negative() && self != 0.0 }
            #[inline] fn max(self, other: Self) -> Self { self.max(other) }
            #[inline] fn min(self, other: Self) -> Self { self.min(other) }
            #[inline] fn clamp(self, min: Self, max: Self) -> Self { self.clamp(min, max) }
        }

        impl Signed for $t {}

        impl Float for $t {
            const RADIX: u32 = Self::RADIX;
            const MANTISSA_DIGITS: u32 = Self::MANTISSA_DIGITS;
            const DIGITS: u32 = Self::DIGITS;
            const EPSILON: Self = Self::EPSILON;
            const MIN_POSITIVE: Self = Self::MIN_POSITIVE;
            const MIN_EXP: i32 = Self::MIN_EXP;
            const MAX_EXP: i32 = Self::MAX_EXP;
            const MIN_10_EXP: i32 = Self::MIN_10_EXP;
            const MAX_10_EXP: i32 = Self::MAX_10_EXP;
            const NAN: Self = Self::NAN;
            const INFINITY: Self = Self::INFINITY;
            const NEG_INFINITY: Self = Self::NEG_INFINITY;
            
            const PI: Self = core::$n::consts::PI;
            const TAU: Self = core::$n::consts::TAU;
            const FRAC_PI_2: Self = core::$n::consts::FRAC_PI_2;
            const FRAC_PI_3: Self = core::$n::consts::FRAC_PI_3;
            const FRAC_PI_4: Self = core::$n::consts::FRAC_PI_4;
            const FRAC_PI_6: Self = core::$n::consts::FRAC_PI_6;
            const FRAC_PI_8: Self = core::$n::consts::FRAC_PI_8;
            const FRAC_1_PI: Self = core::$n::consts::FRAC_1_PI;
            const FRAC_2_PI: Self = core::$n::consts::FRAC_2_PI;
            const FRAC_2_SQRT_PI: Self = core::$n::consts::FRAC_2_SQRT_PI;
            const SQRT_2: Self = core::$n::consts::SQRT_2;
            const FRAC_1_SQRT_2: Self = core::$n::consts::FRAC_1_SQRT_2;
            const E: Self = core::$n::consts::E;
            const LOG2_E: Self = core::$n::consts::LOG2_E;
            const LOG2_10: Self = core::$n::consts::LOG2_10;
            const LOG10_E: Self = core::$n::consts::LOG10_E;
            const LOG10_2: Self = core::$n::consts::LOG10_2;
            const LN_2: Self = core::$n::consts::LN_2;
            const LN_10: Self = core::$n::consts::LN_10;

            #[inline] fn is_nan(self) -> bool { self.is_nan() }
            #[inline] fn is_infinite(self) -> bool { self.is_infinite() }
            #[inline] fn is_finite(self) -> bool { self.is_finite() }
            #[inline] fn is_subnormal(self) -> bool { self.is_subnormal() }
            #[inline] fn is_normal(self) -> bool { self.is_normal() }
            #[inline] fn is_sign_positive(self) -> bool { self.is_sign_positive() }
            #[inline] fn is_sign_negative(self) -> bool { self.is_sign_negative() }
            #[inline] fn classify(self) -> FpCategory { self.classify() }
            #[inline] fn recip(self) -> Self { self.recip() }
            #[inline] fn to_degrees(self) -> Self { self.to_degrees() }
            #[inline] fn to_radians(self) -> Self { self.to_radians() }
            #[inline] fn float_signum(self) -> Self { self.signum() }

            #[inline] fn floor(self) -> Self { self.floor() }
            #[inline] fn ceil(self) -> Self { self.ceil() }
            #[inline] fn round(self) -> Self { self.round() }
            #[inline] fn trunc(self) -> Self { self.trunc() }
            #[inline] fn fract(self) -> Self { self.fract() }
            
            #[inline] fn copysign(self, other: Self) -> Self { self.copysign(other) }
            
            #[inline] fn mul_add(self, a: Self, b: Self) -> Self { self.mul_add(a, b) }
            #[inline] fn powi(self, n: i32) -> Self { self.powi(n) }
            #[inline] fn powf(self, n: Self) -> Self { self.powf(n) }
            #[inline] fn sqrt(self) -> Self { self.sqrt() }
            #[inline] fn cbrt(self) -> Self { self.cbrt() }
            #[inline] fn exp(self) -> Self { self.exp() }
            #[inline] fn exp2(self) -> Self { self.exp2() }
            #[inline] fn exp_m1(self) -> Self { self.exp_m1() }
            #[inline] fn ln_1p(self) -> Self { self.ln_1p() }

            #[inline] fn ln(self) -> Self { self.ln() }
            #[inline] fn log(self, base: Self) -> Self { self.log(base) }
            #[inline] fn log2(self) -> Self { self.log2() }
            #[inline] fn log10(self) -> Self { self.log10() }

            #[inline] fn hypot(self, other: Self) -> Self { self.hypot(other) }
            #[inline] fn sin(self) -> Self { self.sin() }
            #[inline] fn cos(self) -> Self { self.cos() }
            #[inline] fn tan(self) -> Self { self.tan() }
            #[inline] fn asin(self) -> Self { self.asin() }
            #[inline] fn acos(self) -> Self { self.acos() }
            #[inline] fn atan(self) -> Self { self.atan() }
            #[inline] fn atan2(self, other: Self) -> Self { self.atan2(other) }
            #[inline] fn sin_cos(self) -> (Self, Self) { self.sin_cos() }

            #[inline] fn sinh(self) -> Self { self.sinh() }
            #[inline] fn cosh(self) -> Self { self.cosh() }
            #[inline] fn tanh(self) -> Self { self.tanh() }
            #[inline] fn asinh(self) -> Self { self.asinh() }
            #[inline] fn acosh(self) -> Self { self.acosh() }
            #[inline] fn atanh(self) -> Self { self.atanh() }
        }
    )*};
}

#[cfg(not(feature = "std"))]
macro_rules! impl_float {
    ($($t:ty[$n:ident]: $s:expr),*) => {$(
        impl Number for $t {
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
            const BITS: u32 = $s;
            const ZERO: Self = 0.0;
            const ONE: Self = 1.0;

            #[inline]
            fn div_euclid(self, rhs: Self) -> Self {
                let q = Float::trunc(self / rhs);
                if self % rhs < 0.0 {
                    if rhs > 0.0 {
                        q - 1.0
                    } else {
                        q + 1.0
                    }
                } else { q }
            }

            #[inline]
            fn rem_euclid(self, rhs: Self) -> Self {
                let r = self % rhs;
                if r < 0.0 {
                    if rhs > 0.0 {
                        r + rhs
                    } else {
                        r - rhs
                    }
                } else { r }
            }
            
            #[inline] fn abs(self) -> Self { if self.is_nan() { self } else if self.is_sign_negative() { -self } else { self } }
            #[inline] fn abs_diff(self, other: Self) -> Self { if self < other { other - self } else { self - other } }
            #[inline] fn signum(self) -> Self { if self.is_nan() { self } else if self == 0.0 { 0.0 } else if self.is_sign_negative() { -1.0 } else { 1.0 } }
            #[inline] fn is_positive(self) -> bool { self.is_sign_positive() && self != 0.0 }
            #[inline] fn is_negative(self) -> bool { self.is_sign_negative() && self != 0.0 }
            #[inline] fn max(self, other: Self) -> Self { self.max(other) }
            #[inline] fn min(self, other: Self) -> Self { self.min(other) }
            #[inline] fn clamp(self, min: Self, max: Self) -> Self { self.clamp(min, max) }
        }

        impl Signed for $t {}

        impl Float for $t {
            const RADIX: u32 = Self::RADIX;
            const MANTISSA_DIGITS: u32 = Self::MANTISSA_DIGITS;
            const DIGITS: u32 = Self::DIGITS;
            const EPSILON: Self = Self::EPSILON;
            const MIN_POSITIVE: Self = Self::MIN_POSITIVE;
            const MIN_EXP: i32 = Self::MIN_EXP;
            const MAX_EXP: i32 = Self::MAX_EXP;
            const MIN_10_EXP: i32 = Self::MIN_10_EXP;
            const MAX_10_EXP: i32 = Self::MAX_10_EXP;
            const NAN: Self = Self::NAN;
            const INFINITY: Self = Self::INFINITY;
            const NEG_INFINITY: Self = Self::NEG_INFINITY;
            
            const PI: Self = core::$n::consts::PI;
            const TAU: Self = core::$n::consts::TAU;
            const FRAC_PI_2: Self = core::$n::consts::FRAC_PI_2;
            const FRAC_PI_3: Self = core::$n::consts::FRAC_PI_3;
            const FRAC_PI_4: Self = core::$n::consts::FRAC_PI_4;
            const FRAC_PI_6: Self = core::$n::consts::FRAC_PI_6;
            const FRAC_PI_8: Self = core::$n::consts::FRAC_PI_8;
            const FRAC_1_PI: Self = core::$n::consts::FRAC_1_PI;
            const FRAC_2_PI: Self = core::$n::consts::FRAC_2_PI;
            const FRAC_2_SQRT_PI: Self = core::$n::consts::FRAC_2_SQRT_PI;
            const SQRT_2: Self = core::$n::consts::SQRT_2;
            const FRAC_1_SQRT_2: Self = core::$n::consts::FRAC_1_SQRT_2;
            const E: Self = core::$n::consts::E;
            const LOG2_E: Self = core::$n::consts::LOG2_E;
            const LOG2_10: Self = core::$n::consts::LOG2_10;
            const LOG10_E: Self = core::$n::consts::LOG10_E;
            const LOG10_2: Self = core::$n::consts::LOG10_2;
            const LN_2: Self = core::$n::consts::LN_2;
            const LN_10: Self = core::$n::consts::LN_10;

            #[inline] fn is_nan(self) -> bool { self.is_nan() }
            #[inline] fn is_infinite(self) -> bool { self.is_infinite() }
            #[inline] fn is_finite(self) -> bool { self.is_finite() }
            #[inline] fn is_subnormal(self) -> bool { self.is_subnormal() }
            #[inline] fn is_normal(self) -> bool { self.is_normal() }
            #[inline] fn is_sign_positive(self) -> bool { self.is_sign_positive() }
            #[inline] fn is_sign_negative(self) -> bool { self.is_sign_negative() }
            #[inline] fn classify(self) -> FpCategory { self.classify() }
            #[inline] fn recip(self) -> Self { self.recip() }
            #[inline] fn to_degrees(self) -> Self { self.to_degrees() }
            #[inline] fn to_radians(self) -> Self { self.to_radians() }
            #[inline] fn float_signum(self) -> Self { self.signum() }
            
            #[inline]
            fn floor(self) -> Self {
                let f = self.fract();
                if f.is_nan() || f == 0.0 {
                    self
                } else if self < 0.0 {
                    self - f - 1.0
                } else {
                    self - f
                }
            }
            
            #[inline]
            fn ceil(self) -> Self {
                let f = self.fract();
                if f.is_nan() || f == 0.0 {
                    self
                } else if self > 0.0 {
                    self - f + 1.0
                } else {
                    self - f
                }
            }
            
            #[inline]
            fn round(self) -> Self {
                let f = self.fract();
                if f.is_nan() || f == 0.0 {
                    self
                } else if self > 0.0 {
                    if f < 0.5 {
                        self - f
                    } else {
                        self - f + 1.0
                    }
                } else {
                    if -f < 0.5 {
                        self - f
                    } else {
                        self - f - 1.0
                    }
                }
            }
            
            #[inline]
            fn trunc(self) -> Self {
                let f = self.fract();
                if f.is_nan() {
                    self
                } else {
                    self - f
                }
            }
            
            #[inline]
            fn fract(self) -> Self {
                if self == 0.0 {
                    0.0
                } else {
                    self % 1.0
                }
            }
            
            #[inline]
            fn copysign(self, sign: Self) -> Self {
                if self.is_sign_negative() == sign.is_sign_negative() {
                    self
                } else {
                    -self
                }
            }
        }
    )*};
}

impl_float!(f32[f32]: 32, f64[f64]: 64);
