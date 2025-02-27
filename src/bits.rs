use std::ops::{BitAnd, Not, Shl, Shr};

use num_traits::{One, Zero};

/// Sign-extends a `srcbits`-bit number into a [`u32`].
pub fn sign_extend(base: u32, srcbits: u32) -> u32 {
    if srcbits == 0 {
        return 0;
    }
    let value_bits = srcbits - 1;
    let value = base & !(!0u32 << value_bits);
    let sign = if is_set(base, value_bits) {
        !0u32 << value_bits
    } else {
        0
    };
    let out = sign | value;
    out
}

/// Isolates bits `lsb` to `lsb + count` from `value` and moves them to bits 0-`count`.
///
/// Useful for extracting from bitfields.
pub fn extract<
    T: Zero + Not<Output = T> + Shr<Output = T> + Shl<Output = T> + BitAnd<Output = T>,
>(
    value: T,
    lsb: T,
    count: T,
) -> T {
    (value >> lsb) & !(!T::zero() << count)
}

/// Checks if a single bit is set.
pub fn is_set<T: Zero + One + BitAnd<Output = T> + Shl<Output = T> + PartialEq>(
    value: T,
    bit: T,
) -> bool {
    (value & (T::one() << bit)) != T::zero()
}
