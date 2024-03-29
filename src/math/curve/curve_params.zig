// code ported from starknet-curve:
// https://github.com/xJonathanLEI/starknet-rs/blob/0857bd6cd3bd34cbb06708f0a185757044171d8d/starknet-curve/src/curve_params.rs
const Felt252 = @import("../fields/starknet.zig").Felt252;
const bigInt = @import("../fields/biginteger.zig").bigInt;
const AffinePoint = @import("./short_weierstrass/affine.zig").AffinePoint;

/// Represents the order of the subgroup generated by the base point on the STARK-friendly elliptic curve.
///
/// The EC_ORDER constant defines the order of the subgroup generated by the base point on the elliptic curve used in the STARK scheme.
/// It is a crucial parameter in cryptographic operations, including ECDSA, as it determines the size of the cryptographic group.
/// The EC_ORDER is a large prime number, ensuring the security of the elliptic curve cryptographic scheme.
///
/// # Description
///
/// The EC_ORDER constant is represented as a field element (Felt252) initialized from a hexadecimal integer value.
/// It defines the order of the subgroup generated by the base point, ensuring that the discrete logarithm problem is hard to solve.
///
/// # Value
///
/// The value of EC_ORDER is derived from the hexadecimal integer:
/// 0x800000000000010ffffffffffffffffb781126dcae7b2321e66a241adc64d2f
///
/// # Remarks
///
/// - The EC_ORDER ensures the security of the STARK-friendly elliptic curve by defining the size of the subgroup.
/// - It is essential for cryptographic operations, including key generation and signature generation.
pub const EC_ORDER = Felt252.fromInt(
    u256,
    0x800000000000010ffffffffffffffffb781126dcae7b2321e66a241adc64d2f,
);

/// Represents the coefficient 𝛼 in the equation of the STARK-friendly elliptic curve.
///
/// The ALPHA constant defines the coefficient 𝛼 in the equation of the STARK-friendly elliptic curve.
/// It is a crucial parameter in defining the elliptic curve equation, which ensures cryptographic security and efficiency.
/// The value of ALPHA is typically chosen to meet specific security requirements and compatibility with cryptographic protocols.
///
/// # Description
///
/// The ALPHA constant is represented as a field element (Felt252) initialized to the value one.
/// It serves as the coefficient 𝛼 in the elliptic curve equation: 𝑦^2 ≡ 𝑥^3 + 𝛼⋅𝑥 + 𝛽 (mod 𝑝).
///
/// # Value
///
/// The value of ALPHA is one, representing the identity element in field arithmetic operations.
///
/// # Remarks
///
/// - ALPHA is a fundamental parameter in defining the equation of the STARK-friendly elliptic curve.
/// - It is typically chosen to ensure the security and efficiency of cryptographic operations.
pub const ALPHA = Felt252.one();

/// Represents the coefficient 𝛽 in the equation of the STARK-friendly elliptic curve.
///
/// The BETA constant defines the coefficient 𝛽 in the equation of the STARK-friendly elliptic curve.
/// It is a crucial parameter in defining the elliptic curve equation, contributing to the curve's shape and cryptographic properties.
/// The value of BETA is typically chosen to meet specific security requirements and compatibility with cryptographic protocols.
///
/// # Description
///
/// The BETA constant is represented as a field element (Felt252) initialized from a hexadecimal integer value.
/// It serves as the coefficient 𝛽 in the elliptic curve equation: 𝑦^2 ≡ 𝑥^3 + 𝛼⋅𝑥 + 𝛽 (mod 𝑝).
///
/// # Value
///
/// The value of BETA is derived from the hexadecimal integer:
/// 0x6f21413efbe40de150e596d72f7a8c5609ad26c15c915c1f4cdfcb99cee9e89
///
/// # Remarks
///
/// - BETA is a fundamental parameter in defining the equation of the STARK-friendly elliptic curve.
/// - It contributes to the curve's shape and ensures cryptographic security.
pub const BETA = Felt252.fromInt(
    u256,
    0x6f21413efbe40de150e596d72f7a8c5609ad26c15c915c1f4cdfcb99cee9e89,
);

/// Represents the base point of the elliptic curve, which generates a subgroup of large prime order `n`.
///
/// The generator point `G` is a fundamental point on the elliptic curve used in various cryptographic operations, including ECDSA.
/// It generates a subgroup of large prime order `n`, forming the basis for key generation and cryptographic operations.
///
/// # Description
///
/// The generator point `G` is defined by its x and y coordinates on the elliptic curve.
/// These coordinates are provided as field elements (Felt252) representing the x and y components of the point.
/// Additionally, the `infinity` flag indicates whether the point is at infinity or not.
///
/// # Parameters
///
/// * `x` - The x-coordinate of the generator point.
/// * `y` - The y-coordinate of the generator point.
/// * `infinity` - A boolean flag indicating whether the generator point is at infinity.
pub const GENERATOR: AffinePoint = .{
    .x = Felt252.fromInt(
        u256,
        0x1ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca,
    ),
    .y = Felt252.fromInt(
        u256,
        0x5668060aa49730b7be4801df46ec62de53ecd11abe43a32873000c36e8dc1f,
    ),
    .infinity = false,
};

/// The shift point 𝑃0 was added for technical reasons to make sure the point at infinity on the elliptic curve does not appear during the computation.
pub const SHIFT_POINT: AffinePoint = .{
    .x = Felt252.fromInt(
        u256,
        0x49ee3eba8c1600700ee1b87eb599f16716b0b1022947733551fde4050ca6804,
    ),
    .y = Felt252.fromInt(
        u256,
        0x3ca0cfe4b3bc6ddf346d49d06ea0ed34e621062c0e056c1d0405d266e10268a,
    ),
    .infinity = false,
};

/// Constant representing the Pedersen hash point P0.
/// P0 is derived from the decimal digits of π and is used in the Pedersen hash function.
pub const PEDERSEN_P0: AffinePoint = .{
    .x = Felt252.fromInt(
        u256,
        0x234287dcbaffe7f969c748655fca9e58fa8120b6d56eb0c1080d17957ebe47b,
    ),
    .y = Felt252.fromInt(
        u256,
        0x3b056f100f96fb21e889527d41f4e39940135dd7a6c94cc6ed0268ee89e5615,
    ),
    .infinity = false,
};

/// Constant representing the Pedersen hash point P1.
/// P1 is derived from the decimal digits of π and is used in the Pedersen hash function.
pub const PEDERSEN_P1: AffinePoint = .{
    .x = Felt252.fromInt(
        u256,
        0x4fa56f376c83db33f9dab2656558f3399099ec1de5e3018b7a6932dba8aa378,
    ),
    .y = Felt252.fromInt(
        u256,
        0x3fa0984c931c9e38113e0c0e47e4401562761f92a7a23b45168f4e80ff5b54d,
    ),
    .infinity = false,
};

/// Constant representing the Pedersen hash point P2.
/// P2 is derived from the decimal digits of π and is used in the Pedersen hash function.
pub const PEDERSEN_P2: AffinePoint = .{
    .x = Felt252.fromInt(
        u256,
        0x4ba4cc166be8dec764910f75b45f74b40c690c74709e90f3aa372f0bd2d6997,
    ),
    .y = Felt252.fromInt(
        u256,
        0x40301cf5c1751f4b971e46c4ede85fcac5c59a5ce5ae7c48151f27b24b219c,
    ),
    .infinity = false,
};

/// Constant representing the Pedersen hash point P3.
/// P3 is derived from the decimal digits of π and is used in the Pedersen hash function.
pub const PEDERSEN_P3: AffinePoint = .{
    .x = Felt252.fromInt(
        u256,
        0x54302dcb0e6cc1c6e44cca8f61a63bb2ca65048d53fb325d36ff12c49a58202,
    ),
    .y = Felt252.fromInt(
        u256,
        0x1b77b3e37d13504b348046268d8ae25ce98ad783c25561a879dcc77e99c2426,
    ),
    .infinity = false,
};
