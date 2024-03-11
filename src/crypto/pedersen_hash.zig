const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const Felt252 = @import("../math/fields/starknet.zig").Felt252;
const CurveParams = @import("../math/curve/curve_params.zig");
const ProjectivePoint = @import("../math/curve/short_weierstrass/projective.zig").ProjectivePoint;
const AffinePoint = @import("../math/curve/short_weierstrass/affine.zig").AffinePoint;
const pedersen_constants = @import("./pedersen/constants.zig");

const SHIFT_POINT = ProjectivePoint.fromAffinePoint(&CurveParams.SHIFT_POINT);

fn boolsToUsizeLe(bits: []const bool) usize {
    var result: usize = 0;
    for (bits, 0..) |bit, i| {
        if (bit) {
            result += @as(usize, 1) << @intCast(i);
        }
    }

    return result;
}

fn addPoints(acc: *ProjectivePoint, bits: []const bool, prep: []const AffinePoint) void {
    // Preprocessed material is lookup-tables for each chunk of bits
    const table_size = (1 << pedersen_constants.CURVE_CONSTS_BITS) - 1;

    for (0..bits.len / pedersen_constants.CURVE_CONSTS_BITS) |i| {
        const offset = boolsToUsizeLe(bits[i * pedersen_constants.CURVE_CONSTS_BITS .. (i + 1) * pedersen_constants.CURVE_CONSTS_BITS][0..4]);

        if (offset > 0) {
            // Table lookup at 'offset-1' in table for chunk 'i'
            acc.addAffineAssign(&prep[i * table_size + offset - 1]);
        }
    }
}

/// Computes the Starkware version of the Pedersen hash of x and y.
///
pub fn pedersenHash(x: Felt252, y: Felt252) Felt252 {
    const x_bits = x.toBitsLe();
    const y_bits = y.toBitsLe();

    // Compute hash
    var acc = SHIFT_POINT;

    addPoints(&acc, x_bits[0..248], &pedersen_constants.CURVE_CONSTS_P0); // Add a_low * P1
    addPoints(&acc, x_bits[248..252], &pedersen_constants.CURVE_CONSTS_P1); // Add a_high * P2
    addPoints(&acc, y_bits[0..248], &pedersen_constants.CURVE_CONSTS_P2); // Add b_low * P3
    addPoints(&acc, y_bits[248..252], &pedersen_constants.CURVE_CONSTS_P3); // Add b_high * P4

    // Return x-coordinate
    return AffinePoint.fromProjectivePoint(&acc).x;
}

test "Pedersen hash" {
    //   Test case ported from:
    //   https://github.com/starkware-libs/crypto-cpp/blob/95864fbe11d5287e345432dbe1e80dea3c35fc58/src/starkware/crypto/ffi/crypto_lib_test.go
    const in1 = Felt252.fromInt(
        u256,
        0x03d937c035c878245caf64531a5756109c53068da139362728feb561405371cb,
    );
    const in2 = Felt252.fromInt(
        u256,
        0x0208a0a10250e382e1e4bbe2880906c2791bf6275695e02fbbc6aeff9cd8b31a,
    );
    const expected_hash = Felt252.fromInt(
        u256,
        0x030e480bed5fe53fa909cc0f8c4d99b8f9f2c016be4c41e13a4848797979c662,
    );

    try std.testing.expectEqual(expected_hash, pedersenHash(in1, in2));
}
