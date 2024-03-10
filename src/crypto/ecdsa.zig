const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const Felt252 = @import("../math/fields/starknet.zig").Felt252;
const CurveParams = @import("../math/curve/curve_params.zig");
const ProjectivePoint = @import("../math/curve/short_weierstrass/projective.zig").ProjectivePoint;
const AffinePoint = @import("../math/curve/short_weierstrass/affine.zig").AffinePoint;

/// Represents an error that can occur during ECDSA signing.
pub const SignError = error{
    /// The message hash is invalid.
    InvalidMessageHash,
    /// The value of `k` is invalid.
    InvalidK,
};

/// Represents an error that can occur during ECDSA verification.
pub const VerifyError = error{
    /// The public key is invalid.
    InvalidPublicKey,
    /// The message hash is invalid.
    InvalidMessageHash,
    /// The value of `r` is invalid.
    InvalidR,
    /// The value of `s` is invalid.
    InvalidS,
};

/// Represents an error that can occur during ECDSA signature recovery.
pub const RecoverError = error{
    /// The message hash is invalid.
    InvalidMessageHash,
    /// The value of `r` is invalid.
    InvalidR,
    /// The value of `s` is invalid.
    InvalidS,
    /// The value of `v` is invalid.
    InvalidV,
};

/// Represents an ECDSA signature.
pub const Signature = struct {
    const Self = @This();

    /// The `r` value of the signature.
    r: Felt252 = .{},
    /// The `s` value of the signature.
    s: Felt252 = .{},
    /// The `v` value of the signature, if it's provided.
    v: ?Felt252 = null,

    /// Initializes an ECDSA signature with `r` and `s` values.
    pub fn init(r: Felt252, s: Felt252) Self {
        return .{ .r = r, .s = s };
    }

    /// Initializes an ECDSA signature with extended `r`, `s`, and `v` values.
    pub fn initExtended(r: Felt252, s: Felt252, v: Felt252) Self {
        return .{ .r = r, .s = s, .v = v };
    }

    pub fn sign(private_key: *const Felt252, message: *const Felt252, k: *const Felt252) !Self {
        if (message.gte(&comptime Felt252.MaxField)) return SignError.InvalidMessageHash;
        if (k.isZero()) return SignError.InvalidK;

        const full_r = (comptime CurveParams.GENERATOR).mulByScalarProjective(k);

        const r = full_r.x;

        if (r.isZero() or r.gte(&comptime Felt252.MaxField)) return SignError.InvalidK;

        const s = Felt252.fromBytesLe(
            r.fromMontgomery().mulMod(
                &private_key.fromMontgomery(),
                &comptime CurveParams.EC_ORDER.fromMontgomery(),
            ).addWithCarry(
                &message.fromMontgomery(),
            )[0].mulMod(
                &(try k.modInverse(comptime CurveParams.EC_ORDER)).fromMontgomery(),
                &comptime CurveParams.EC_ORDER.fromMontgomery(),
            ).toBytesLe(),
        );

        if (s.isZero() or s.gte(&comptime Felt252.MaxField))
            return SignError.InvalidK;

        return .{
            .r = r,
            .s = s,
            .v = Felt252.fromBytesLe(
                full_r.y.fromMontgomery()
                    .bitAnd(&comptime Felt252.one().fromMontgomery())
                    .toBytesLe(),
            ),
        };
    }

    pub fn verify(self: *const Self, public_key: *const Felt252, message: *const Felt252) !bool {
        if (message.gte(&Felt252.MaxField)) return VerifyError.InvalidMessageHash;
        if (self.r.isZero() or self.r.gte(&Felt252.MaxField)) return VerifyError.InvalidR;
        if (self.s.isZero() or self.s.gte(&Felt252.MaxField)) return VerifyError.InvalidS;

        const full_public_key = AffinePoint.fromX(public_key.*) catch return VerifyError.InvalidPublicKey;

        const w = try self.s.modInverse(CurveParams.EC_ORDER);

        if (w.isZero() or w.gte(&Felt252.MaxField)) return VerifyError.InvalidS;

        const zw_g = CurveParams.GENERATOR.mulByScalarProjective(
            &Felt252.fromBytesLe(message.fromMontgomery().mulMod(
                &w.fromMontgomery(),
                &CurveParams.EC_ORDER.fromMontgomery(),
            ).toBytesLe()),
        );

        const rw_q = full_public_key.mulByScalarProjective(
            &Felt252.fromBytesLe(
                self.r.fromMontgomery().mulMod(
                    &w.fromMontgomery(),
                    &CurveParams.EC_ORDER.fromMontgomery(),
                ).toBytesLe(),
            ),
        );

        return (try zw_g.add(&rw_q)).x.eql(self.r) or
            (try zw_g.sub(&rw_q)).x.eql(self.r);
    }

    pub fn recover(self: *const Self, message: *const Felt252) !Felt252 {
        if (message.gte(&Felt252.MaxField)) return RecoverError.InvalidMessageHash;

        if (self.r.isZero() or self.r.gte(&Felt252.MaxField)) return RecoverError.InvalidR;
        if (self.s.isZero() or self.s.gte(&Felt252.MaxField)) return RecoverError.InvalidS;
        if (self.v.?.gt(&Felt252.one())) return RecoverError.InvalidV;

        var full_r = AffinePoint.fromX(self.r) catch return RecoverError.InvalidR;

        if (!Felt252.fromBytesLe(
            full_r.y.fromMontgomery().bitAnd(
                &comptime Felt252.one().fromMontgomery(),
            ).toBytesLe(),
        ).eql(self.v.?))
            full_r.y = full_r.y.neg();

        const full_rs = full_r.mulByScalarProjective(&self.s);

        const zg = CurveParams.GENERATOR.mulByScalarProjective(message);

        const r_inv = try self.r.modInverse(CurveParams.EC_ORDER);

        const rs_zg = try full_rs.sub(&zg);

        return rs_zg.mulByScalarProjective(&r_inv).x;
    }
};

/// Computes the public key corresponding to the given private key using the elliptic curve parameters.
///
/// This function calculates the public key corresponding to the provided private key
/// using the elliptic curve parameters. It performs scalar multiplication of the base generator point
/// by the private key, following the ECDSA key-pair generation process, and returns the x-coordinate of the resulting point as the public key.
///
/// # Key Generation
///
/// The ECDSA key-pair consists of:
/// - Private key (integer): `privKey`
/// - Public key (EC point): `pubKey = privKey * G`
///
/// The private key is generated as a random integer in the range [0...n-1], where `n` is the order of the base generator point `G`.
/// The public key `pubKey` is a point on the elliptic curve, calculated by the EC point multiplication: `pubKey = privKey * G` (the private key, multiplied by the generator point `G`).
///
/// # Arguments
///
/// * `private_key` - A pointer to the private key represented as a field element.
///
/// # Returns
///
/// The x-coordinate of the resulting point after scalar multiplication, representing the public key.
pub fn getPublicKey(private_key: *const Felt252) Felt252 {
    // Scalar multiply the base generator point by the private key and return the x-coordinate.
    return CurveParams.GENERATOR.mulByScalarProjective(private_key).x;
}

// Test cases ported from:
//   https://github.com/starkware-libs/crypto-cpp/blob/95864fbe11d5287e345432dbe1e80dea3c35fc58/src/starkware/crypto/ffi/crypto_lib_test.go

test "getPublicKey: first test" {
    const private_key = Felt252.fromInt(
        u256,
        0x03c1e9550e66958296d11b60f8e8e7a7ad990d07fa65d5f7652c4a6c87d4e3cc,
    );

    const expected_key = Felt252.fromInt(
        u256,
        0x077a3b314db07c45076d11f62b6f9e748a39790441823307743cf00d6597ea43,
    );

    try expect(getPublicKey(&private_key).eql(expected_key));
}

test "getPublicKey: second test" {
    const private_key = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000012,
    );

    const expected_key = Felt252.fromInt(
        u256,
        0x019661066e96a8b9f06a1d136881ee924dfb6a885239caa5fd3f87a54c6b25c4,
    );

    try expect(getPublicKey(&private_key).eql(expected_key));
}

test "Signature: verify valid message" {
    const public_key = Felt252.fromInt(
        u256,
        0x01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca,
    );

    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    const r_bytes = Felt252.fromInt(
        u256,
        0x0411494b501a98abd8262b0da1351e17899a0c4ef23dd2f96fec5ba847310b20,
    );

    const s_bytes = Felt252.fromInt(
        u256,
        0x0405c3191ab3883ef2b763af35bc5f5d15b3b4e99461d70e84c654a351a7c81b,
    );

    const signature = Signature.init(r_bytes, s_bytes);

    try expect(try signature.verify(&public_key, &message_hash));
}

test "Signature: verify invalid message" {
    const public_key = Felt252.fromInt(
        u256,
        0x077a4b314db07c45076d11f62b6f9e748a39790441823307743cf00d6597ea43,
    );

    const message_hash = Felt252.fromInt(
        u256,
        0x0397e76d1667c4454bfb83514e120583af836f8e32a516765497823eabe16a3f,
    );

    const r_bytes = Felt252.fromInt(
        u256,
        0x0173fd03d8b008ee7432977ac27d1e9d1a1f6c98b1a2f05fa84a21c84c44e882,
    );

    const s_bytes = Felt252.fromInt(
        u256,
        0x01f2c44a7798f55192f153b4c48ea5c1241fbb69e6132cc8a0da9c5b62a4286e,
    );

    const signature = Signature.init(r_bytes, s_bytes);

    try expect(!(try signature.verify(&public_key, &message_hash)));
}

test "Signature: verify with invalid public key" {
    const public_key = Felt252.fromInt(
        u256,
        0x03ee9bffffffffff26ffffffff60ffffffffffffffffffffffffffff004accff,
    );

    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    const r_bytes = Felt252.fromInt(
        u256,
        0x0411494b501a98abd8262b0da1351e17899a0c4ef23dd2f96fec5ba847310b20,
    );

    const s_bytes = Felt252.fromInt(
        u256,
        0x0405c3191ab3883ef2b763af35bc5f5d15b3b4e99461d70e84c654a351a7c81b,
    );

    const signature = Signature.init(r_bytes, s_bytes);

    try expectError(VerifyError.InvalidPublicKey, signature.verify(&public_key, &message_hash));
}

test "Signature: test message signature" {
    const private_key = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    );

    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    const k = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000003,
    );

    const signature = try Signature.sign(&private_key, &message_hash, &k);
    const public_key = getPublicKey(&private_key);

    try expect((try signature.verify(&public_key, &message_hash)));
}

test "Signature: test recover" {
    const private_key = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    );

    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    const k = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000003,
    );

    const signature = try Signature.sign(&private_key, &message_hash, &k);

    try expectEqual(getPublicKey(&private_key), try signature.recover(&message_hash));
}

test "Signature: test recover with invalid r" {
    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    const r = Felt252.fromInt(
        u256,
        0x03ee9bffffffffff26ffffffff60ffffffffffffffffffffffffffff004accff,
    );

    const s = Felt252.fromInt(
        u256,
        0x0405c3191ab3883ef2b763af35bc5f5d15b3b4e99461d70e84c654a351a7c81b,
    );

    const v = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    );

    const signature = Signature.initExtended(r, s, v);

    try expectError(RecoverError.InvalidR, signature.recover(&message_hash));

    std.debug.print("EMPTY_UNCLE_HASH = {any}\n", .{CurveParams.EC_ORDER.toU256()});
}
