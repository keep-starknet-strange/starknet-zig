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

    /// Signs a message using the provided private key and nonce (random scalar) in the elliptic curve digital signature algorithm (ECDSA).
    ///
    /// This method generates an ECDSA signature for a given message using the provided private key and nonce (`k`).
    /// The signature process involves several cryptographic operations to ensure the integrity and authenticity of the message.
    ///
    /// # Arguments
    ///
    /// * `private_key` - A pointer to the private key represented as a field element.
    /// * `message` - A pointer to the message represented as a field element.
    /// * `k` - A pointer to the nonce (random scalar) represented as a field element. This nonce is crucial for security, and its uniqueness for each message is essential to prevent key recovery attacks.
    ///
    /// # Returns
    ///
    /// An ECDSA signature containing the `r` and `s` values. The signature represents the cryptographic proof of the message's authenticity and integrity.
    ///
    /// # Errors
    ///
    /// Returns an error if any error occurs during the signing process, such as an invalid message hash or nonce. It's essential to handle these errors to ensure the security and reliability of the signature.
    ///
    /// # Remarks
    ///
    /// - It's crucial to use a cryptographically secure random number generator for generating the nonce (`k`) to prevent predictable signatures and key recovery attacks.
    /// - The uniqueness of the nonce (`k`) for each message is fundamental to the security of the ECDSA scheme. Reusing the same nonce for multiple messages can lead to the leakage of the private key.
    pub fn sign(private_key: *const Felt252, message: *const Felt252, k: *const Felt252) !Self {
        // Check if the message hash is valid
        if (message.gte(&comptime Felt252.MaxField)) return SignError.InvalidMessageHash;

        // Check if the nonce `k` is zero
        if (k.isZero()) return SignError.InvalidK;

        // Compute curve point r = k * G
        const full_r = (comptime CurveParams.GENERATOR).mulByScalarProjective(k);
        const r = full_r.x;

        // Check if r is zero or greater than the maximum field value
        if (r.isZero() or r.gte(&comptime Felt252.MaxField)) return SignError.InvalidK;

        // Compute s = (k^(-1) * (z + rd_A)) mod n
        const s = Felt252.fromBytesLe(
            r.toBigInt().mulMod(
                &private_key.toBigInt(),
                &comptime CurveParams.EC_ORDER.toBigInt(),
            ).addWithCarry(
                &message.toBigInt(),
            )[0].mulMod(
                &(try k.modInverse(comptime CurveParams.EC_ORDER)).toBigInt(),
                &comptime CurveParams.EC_ORDER.toBigInt(),
            ).toBytesLe(),
        );

        // Check if s is zero or greater than the maximum field value
        if (s.isZero() or s.gte(&comptime Felt252.MaxField)) return SignError.InvalidK;

        // Calculate v = (y-coordinate of full_r) mod 2
        const v = Felt252.fromBytesLe(
            full_r.y.toBigInt()
                .bitAnd(&comptime Felt252.one().toBigInt())
                .toBytesLe(),
        );

        return .{ .r = r, .s = s, .v = v };
    }

    /// Verifies the authenticity of an ECDSA signature.
    ///
    /// This function verifies whether a given ECDSA signature is authentic by checking against the provided public key and message hash.
    ///
    /// # Arguments
    ///
    /// * `public_key` - A pointer to the public key represented as a field element.
    /// * `message` - A pointer to the message hash represented as a field element.
    ///
    /// # Returns
    ///
    /// Returns `true` if the signature is authentic, `false` otherwise.
    ///
    /// # Errors
    ///
    /// Returns an error if any error occurs during the verification process, such as an invalid message hash, `r`, `s`, or public key.
    ///
    /// # Math Behind the ECDSA Sign/Verify
    ///
    /// How does the above sign/verify scheme work? Let's delve into the mathematics behind it.
    /// The equation behind the recovery of the point R', calculated during the signature verification, can be transformed by replacing the pubKey with privKey * G as follows:
    ///
    /// R' = (h * s1) * G + (r * s1) * pubKey =
    ///     = (h * s1) * G + (r * s1) * privKey * G
    ///     = (h + r * privKey) * s1 * G
    ///
    /// If we take the number s = (z + r * privKey) * k^(-1) (calculated during the signing process), we can calculate s1 = s * k as follows:
    ///
    /// s1 = s * k^(-1) =
    ///     = ((z + r * privKey) * k^(-1)) * k
    ///     = z + r * privKey
    ///
    /// Now, replace s1 in the point R':
    ///
    /// R' = (h + r * privKey) * s1 * G =
    ///     = (z + r * privKey) * G =
    ///     = k * G
    ///
    /// The final step is to compare the point R' (decoded by the pubKey) with the point R (encoded by the privKey).
    /// The algorithm, in fact, compares only the x-coordinates of R' and R: the integers r' and r.
    /// It is expected that r' == r if the signature is valid and r' ≠ r if the signature or the message or the public key is incorrect.
    pub fn verify(self: *const Self, public_key: *const Felt252, message: *const Felt252) !bool {
        // Check if the message hash is within the valid range
        if (message.gte(&comptime Felt252.MaxField)) return VerifyError.InvalidMessageHash;

        // Check if the 'r' value is zero or exceeds the maximum field value
        if (self.r.isZero() or self.r.gte(&comptime Felt252.MaxField)) return VerifyError.InvalidR;

        // Check if the 's' value is zero or exceeds the maximum field value
        if (self.s.isZero() or self.s.gte(&comptime Felt252.MaxField)) return VerifyError.InvalidS;

        // Attempt to convert the provided public key to an affine point
        const full_public_key = AffinePoint.fromX(public_key.*) catch
            return VerifyError.InvalidPublicKey;

        // Calculate the modular inverse of 's' with respect to the EC order
        const w = try self.s.modInverse(CurveParams.EC_ORDER);

        // Check if the modular inverse of 's' is zero or exceeds the maximum field value
        if (w.isZero() or w.gte(&Felt252.MaxField)) return VerifyError.InvalidS;

        // Calculate 'zw * G'
        const zw_g = CurveParams.GENERATOR.mulByScalarProjective(
            &Felt252.fromBytesLe(
                message.toBigInt().mulMod(
                    &w.toBigInt(),
                    &CurveParams.EC_ORDER.toBigInt(),
                ).toBytesLe(),
            ),
        );

        // Calculate 'rw * Q'
        const rw_q = full_public_key.mulByScalarProjective(
            &Felt252.fromBytesLe(
                self.r.toBigInt().mulMod(
                    &w.toBigInt(),
                    &CurveParams.EC_ORDER.toBigInt(),
                ).toBytesLe(),
            ),
        );

        // Check if the sum or difference of 'zw * G' and 'rw * Q' matches the 'r' value
        return (try zw_g.add(&rw_q)).x.eql(self.r) or
            (try zw_g.sub(&rw_q)).x.eql(self.r);
    }

    /// Recovers the public key from a given ECDSA signature and message hash.
    ///
    /// This function attempts to recover the public key used to sign a message from the provided ECDSA signature and message hash.
    /// The ECDSA signature scheme allows the public key to be recovered from the signed message together with the signature.
    /// The recovery process is based on some mathematical computations (described in the SECG: SEC 1 standard) and returns 0, 1, or 2 possible EC points that are valid public keys, corresponding to the signature.
    /// To avoid this ambiguity, some ECDSA implementations add one additional bit v to the signature during the signing process, and it takes the form {r, s, v}.
    /// From this extended ECDSA signature {r, s, v} + the signed message, the signer's public key can be restored with confidence.
    ///
    /// # Arguments
    ///
    /// * `message` - A pointer to the message hash represented as a field element.
    ///
    /// # Returns
    ///
    /// Returns the recovered public key as a field element if successful.
    ///
    /// # Errors
    ///
    /// Returns an error if any error occurs during the recovery process, such as an invalid message hash, `r`, `s`, or `v` value.
    ///
    /// # Note
    ///
    /// Public key recovery is possible for signatures based on the ElGamal signature scheme (such as DSA and ECDSA). This feature is particularly useful in bandwidth-constrained or storage-constrained environments, such as blockchain systems, where transmission or storage of the public keys cannot be afforded. For example, the Ethereum blockchain uses extended signatures {r, s, v} for the signed transactions on the chain to save storage and bandwidth.
    pub fn recover(self: *const Self, message: *const Felt252) !Felt252 {
        // Check if the message hash is within the valid range
        if (message.gte(&Felt252.MaxField)) return RecoverError.InvalidMessageHash;

        // Check if the 'r' value is zero or exceeds the maximum field value
        if (self.r.isZero() or self.r.gte(&Felt252.MaxField)) return RecoverError.InvalidR;

        // Check if the 's' value is zero or exceeds the maximum field value
        if (self.s.isZero() or self.s.gte(&Felt252.MaxField)) return RecoverError.InvalidS;

        // Check if the 'v' value is greater than one
        if (self.v.?.gt(&Felt252.one())) return RecoverError.InvalidV;

        // Attempt to convert the 'r' value to an affine point
        var full_r = AffinePoint.fromX(self.r) catch return RecoverError.InvalidR;

        // Adjust the 'y' coordinate of 'full_r' based on the 'v' value
        if (!Felt252.fromBytesLe(
            full_r.y.toBigInt().bitAnd(
                &comptime Felt252.one().toBigInt(),
            ).toBytesLe(),
        ).eql(self.v.?))
            full_r.y = full_r.y.neg();

        // Calculate 'full_r * s'
        const full_rs = full_r.mulByScalarProjective(&self.s);

        // Calculate 'G * message'
        const zg = CurveParams.GENERATOR.mulByScalarProjective(message);

        // Calculate the modular inverse of 'r' with respect to the EC order
        const r_inv = try self.r.modInverse(comptime CurveParams.EC_ORDER);

        // Calculate '(full_rs - zg) * r_inv'
        const rs_zg = try full_rs.sub(&zg);

        // Return the 'x' coordinate of '(rs_zg * r_inv)'
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
    // Define a private key for testing purposes
    const private_key = Felt252.fromInt(
        u256,
        0x03c1e9550e66958296d11b60f8e8e7a7ad990d07fa65d5f7652c4a6c87d4e3cc,
    );

    // Define the expected public key corresponding to the private key
    const expected_key = Felt252.fromInt(
        u256,
        0x077a3b314db07c45076d11f62b6f9e748a39790441823307743cf00d6597ea43,
    );

    // Call the getPublicKey function with the private key and verify the result
    try expect(getPublicKey(&private_key).eql(expected_key));
}

test "getPublicKey: second test" {
    // Define a private key for testing purposes
    const private_key = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000012,
    );

    // Define the expected public key corresponding to the private key
    const expected_key = Felt252.fromInt(
        u256,
        0x019661066e96a8b9f06a1d136881ee924dfb6a885239caa5fd3f87a54c6b25c4,
    );

    // Call the getPublicKey function with the private key and verify the result
    try expect(getPublicKey(&private_key).eql(expected_key));
}

test "Signature: verify valid message" {
    // Define the public key for testing purposes
    const public_key = Felt252.fromInt(
        u256,
        0x01ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca,
    );

    // Define the message hash for testing purposes
    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    // Define the `r` value of the signature
    const r_bytes = Felt252.fromInt(
        u256,
        0x0411494b501a98abd8262b0da1351e17899a0c4ef23dd2f96fec5ba847310b20,
    );

    // Define the `s` value of the signature
    const s_bytes = Felt252.fromInt(
        u256,
        0x0405c3191ab3883ef2b763af35bc5f5d15b3b4e99461d70e84c654a351a7c81b,
    );

    // Initialize the signature with the `r` and `s` values
    const signature = Signature.init(r_bytes, s_bytes);

    // Verify the signature against the provided public key and message hash
    try expect(try signature.verify(&public_key, &message_hash));
}

test "Signature: verify invalid message" {
    // Define the public key for testing purposes
    const public_key = Felt252.fromInt(
        u256,
        0x077a4b314db07c45076d11f62b6f9e748a39790441823307743cf00d6597ea43,
    );

    // Define the message hash for testing purposes
    const message_hash = Felt252.fromInt(
        u256,
        0x0397e76d1667c4454bfb83514e120583af836f8e32a516765497823eabe16a3f,
    );

    // Define the `r` value of the signature
    const r_bytes = Felt252.fromInt(
        u256,
        0x0173fd03d8b008ee7432977ac27d1e9d1a1f6c98b1a2f05fa84a21c84c44e882,
    );

    // Define the `s` value of the signature
    const s_bytes = Felt252.fromInt(
        u256,
        0x01f2c44a7798f55192f153b4c48ea5c1241fbb69e6132cc8a0da9c5b62a4286e,
    );

    // Initialize the signature with the `r` and `s` values
    const signature = Signature.init(r_bytes, s_bytes);

    // Verify that the signature does not verify against the provided public key and message hash
    try expect(!(try signature.verify(&public_key, &message_hash)));
}

test "Signature: verify with invalid public key" {
    // Define an invalid public key for testing purposes
    const public_key = Felt252.fromInt(
        u256,
        0x03ee9bffffffffff26ffffffff60ffffffffffffffffffffffffffff004accff,
    );

    // Define the message hash for testing purposes
    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    // Define the `r` value of the signature
    const r_bytes = Felt252.fromInt(
        u256,
        0x0411494b501a98abd8262b0da1351e17899a0c4ef23dd2f96fec5ba847310b20,
    );

    // Define the `s` value of the signature
    const s_bytes = Felt252.fromInt(
        u256,
        0x0405c3191ab3883ef2b763af35bc5f5d15b3b4e99461d70e84c654a351a7c81b,
    );

    // Initialize the signature with the `r` and `s` values
    const signature = Signature.init(r_bytes, s_bytes);

    // Verify that an error is thrown when attempting to verify the signature with the invalid public key
    try expectError(VerifyError.InvalidPublicKey, signature.verify(&public_key, &message_hash));
}

test "Signature: test message signature" {
    // Define the private key for testing purposes
    const private_key = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    );

    // Define the message hash for testing purposes
    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    // Define the nonce (random scalar) for testing purposes
    const k = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000003,
    );

    // Sign the message using the provided private key and nonce
    const signature = try Signature.sign(&private_key, &message_hash, &k);

    // Derive the public key from the provided private key
    const public_key = getPublicKey(&private_key);

    // Verify that the signature is valid for the provided public key and message hash
    try expect(try signature.verify(&public_key, &message_hash));
}

test "Signature: test recover" {
    // Define the private key for testing purposes
    const private_key = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000001,
    );

    // Define the message hash for testing purposes
    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    // Define the nonce (random scalar) for testing purposes
    const k = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000003,
    );

    // Sign the message using the provided private key and nonce
    const signature = try Signature.sign(&private_key, &message_hash, &k);

    // Recover the public key from the signature and message hash
    try expectEqual(getPublicKey(&private_key), try signature.recover(&message_hash));
}

test "Signature: test recover with invalid r" {
    // Define the message hash for testing purposes
    const message_hash = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000002,
    );

    // Define the 'r' value for testing purposes
    const r = Felt252.fromInt(
        u256,
        0x03ee9bffffffffff26ffffffff60ffffffffffffffffffffffffffff004accff,
    );

    // Define the 's' value for testing purposes
    const s = Felt252.fromInt(
        u256,
        0x0405c3191ab3883ef2b763af35bc5f5d15b3b4e99461d70e84c654a351a7c81b,
    );

    // Define the 'v' value for testing purposes
    const v = Felt252.fromInt(
        u256,
        0x0000000000000000000000000000000000000000000000000000000000000000,
    );

    // Initialize a signature with the provided 'r', 's', and 'v' values
    const signature = Signature.initExtended(r, s, v);

    // Attempt to recover the public key from the signature and message hash
    try expectError(RecoverError.InvalidR, signature.recover(&message_hash));
}
