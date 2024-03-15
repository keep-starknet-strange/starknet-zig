const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const Felt252 = @import("../math/fields/starknet.zig").Felt252;
const big_int = @import("../math/fields/biginteger.zig").bigInt(4);
const field_constants = @import("../math/fields/constants.zig");
const CurveParams = @import("../math/curve/curve_params.zig");
const ProjectivePoint = @import("../math/curve/short_weierstrass/projective.zig").ProjectivePoint;
const AffinePoint = @import("../math/curve/short_weierstrass/affine.zig").AffinePoint;

const Hash = std.crypto.hash.sha2.Sha256;
const Hmac = std.crypto.auth.hmac.Hmac(Hash);

/// Number of bits required to represent an element in the ECDSA field.
const N_ELEMENT_BITS_ECDSA: u256 = @floor(
    @as(
        f128,
        @floatFromInt(std.math.log2(@as(u256, field_constants.STARKNET_PRIME))),
    ),
);

/// Upper bound for elements in the ECDSA field.
/// Calculated as 2^(N_ELEMENT_BITS_ECDSA).
const ELEMENT_UPPER_BOUND = Felt252.fromInt(
    u256,
    std.math.pow(u256, 2, N_ELEMENT_BITS_ECDSA),
);

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

    const EC_ORDER: u256 = 0x0800000000000010ffffffffffffffffb781126dcae7b2321e66a241adc64d2f;

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
        // Check if the message hash is valid.
        // Message hash must be smaller than 2**N_ELEMENT_BITS_ECDSA.
        // Message whose hash is >= 2**N_ELEMENT_BITS_ECDSA cannot be signed.
        // This happens with a very small probability.
        if (message.gte(&comptime ELEMENT_UPPER_BOUND)) return SignError.InvalidMessageHash;

        // Check if the nonce `k` is zero
        if (k.isZero()) return SignError.InvalidK;

        // Compute curve point r = k * G
        const full_r = (comptime CurveParams.GENERATOR).mulByScalarProjective(k);
        const r = full_r.x;

        // Check if r is zero or greater than the maximum field value
        if (r.isZero() or r.gte(&comptime ELEMENT_UPPER_BOUND)) return SignError.InvalidK;

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
        if (s.isZero() or s.gte(&comptime ELEMENT_UPPER_BOUND)) return SignError.InvalidK;

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
        if (message.gte(&comptime ELEMENT_UPPER_BOUND)) return VerifyError.InvalidMessageHash;

        // Check if the 'r' value is zero or exceeds the maximum field value
        if (self.r.isZero() or self.r.gte(&comptime ELEMENT_UPPER_BOUND)) return VerifyError.InvalidR;

        // Check if the 's' value is zero or exceeds the maximum field value
        if (self.s.isZero() or self.s.gte(&comptime ELEMENT_UPPER_BOUND)) return VerifyError.InvalidS;

        // Attempt to convert the provided public key to an affine point
        const full_public_key = AffinePoint.fromX(public_key.*) catch
            return VerifyError.InvalidPublicKey;

        // Calculate the modular inverse of 's' with respect to the EC order
        const w = try self.s.modInverse(CurveParams.EC_ORDER);

        // Check if the modular inverse of 's' is zero or exceeds the maximum field value
        if (w.isZero() or w.gte(&ELEMENT_UPPER_BOUND)) return VerifyError.InvalidS;

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
        if (message.gte(&ELEMENT_UPPER_BOUND)) return RecoverError.InvalidMessageHash;

        // Check if the 'r' value is zero or exceeds the maximum field value
        if (self.r.isZero() or self.r.gte(&ELEMENT_UPPER_BOUND)) return RecoverError.InvalidR;

        // Check if the 's' value is zero or exceeds the maximum field value
        if (self.s.isZero() or self.s.gte(&ELEMENT_UPPER_BOUND)) return RecoverError.InvalidS;

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

    const noise_length: usize = 32;

    // // Create a deterministic scalar according to a secret key and optional noise.
    // // This uses the overly conservative scheme from the "Deterministic ECDSA and EdDSA Signatures with Additional Randomness" draft.
    // fn deterministicScalar(h: [Hash.digest_length]u8, secret_key: Felt252, noise: ?[noise_length]u8, message_hash: Felt252) Felt252 {
    //     var h: [32]u8 = undefined;

    //     const sha = Hash.init(.{});
    //     sha.update(&message_hash.toBytesBe());
    //     sha.final(h[0..]);

    //     var k = [_]u8{0x00} ** h.len;
    //     var m = [_]u8{0x00} ** (h.len + 1 + noise_length + secret_key.len + h.len);
    //     var t = [_]u8{0x00} ** (4 * @sizeOf(u64));
    //     const m_v = m[0..h.len];
    //     const m_i = &m[m_v.len];
    //     const m_z = m[m_v.len + 1 ..][0..noise_length];
    //     const m_x = m[m_v.len + 1 + noise_length ..][0..secret_key.len];
    //     const m_h = m[m.len - h.len ..];

    //     @memset(m_v, 0x01);
    //     m_i.* = 0x00;
    //     if (noise) |n| @memcpy(m_z, &n);
    //     @memcpy(m_x, &secret_key);
    //     @memcpy(m_h, &h);
    //     Hmac.create(&k, &m, &k);
    //     Hmac.create(m_v, m_v, &k);
    //     m_i.* = 0x01;
    //     Hmac.create(&k, &m, &k);
    //     Hmac.create(m_v, m_v, &k);
    //     while (true) {
    //         var t_off: usize = 0;
    //         while (t_off < t.len) : (t_off += m_v.len) {
    //             const t_end = @min(t_off + m_v.len, t.len);
    //             Hmac.create(m_v, m_v, &k);
    //             @memcpy(t[t_off..t_end], m_v[0 .. t_end - t_off]);
    //         }
    //         if (Felt252.fromBytesBe(t)) |s| return s else |_| {}
    //         m_i.* = 0x00;
    //         Hmac.create(&k, m[0 .. m_v.len + 1], &k);
    //         Hmac.create(m_v, m_v, &k);
    //     }
    // }

    // // Create a deterministic scalar according to a secret key and optional noise.
    // // This uses the overly conservative scheme from the "Deterministic ECDSA and EdDSA Signatures with Additional Randomness" draft.
    // fn deterministicScalar(
    //     message_hash: Felt252,
    //     private_key: Felt252,
    //     noise: ?[noise_length]u8,
    // ) Felt252 {
    //     var h: [32]u8 = undefined;
    //     var sha = Hash.init(.{});
    //     sha.update(&message_hash.toBytesBe());
    //     sha.final(&h);

    //     const secret_key = private_key.toBytesBe();

    //     var k = [_]u8{0x00} ** h.len;
    //     var m = [_]u8{0x00} ** (h.len + 1 + noise_length + secret_key.len + h.len);
    //     var t = [_]u8{0x00} ** (4 * @sizeOf(u64));
    //     const m_v = m[0..h.len];
    //     const m_i = &m[m_v.len];
    //     const m_z = m[m_v.len + 1 ..][0..noise_length];
    //     const m_x = m[m_v.len + 1 + noise_length ..][0..secret_key.len];
    //     const m_h = m[m.len - h.len ..];

    //     @memset(m_v, 0x01);
    //     m_i.* = 0x00;
    //     if (noise) |n| @memcpy(m_z, &n);
    //     @memcpy(m_x, &secret_key);
    //     @memcpy(m_h, &h);
    //     Hmac.create(&k, &m, &k);
    //     Hmac.create(m_v, m_v, &k);
    //     m_i.* = 0x01;
    //     Hmac.create(&k, &m, &k);
    //     Hmac.create(m_v, m_v, &k);
    //     while (true) {
    //         var t_off: usize = 0;
    //         while (t_off < t.len) : (t_off += m_v.len) {
    //             const t_end = @min(t_off + m_v.len, t.len);
    //             Hmac.create(m_v, m_v, &k);
    //             @memcpy(t[t_off..t_end], m_v[0 .. t_end - t_off]);
    //         }
    //         // if (Felt252.fromBytesBe(t)) |s| return s else |_| {}

    //         std.debug.print("test dans fonction = {x}\n", .{big_int.fromBytesBe(t).toU256()});

    //         if (!big_int.fromBytesBe(t).isZero() and big_int.fromBytesBe(t).lt(
    //             &big_int.fromInt(
    //                 u256,
    //                 0x0800000000000010ffffffffffffffffb781126dcae7b2321e66a241adc64d2f,
    //             ),
    //         ))
    //             return Felt252.fromBytesBe(t);

    //         m_i.* = 0x00;
    //         Hmac.create(&k, m[0 .. m_v.len + 1], &k);
    //         Hmac.create(m_v, m_v, &k);
    //     }
    // }

    // Create a deterministic scalar according to a secret key and optional noise.
    // This uses the overly conservative scheme from the "Deterministic ECDSA and EdDSA Signatures with Additional Randomness" draft.
    fn deterministicScalarTest() Felt252 {
        // var h: [32]u8 = undefined;
        // var sha = Hash.init(.{});
        // sha.update(&message_hash.toBytesBe());
        // sha.final(&h);

        const h = [32]u8{ 0xAF, 0x2B, 0xDB, 0xE1, 0xAA, 0x9B, 0x6E, 0xC1, 0xE2, 0xAD, 0xE1, 0xD6, 0x94, 0xF4, 0x1F, 0xC7, 0x1A, 0x83, 0x1D, 0x02, 0x68, 0xE9, 0x89, 0x15, 0x62, 0x11, 0x3D, 0x8A, 0x62, 0xAD, 0xD1, 0xBF };
        const private_key = [21]u8{ 0x00, 0x9A, 0x4D, 0x67, 0x92, 0x29, 0x5A, 0x7F, 0x73, 0x0F, 0xC3, 0xF2, 0xB4, 0x9C, 0xBC, 0x0F, 0x62, 0xE8, 0x62, 0x27, 0x2F };
        const q = [21]u8{ 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x01, 0x08, 0xa2, 0xe0, 0xcc, 0x0d, 0x99, 0xf8, 0xa5, 0xef };

        const z1 = std.mem.readInt(u256, &h, .big) >> 93;
        const z2: i256 = z1 - std.mem.readInt(u168, &q, .big);

        const h1: u168 = if (z2 < 0) z1 else z2;

        var seed: [21]u8 = undefined;
        std.mem.writeInt(u168, &seed, h1, .big);

        std.debug.print("test seed = {X}\n", .{seed});

        // const seed = [21]u8{ 0x01, 0x79, 0x5E, 0xDF, 0x0D, 0x54, 0xDB, 0x76, 0x0F, 0x15, 0x6D, 0x0D, 0xAC, 0x04, 0xC0, 0x32, 0x2B, 0x3A, 0x20, 0x42, 0x24 };
        // var t = [_]u8{0x01} ** 21;

        // such that the length of V, in bits, is equal to 8*ceil(hlen/8).
        // For instance, on an octet-based system, if H is SHA-256, then V is set to a sequence of 32 octets of value 1.
        var v = [_]u8{0x01} ** 32;

        // such that the length of K, in bits, is equal to 8*ceil(message_hash_bytes_array/8).
        var k = [_]u8{0x00} ** 32;

        std.debug.print("v debut = {X}\n", .{v});
        std.debug.print("k debut = {X}\n", .{k});

        // Hmac.create(&k, &v, &k);
        // Hmac.create(&k, &[_]u8{0x00}, &k);
        // Hmac.create(&k, &private_key, &k);
        // Hmac.create(&k, &seed, &k);

        // K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1))
        Hmac.create(&k, &(v ++ [_]u8{0x00} ++ private_key ++ seed), &k);

        std.debug.print("k after step d = {X}\n", .{k});

        // V = HMAC_K(V)
        Hmac.create(&v, &v, &k);

        std.debug.print("v after step e = {X}\n", .{v});

        // K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1))
        // Note that the "internal octet" is 0x01 this time.
        Hmac.create(&k, &(v ++ [_]u8{0x01} ++ private_key ++ seed), &k);

        std.debug.print("k after step f = {X}\n", .{k});

        // V = HMAC_K(V)
        Hmac.create(&v, &v, &k);

        std.debug.print("v after step g = {X}\n", .{v});

        // var t_len: usize = 0;

        var i: usize = 0;

        while (true) {
            Hmac.create(&v, &v, &k);

            const t = v;

            std.debug.print("t in while = {X}\n", .{t});

            const k1 = std.mem.readInt(u256, &t, .big) >> (93);
            const qm1 = std.mem.readInt(u168, &q, .big) - 1;

            std.debug.print("k1 in while = {X}\n", .{k1});
            // std.debug.print("qm1 in while = {X}\n", .{q});
            std.debug.print("est ce que k& plus petit que qm1 = {any}\n", .{k1 < qm1});

            i += 1;

            Hmac.create(&k, &(v ++ [_]u8{0x00}), &k);
            Hmac.create(&v, &v, &k);

            if (i == 3) break;
        }

        return .{};
    }

    // Description: This function returns the elliptic curve order as a byte array.
    //
    // Returns:
    //   - [32]u8: The elliptic curve order represented as a byte array.
    //
    // Notes:
    //   - The function computes the elliptic curve order at compile-time.
    //   - The elliptic curve order is converted into a byte array with big-endian representation.
    //
    // Reference: EC_ORDER - The order of the elliptic curve used in cryptographic operations.
    fn getEcOrderAsBytes() [32]u8 {
        comptime {
            var q: [32]u8 = undefined;
            std.mem.writeInt(u256, &q, EC_ORDER, .big);
            return q;
        }
    }

    // Description: This function computes the number of leading zeros in the binary representation of the elliptic curve order.
    //
    // Returns:
    //   - u64: The number of leading zeros in the binary representation of the elliptic curve order.
    //
    // Notes:
    //   - The function computes the number of leading zeros at compile-time using the @clz intrinsic.
    //
    // Reference: EC_ORDER - The order of the elliptic curve used in cryptographic operations.
    fn getEcOrderLeadingZeros() u64 {
        comptime {
            return @clz(EC_ORDER);
        }
    }

    // Description: This function generates a deterministic scalar according to a secret key and optional noise,
    //              following the process described in RFC 6979.
    //
    // Parameters:
    //   - message_hash: Felt252 - The hash of the message to be signed.
    //   - secret_key: Felt252 - The secret key used for signing.
    //   - seed: ?Felt252 - Optional additional randomness (noise) to enhance security.
    //
    // Returns:
    //   - Felt252: The deterministic scalar value suitable for ECDSA or DSA signatures.
    //
    // Notes:
    //   - The function uses HMAC-based Extract-and-Expand Key Derivation Function (HKDF) for deterministic scalar generation.
    //   - The provided secret key and message hash are converted into byte arrays.
    //   - The function initializes V and K according to the specified process.
    //   - If noise is provided, it is incorporated into the HMAC computation.
    //   - The function repeats the process until a proper value for k is found.
    //   - The resulting scalar value is returned as a Felt252.
    //
    // RFC Reference: https://datatracker.ietf.org/doc/html/rfc6979
    //                Section 3.2: Generation of k
    fn deterministicScalar(
        message_hash: Felt252,
        secret_key: Felt252,
        seed: ?Felt252,
    ) Felt252 {
        // Check if noise (seed) is provided, convert it to bytes; otherwise, set it to null.
        const noise = if (seed) |s| s.toBytesBe() else null;

        // Convert the message hash to bytes.
        const h = message_hash.toBytesBe();

        // Convert the secret key to a 256-bit unsigned integer and store it in a byte array.
        var private_key: [32]u8 = undefined;
        std.mem.writeInt(u256, &private_key, secret_key.toU256(), .big);

        // Initialize V as a sequence of octets of value 1, with a length equal to the hash length.
        var v = [_]u8{0x01} ** 32;

        // Initialize K as a sequence of octets of value 0, with a length equal to the hash length.
        var k = [_]u8{0x00} ** 32;

        // Determine the index of the first non-zero byte in the noise array, if noise is provided.
        var first_non_zero_index: usize = 0;
        if (noise) |n| {
            for (n, 0..) |elm, i| {
                if (elm != 0) {
                    first_non_zero_index = i;
                    break;
                }
            }
        }

        // Iterate twice to compute K and V.
        inline for (0..2) |i| {
            if (noise) |n| {
                // Initialize HMAC with K as the key and update it with the concatenation of V, 0x00, private key, h, and noise.
                var hmac = Hmac.init(&k);
                hmac.update(&(v ++ [_]u8{i} ++ private_key ++ h));
                // If noise is provided, update HMAC with the non-zero part of the noise array.
                if (first_non_zero_index != noise_length)
                    hmac.update(n[first_non_zero_index..]);
                // Finalize HMAC to compute the new value of K.
                hmac.final(&k);
            } else {
                // If noise is not provided, directly compute K using HMAC with the concatenation of V, 0x00, private key, and h.
                Hmac.create(&k, &(v ++ [_]u8{i} ++ private_key ++ h), &k);
            }
            // Update V using HMAC with K.
            Hmac.create(&v, &v, &k);
        }

        // Repeat the process until a proper value for k is found.
        while (true) {
            // Update V using HMAC with K.
            // Compute V = HMAC_K(V)
            Hmac.create(&v, &v, &k);
            // Convert a portion of V to an integer, considering leading zeros based on EC order.
            const k1 = std.mem.readInt(u256, &v, .big) >> comptime getEcOrderLeadingZeros();
            // If k1 is within the valid range and not 0, return it as a Felt252.
            if (k1 != 0 and k1 < EC_ORDER - 1) return Felt252.fromInt(u256, k1);
            // If k1 is not suitable, update K and V and repeat the process.
            // Compute K = HMAC_K(V || 0x00)
            Hmac.create(&k, &(v ++ [_]u8{0x00}), &k);
            // Compute V = HMAC_K(V)
            Hmac.create(&v, &v, &k);
        }
    }
};

/// An ECDSA key pair.
pub const KeyPair = struct {
    const Self = @This();

    /// Public part.
    public_key: Felt252,
    /// Secret scalar.
    private_key: Felt252,

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
    pub fn fromSecretKey(private_key: *const Felt252) Self {
        // Scalar multiply the base generator point by the private key and return the x-coordinate.
        return .{
            .private_key = private_key.*,
            .public_key = CurveParams.GENERATOR.mulByScalarProjective(private_key).x,
        };
    }
};

// Test cases ported from:
//   https://github.com/starkware-libs/crypto-cpp/blob/95864fbe11d5287e345432dbe1e80dea3c35fc58/src/starkware/crypto/ffi/crypto_lib_test.go

test "getPublicKey: test with precomputed keys" {
    // Precomputed keys can be found here:
    // https://github.com/starkware-libs/starkex-for-spot-trading/blob/master/src/starkware/crypto/starkware/crypto/signature/src/config/keys_precomputed.json
    const private_keys = [_]u256{
        0x1,
        0x2,
        0x3,
        0x4,
        0x5,
        0x6,
        0x7,
        0x8,
        0x9,
        0x800000000000000000000000000000000000000000000000000000000000000,
        0x800000000000000000000000000000000000000000000000000000000000001,
        0x800000000000000000000000000000000000000000000000000000000000002,
        0x800000000000000000000000000000000000000000000000000000000000003,
        0x800000000000000000000000000000000000000000000000000000000000004,
        0x800000000000000000000000000000000000000000000000000000000000005,
        0x800000000000000000000000000000000000000000000000000000000000006,
        0x800000000000000000000000000000000000000000000000000000000000007,
        0x800000000000000000000000000000000000000000000000000000000000008,
        0x800000000000000000000000000000000000000000000000000000000000009,
        0x2e9c99d8382fa004dcbbee720aef8a97002de0e991f6a8344e6dc636a71b59e,
        0x8620458785138df8722214e073a91b8f55076ea78197cf41007692dd27fd90,
        0x1b920e7dfb49ba5ada673882af5342e7448d3e9335e0ac37feb6280cd7289ce,
        0x704170dbfd5dc63caef69d2ce6dfc2b2dbb2af6e75851242bbe79fb6e62a118,
        0x4b58bf4228f39550eca59b5c96a0cb606036cc9495eef9a546f24f01b1b7829,
        0x2e93226c90fb7a2381a24e940a94b98433e3553dcbf745d3f54d62963c75604,
        0x4615f94598cd756ad1a551d7e57fd725916adfd0054eb773ceb482eef87d0b2,
        0x6ade54b7debd7ca1d4e8e932f9545f8fa4024d73be1efcc86df86367fc333f8,
        0x618e7467dd24c2a3449c4df640439c12cdd0f8ea779afcee6e252b2cf494354,
        0x7eae185e1f41ec76d214d763f0592f194933622a9dd5f3d52d0209f71619c1a,
        0x178047D3869489C055D7EA54C014FFB834A069C9595186ABE04EA4D1223A03F,
    };

    const expected_public_keys = [_]u256{
        0x1ef15c18599971b7beced415a40f0c7deacfd9b0d1819e03d723d8bc943cfca,
        0x759ca09377679ecd535a81e83039658bf40959283187c654c5416f439403cf5,
        0x411494b501a98abd8262b0da1351e17899a0c4ef23dd2f96fec5ba847310b20,
        0xa7da05a4d664859ccd6e567b935cdfbfe3018c7771cb980892ef38878ae9bc,
        0x788435d61046d3eec54d77d25bd194525f4fa26ebe6575536bc6f656656b74c,
        0x1efc3d7c9649900fcbd03f578a8248d095bc4b6a13b3c25f9886ef971ff96fa,
        0x743829e0a179f8afe223fc8112dfc8d024ab6b235fd42283c4f5970259ce7b7,
        0x6eeee2b0c71d681692559735e08a2c3ba04e7347c0c18d4d49b83bb89771591,
        0x216b4f076ff47e03a05032d1c6ee17933d8de8b2b4c43eb5ad5a7e1b25d3849,
        0x5c79074e7f7b834c12c81a9bb0d46691a5e7517767a849d9d98cb84e2176ed2,
        0x1c4f24e3bd16db0e2457bc005a9d61965105a535554c6b338871e34cb8e2d3a,
        0xdfbb89b39288a9ddacf3942b4481b04d4fa2f8ed3c424757981cc6357f27ac,
        0x41bef28265fd750b102f4f2d1e0231de7f4a33900a214f191a63d4fec4e72f4,
        0x24de66eb164797d4b414e81ded0cfa1a592ef0a9363ebbcb440d4d03cb18af1,
        0x5efb18c3bc9b69003746acc85fb6ee0cfbdc6adfb982f089cc63e1e5495daad,
        0x10dc71f00918a8ebfe4085c834d41dd22b251b9f81eef8b9a4fab77e7e1afe9,
        0x4267ebfd379b1c8caae73febc5920b0c95bd6f9f3536f47c5ddad1259c332ff,
        0x6da515118c8e01fd5b2e96b814ee95bad7d60be4d2ba6b47e0d283f579d9671,
        0x7a5b4797f4e56ed1473876bc2693fbe3f2fef7e050717cbae924ff23d426052,
        0x1ff6803ae740e7e596504ac5c6afbea472e53679361e214f12be0155b13e25d,
        0x5967da40b90d7ca1e36dc4024381d7d4b403c6ac1a0ab358b0743984934a805,
        0x78c7ab46333968fbde3201cf512c1eeb5529360259072c459a158dee4449b57,
        0x534bd8d6ebe4bb2f6992e2d7c19ef3146247e10c2849f357e44eddd283b2af6,
        0x1097a8c5a46d94596f1c8e70ca66941f2bb11e3c8d4fd58fdc4589f09965be8,
        0x369f0e8c8e984f244290267393a004dba435a4df091767ad5063fece7b1884c,
        0x1ee5b8d612102a2408cde59ce52a6498d2e38fe8789bb26d400dea310684ec9,
        0x37de3bf52412b2fb9b0030d232ca9dd921cd8f71fd67975cdc62546826e121,
        0x71c2b578c432f2d305d3808bb645ecc46dd670cb43d4f4a076f75ccbff74fbc,
        0x2b0160052e70176e5b0ff2a6eff90896ae07b732fc27219e36e077735abd57e,
        0x1895a6a77ae14e7987b9cb51329a5adfb17bd8e7c638f92d6892d76e51cebcf,
    };

    for (private_keys, expected_public_keys) |private_key, public_key| {
        const k1 = Felt252.fromInt(u256, private_key);
        const k2 = Felt252.fromInt(u256, public_key);
        try expectEqual(
            KeyPair{ .private_key = k1, .public_key = k2 },
            KeyPair.fromSecretKey(&k1),
        );
    }
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
    const key_pair = KeyPair.fromSecretKey(&private_key);

    // Verify that the signature is valid for the provided public key and message hash
    try expect(try signature.verify(&key_pair.public_key, &message_hash));
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
    try expectEqual(
        KeyPair.fromSecretKey(&private_key).public_key,
        try signature.recover(&message_hash),
    );
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

test "Signature: generate deterministic scalar padded" {
    const data =
        [_]struct { message_hash: Felt252, private_key: Felt252, seed: ?Felt252, k: Felt252 }{
        .{
            .message_hash = Felt252.fromInt(u256, 0x010b559a3b4dc1b7137d90521cb413b397ff07963214d128a92d65aec7182f68),
            .private_key = Felt252.fromInt(u256, 0x07e3184f4bef18f371bc53fc412dff1b30dbc94f758490fb8e2349bae647a642),
            .seed = Felt252.fromInt(u256, 0x03fe27199aaad4e700559e2436a919f4de70def585a6deb2f4c087fdf6a27c1b),
            .k = Felt252.fromInt(u256, 0x00514de5048c11bf01f3dc98a131e0a3fde03d6269cdfab69d944c8281149184),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x058a8fc2bed05af3ae202f0ea4f6e724b6d3b1034382c7a2e1a3a06bd48bf7ea),
            .private_key = Felt252.fromInt(u256, 0x00efacf45682998e4748e853f13a789b4729be197353eb1b8063fd425e0576f8),
            .seed = Felt252.fromInt(u256, 0x05a595cc1e2dcdb26e2ee3964aaa55090bff0c02be6980f098669bc8c87fb994),
            .k = Felt252.fromInt(u256, 0x0610bd4aec3a26b00331daee8baefc2ad9c94eab42d21384851a1c4fcd5c0483),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x02de2f0d139af136ef15a5ccf8139724131ff6000034be37e281b37a33b06ed7),
            .private_key = Felt252.fromInt(u256, 0x01d2cb8a451ddbe6d0d2f193cf384c275e919e18aeb4aa09e39c2236dd5d4121),
            .seed = Felt252.fromInt(u256, 0x033fe7b36cb79df110f92739f13fcf9c1a9ed9f80dba80a724f73055d763eb94),
            .k = Felt252.fromInt(u256, 0x06019bb42abee70ad655cf5135f35a6fa38ccfa7823abd238e5742d979dcd470),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x05379d4cabb167483ffeeec5463452a021092773ae2d3c9fa639e501cbd337cb),
            .private_key = Felt252.fromInt(u256, 0x062465a3562e57a73e4fbdbc3dc4c7b14138258639a276410fbc553d951f498e),
            .seed = Felt252.fromInt(u256, 0x0603a421b6a665a83efcba9bff5361d728ae96096e3305b0a17df896b54c3832),
            .k = Felt252.fromInt(u256, 0x00c1bc03501b4c521310a5f47f020899f63079d20268126ebf5237c4fe40cc06),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x0605b776d195609f6ed6ebacb20efb1859b7c827abfa9743c4541e1eb48f1c2d),
            .private_key = Felt252.fromInt(u256, 0x00a13a4fa63b534583089df4d6f5ff74ca3cbc2679c4161e076969803cae1aac),
            .seed = Felt252.fromInt(u256, 0x0104c78975779c741a5a5c0a6f5edc8841f570ded6a1c5c519ab0f963ec64c0a),
            .k = Felt252.fromInt(u256, 0x07badb8d84631f6bd418e5eaa46e9b09c083fa607c879e881cf5c31923520e3a),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x01856e6d1c3ce0a34ab04992b4a8d8d9ef756a4044bfc0a5f8068013f829ee17),
            .private_key = Felt252.fromInt(u256, 0x01e20f779df440c3fca66a3ede6f43c68ba60222b23f893854f55c5138c77a1c),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x01bdbdc2db77b6dad0c9bdaca20acb5a78a61200c711cc2dcaeebcb86f9ef1ca),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x0438e872bae2e39e148ab372c6aa4506602d9d0f0acca48dfa853e858e38a8aa),
            .private_key = Felt252.fromInt(u256, 0x02d50c10d13ecf299d6bccea372efd6b0212208fd5f04cca66e5072d89b9bc2f),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x051a3dd43ef8e85094c95ca1d6d5f4cbd5a2c8253466d558a815dde2bae17b76),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x0470d8bd5f6640bbae27a997f5da4493953a2f6c2aacb7ac3a26cfe810738470),
            .private_key = Felt252.fromInt(u256, 0x01af592805ccb005eed4ce5b1997193c7446786b1d8c3cdc9fb30b84ea084cd6),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x004e29ac94c51097d4ee87d4bf9bcfc33ca29518f73e972e725f851ada274a57),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x04d85b6e736dd4aa07a8b1222819585f99e122a09f7e9c77e22da288f9c893b0),
            .private_key = Felt252.fromInt(u256, 0x046dda98ddd7337b4f6248795aedbc2e1b192466356ab8f61ee25317500e3a22),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x014ee0f4a9e8b4f98d48d47993788d8485ded1eca3c894c8501b31dbcd8190e5),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x03fcafdbc49c1b8ff00ad5884db731a643899a2010169481203e9a4aab0545f3),
            .private_key = Felt252.fromInt(u256, 0x02bb48d586e127c86a3a4e6b831a99bac5a9adf0e3974bc629c43a12f52fb488),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x0052218bd1d5447347793972e5d40800a45cc91794746533164827e6f3ce8250),
        },
    };

    for (data) |d| {
        try expectEqual(
            d.k,
            Signature.deterministicScalar(
                d.message_hash,
                d.private_key,
                d.seed,
            ),
        );
    }
}

test "Signature: generate deterministic scalar non padded" {
    const data =
        [_]struct { message_hash: Felt252, private_key: Felt252, seed: ?Felt252, k: Felt252 }{
        .{
            .message_hash = Felt252.fromInt(u256, 0x0080977da1148412a7976215729d396b72aec9e955498757a7b859281354b4b1),
            .private_key = Felt252.fromInt(u256, 0x03fa56dcdbe2fb6769a83786469faf589a3d1e31c66db8b0432f741a38cdeed1),
            .seed = Felt252.fromInt(u256, 0x0776cc1aa4c66417a4923768b9d4a7cfca731e862e4972ed930d8f2ad45d352b),
            .k = Felt252.fromInt(u256, 0x0013480c97bb5861404aa16e1f97a99411ba8f4039b2d54de839dea5c9f0af47),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x00acf1ce22cb1f49d4fc7a6df93cd290d28f4c5a27888c9624b07cfa193de992),
            .private_key = Felt252.fromInt(u256, 0x06ad6342c62315862f51722808d2764a60824f9c5894105dffbb6478cfb06a95),
            .seed = Felt252.fromInt(u256, 0x01314de4fcf69889ea0cdf4aefd1cc7732d1dfbdc6476066e3132c1609756bd0),
            .k = Felt252.fromInt(u256, 0x0687b462764b919fabefcb84fe77a4eae838f45b97f49b2d24fec995ff482c04),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x0020791e67f0d6083d406a3a0fdaf8f4008fc1c6616dc97c1e1fdda352030e2f),
            .private_key = Felt252.fromInt(u256, 0x06e18a4a890962776c397e3ddf659b07275995a341e32bb75cd5a3bff55cfe7b),
            .seed = Felt252.fromInt(u256, 0x0506b182cf3d46d6a7918ed4dfcced8f46c09a44c68067b3b40f2d82bee65e1a),
            .k = Felt252.fromInt(u256, 0x02cc9d2484afa0569b44487cf1705906db0a4cb78d9f73426efaaa572a5d47bb),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x006243fd868f3e5b1852a9bda7a93780405cd05e5809904837398343c649c863),
            .private_key = Felt252.fromInt(u256, 0x0752543710a5075733d597329ff9ef354a2d4a36dbf769a6293a4fd0082026be),
            .seed = Felt252.fromInt(u256, 0x06a7c98da9ea1f2abd105b5cf6722f0d03efadb60891b8d58c79c7a9fc2649a2),
            .k = Felt252.fromInt(u256, 0x02e701fb8707ecd930bea12f9761cfedd9f559d1706a104d3f529d4f7b43223a),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x00b3b40642edd4d2e4c7c60310c55b9e99bcb64b57b05ccd3d4062b6caa10bfc),
            .private_key = Felt252.fromInt(u256, 0x05a1e54cd91afff6b1797ad6244a93380cd530f05eda201b9b25d52da61fbcb2),
            .seed = Felt252.fromInt(u256, 0x00343ace243e3236520d132a07a6bdd757f743e5a4901e7b5d60b72c3f9450af),
            .k = Felt252.fromInt(u256, 0x05bb9f6160e41bd0887b58c40c90060a32569de14dcab341426b16bdf4d9dd94),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x006c663dc46f1f680f32ef5f3f4fe71c5a0488c7fd2500eeee29cbaa3e4231e3),
            .private_key = Felt252.fromInt(u256, 0x013a6f2b21a9344b51635f16da58573f69c7d09ec20769ec9b481629ea9ec485),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x02d59476386604375e958f2ee7f07446d1861a4ceb92eb393009b1c72db308a7),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x006c846f23ae7941f843c53cf86004e0addb8974bdfc5d051035edbfd3dcf836),
            .private_key = Felt252.fromInt(u256, 0x0562bb91276d2463e3186631dcff433169e99592639e0df9f358c56437e90c9a),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x076e1465a3753e7b1139223d9f68880c6192cd19f68b2a1c43b34b7aaa8cab16),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x00539c45625f25004f965082e1e7f5a837f4eee253c915a95f00503fcdfb2c35),
            .private_key = Felt252.fromInt(u256, 0x05f4dddfc752dd28e72f498c7c0298a42fa6cfef14db2c3bdd798c6ca5b1497b),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x06054d0413882a9798127d5760d61dc9e3e940b11ccc353deb33ef4ca58ccf34),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x0050b1346abe44d73084f557fc88f209ae4aadff253bb23b4212f859076f8755),
            .private_key = Felt252.fromInt(u256, 0x0580cf0b0db0ffb7b792b61d6d3da583210b320337a9222ab4208aae78ce4963),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x052b8601d62662702ed36ee1440d1f76ef814193d206218e436ccd3aae25451e),
        },
        .{
            .message_hash = Felt252.fromInt(u256, 0x0054077f197503c09c1265254398f57fb79f3a4f6a5a143cf871d58eeb5a5729),
            .private_key = Felt252.fromInt(u256, 0x07e69dd5b7cf548d598650be2ab3a8ebc038a5877a592d35a1cafa7249ef7fc4),
            .seed = null,
            .k = Felt252.fromInt(u256, 0x07af7d6cf50798dd5fa6e5731394d7d33f16dd57cca4169d63256a2b42179649),
        },
    };

    for (data) |d| {
        try expectEqual(
            d.k,
            Signature.deterministicScalar(
                d.message_hash,
                d.private_key,
                d.seed,
            ),
        );
    }
}
