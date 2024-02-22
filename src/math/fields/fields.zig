const std = @import("std");
const builtin = @import("builtin");
const ArrayList = std.ArrayList;

const tonelliShanks = @import("./helper.zig").tonelliShanks;
const extendedGCD = @import("./helper.zig").extendedGCD;
const arithmetic = @import("./arithmetic.zig");

pub const ModSqrtError = error{
    InvalidInput,
};

// // Modulus in non Montgomery format
// const MODULUS_NON_MONT = [4]u64{ 1, 0, 0, 576460752303423505 };

/// Represents a finite field element.
pub fn Field(comptime F: type, comptime modulo: u256) type {
    return struct {
        const Self = @This();

        // Reprensentation of - modulus^{-1} mod 2^{64}
        pub const Inv: u64 = 0xffffffffffffffff;
        // One before the modulus
        pub const MaxField: Self = .{ .fe = .{ 32, 0, 0, 544 } };
        // Modulus in non Montgomery format
        pub const Modulus: Self = .{ .fe = .{ 1, 0, 0, 576460752303423505 } };
        /// Number of bits needed to represent a field element with the given modulo.
        pub const BitSize = @bitSizeOf(u256) - @clz(modulo);
        /// Number of bytes required to store a field element.
        pub const BytesSize = @sizeOf(u256);
        /// The modulo value representing the finite field.
        pub const Modulo = modulo;
        /// Half of the modulo value (Modulo - 1) divided by 2.
        pub const QMinOneDiv2 = (Modulo - 1) / 2;
        /// The number of bits in each limb (typically 64 for u64).
        pub const Bits: usize = 64;
        /// Bit mask for the last limb.
        pub const Mask: u64 = mask(Bits);
        /// Number of limbs used to represent a field element.
        pub const Limbs: usize = 4;
        /// The smallest value that can be represented by this integer type.
        pub const Min = Self.zero();
        /// The largest value that can be represented by this integer type.
        pub const Max: Self = .{
            .fe = .{
                std.math.maxInt(u64),
                std.math.maxInt(u64),
                std.math.maxInt(u64),
                std.math.maxInt(u64),
            },
        };

        fe: F.MontgomeryDomainFieldElement,

        /// Mask to apply to the highest limb to get the correct number of bits.
        pub fn mask(bits: usize) u64 {
            return switch (bits) {
                0 => 0,
                else => switch (@mod(bits, 64)) {
                    0 => std.math.maxInt(u64),
                    else => |b| std.math.shl(u64, 1, b) - 1,
                },
            };
        }

        /// Creates a `Field` element from an integer of type `T`. The resulting field element is
        /// in Montgomery form. This function handles conversion for integers of various sizes,
        /// ensuring compatibility with the defined finite field (`Field`) and its modulo value.
        ///
        /// # Arguments:
        /// - `T`: The type of the integer value.
        /// - `num`: The integer value to create the `Field` element from.
        ///
        /// # Returns:
        /// A new `Field` element in Montgomery form representing the converted integer.
        pub fn fromInt(comptime T: type, num: T) Self {
            var mont: F.MontgomeryDomainFieldElement = undefined;
            std.debug.assert(num >= 0);
            switch (@typeInfo(T).Int.bits) {
                0...63 => F.toMontgomery(&mont, [_]u64{ @intCast(num), 0, 0, 0 }),
                64 => F.toMontgomery(&mont, [_]u64{ num, 0, 0, 0 }),
                65...128 => F.toMontgomery(
                    &mont,
                    [_]u64{
                        @truncate(
                            @mod(
                                num,
                                @as(u128, @intCast(std.math.maxInt(u64))) + 1,
                            ),
                        ),
                        @truncate(
                            @divTrunc(
                                num,
                                @as(u128, @intCast(std.math.maxInt(u64))) + 1,
                            ),
                        ),
                        0,
                        0,
                    },
                ),
                else => {
                    var lbe: [BytesSize]u8 = [_]u8{0} ** BytesSize;
                    std.mem.writeInt(
                        u256,
                        lbe[0..],
                        num % Modulo,
                        .little,
                    );
                    var nonMont: F.NonMontgomeryDomainFieldElement = undefined;
                    F.fromBytes(
                        &nonMont,
                        lbe,
                    );
                    F.toMontgomery(
                        &mont,
                        nonMont,
                    );
                },
            }

            return .{ .fe = mont };
        }

        /// Get the field element representing zero.
        ///
        /// Returns a field element with a value of zero.
        pub inline fn zero() Self {
            return .{ .fe = [4]u64{ 0, 0, 0, 0 } };
        }

        /// Get the field element representing one.
        ///
        /// Returns a field element with a value of one.
        pub inline fn one() Self {
            return .{
                .fe = [4]u64{
                    18446744073709551585,
                    18446744073709551615,
                    18446744073709551615,
                    576460752303422960,
                },
            };
        }

        /// Get the field element representing two.
        ///
        /// Returns a field element with a value of two.
        pub inline fn two() Self {
            return .{
                .fe = [4]u64{
                    18446744073709551553,
                    18446744073709551615,
                    18446744073709551615,
                    576460752303422416,
                },
            };
        }

        /// Get the field element representing three.
        ///
        /// Returns a field element with a value of three.
        pub inline fn three() Self {
            return .{
                .fe = [4]u64{
                    18446744073709551521,
                    18446744073709551615,
                    18446744073709551615,
                    576460752303421872,
                },
            };
        }

        /// Create a field element from a byte array.
        ///
        /// Converts a byte array into a field element in Montgomery representation.
        pub fn fromBytes(bytes: [BytesSize]u8) Self {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            inline for (0..4) |i| {
                non_mont[i] = std.mem.readInt(
                    u64,
                    bytes[i * 8 .. (i + 1) * 8],
                    .little,
                );
            }
            var ret: Self = undefined;
            F.toMontgomery(&ret.fe, non_mont);

            return ret;
        }

        /// Create a field element from a byte array.
        ///
        /// Converts a byte array into a field element in Montgomery representation.
        pub fn fromBytesBe(bytes: [BytesSize]u8) Self {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            inline for (0..4) |i| {
                non_mont[3 - i] = std.mem.readInt(
                    u64,
                    bytes[i * 8 .. (i + 1) * 8],
                    .big,
                );
            }
            var ret: Self = undefined;
            F.toMontgomery(&ret.fe, non_mont);

            return ret;
        }

        /// Convert the field element to a bits little endian array.
        ///
        /// This function converts the field element to a byte array for serialization.
        pub fn toBitsLe(self: Self) [@bitSizeOf(u256)]u1 {
            var bits = [_]u1{0} ** @bitSizeOf(u256);
            const nmself = self.fromMontgomery();

            inline for (0..4) |ind_element| {
                inline for (0..64) |ind_bit| {
                    bits[ind_element * 64 + ind_bit] = @intCast(
                        (nmself[ind_element] >> ind_bit) & 1,
                    );
                }
            }

            return bits;
        }

        pub fn toBitsBe(self: Self) [@bitSizeOf(u256)]u1 {
            var bits_le = self.toBitsLe();
            std.mem.reverse(u1, &bits_le);
            return bits_le;
        }

        /// Convert the field element to a byte array.
        ///
        /// This function converts the field element to a byte array for serialization.
        pub fn toBytes(self: Self) [BytesSize]u8 {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            F.fromMontgomery(&non_mont, self.fe);
            var ret: [BytesSize]u8 = undefined;
            inline for (0..4) |i| {
                std.mem.writeInt(
                    u64,
                    ret[i * 8 .. (i + 1) * 8],
                    non_mont[i],
                    .little,
                );
            }

            return ret;
        }

        /// Convert the field element to a big-endian byte array.
        ///
        /// This function converts the field element to a big-endian byte array for serialization.
        pub fn toBytesBe(self: Self) [BytesSize]u8 {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            F.fromMontgomery(&non_mont, self.fe);
            var ret: [BytesSize]u8 = undefined;
            inline for (0..4) |i| {
                std.mem.writeInt(
                    u64,
                    ret[i * 8 .. (i + 1) * 8],
                    non_mont[3 - i],
                    .big,
                );
            }

            return ret;
        }

        /// Get the min number of bits needed to field element.
        ///
        /// Returns number of bits needed.
        pub fn numBits(self: Self) u64 {
            const nmself = self.fromMontgomery();
            inline for (0..4) |i| {
                if (nmself[3 - i] != 0)
                    return (4 - i) * @bitSizeOf(u64) - @clz(nmself[3 - i]);
            }

            return 0;
        }

        /// Check if the field element is lexicographically largest.
        ///
        /// Determines whether the field element is larger than half of the field's modulus.
        pub fn lexographicallyLargest(self: Self) bool {
            return self.toInt() > QMinOneDiv2;
        }

        /// Convert the field element to its non-Montgomery representation.
        ///
        /// Converts a field element from Montgomery form to non-Montgomery representation.
        pub fn fromMontgomery(self: Self) F.NonMontgomeryDomainFieldElement {
            var nonMont: F.NonMontgomeryDomainFieldElement = undefined;
            F.fromMontgomery(&nonMont, self.fe);
            return nonMont;
        }

        /// Add two field elements.
        ///
        /// Adds the current field element to another field element.
        pub fn add(self: Self, rhs: Self) Self {
            var ret: F.NonMontgomeryDomainFieldElement = undefined;
            F.add(&ret, self.fe, rhs.fe);
            return .{ .fe = ret };
        }

        /// Double a field element.
        ///
        /// Adds the current field element to itself.
        pub fn double(self: Self) Self {
            var ret: F.NonMontgomeryDomainFieldElement = undefined;
            F.add(&ret, self.fe, self.fe);
            return .{ .fe = ret };
        }

        /// Calculating mod sqrt
        /// TODO: add precomution?
        pub fn sqrt(self: Self) ?Self {
            const v = tonelliShanks(
                @intCast(self.toInt()),
                @intCast(modulo),
            );
            return if (v[2]) Self.fromInt(u256, @intCast(v[0])) else null;
        }

        /// Subtract one field element from another.
        ///
        /// Subtracts another field element from the current field element.
        pub fn sub(self: Self, rhs: Self) Self {
            var ret: F.MontgomeryDomainFieldElement = undefined;
            F.sub(&ret, self.fe, rhs.fe);
            return .{ .fe = ret };
        }

        pub fn mod(self: Self, rhs: Self) Self {
            return Self.fromInt(
                u256,
                @mod(self.toInt(), rhs.toInt()),
            );
        }

        // multiply two field elements and return the result modulo the modulus
        // support overflowed multiplication
        pub fn mulModFloor(
            self: Self,
            rhs: Self,
            modulus: Self,
        ) Self {
            const s: u512 = @intCast(self.toInt());
            const o: u512 = @intCast(rhs.toInt());
            const m: u512 = @intCast(modulus.toInt());

            return Self.fromInt(u256, @intCast((s * o) % m));
        }

        pub fn mul(self: *const Self, rhs: *const Self) Self {
            var a = self.*;
            a.mulAssign(rhs);
            return a;
        }

        pub fn mulAssign(self: *Self, rhs: *const Self) void {
            var r = [_]u64{0} ** 4;

            inline for (0..4) |i| {
                var carry1: u64 = 0;
                r[0] = arithmetic.mac(r[0], self.fe[0], rhs.fe[i], &carry1);

                const k: u64 = r[0] *% comptime Self.Inv;
                var carry2: u64 = 0;
                arithmetic.macDiscard(r[0], k, comptime Self.Modulus.fe[0], &carry2);

                inline for (1..4) |j| {
                    r[j] = arithmetic.macWithCarry(r[j], self.fe[j], rhs.fe[i], &carry1);
                    r[j - 1] = arithmetic.macWithCarry(r[j], k, Self.Modulus.fe[j], &carry2);
                }

                r[3] = carry1 + carry2;
            }

            self.*.fe = r;

            F.subtractModulus(&self.fe);
        }

        pub fn mulTest(self: Self, rhs: Self) Self {
            var ret: F.MontgomeryDomainFieldElement = undefined;
            F.mulTest(&ret, self.fe, rhs.fe);
            return .{ .fe = ret };
        }

        /// Multiply a field element by 5.
        ///
        /// Multiplies the current field element by the constant 5.
        pub fn mulBy5(self: Self) Self {
            var ret: F.MontgomeryDomainFieldElement = undefined;
            F.add(&ret, self.fe, self.fe);
            F.add(&ret, ret, ret);
            F.add(&ret, ret, self.fe);
            return .{ .fe = ret };
        }

        /// Negate a field element.
        ///
        /// Negates the value of the current field element.
        pub fn neg(self: Self) Self {
            var ret: F.MontgomeryDomainFieldElement = undefined;
            F.sub(&ret, Self.zero().fe, self.fe);
            return .{ .fe = ret };
        }

        /// Check if the field element is zero.
        ///
        /// Determines if the current field element is equal to zero.
        pub fn isZero(self: Self) bool {
            return self.eql(Self.zero());
        }

        /// Check if the field element is one.
        ///
        /// Determines if the current field element is equal to one.
        pub fn isOne(self: Self) bool {
            return self.eql(one());
        }

        pub fn modInverse(operand: Self, modulus: Self) !Self {
            const ext = extendedGCD(@bitCast(operand.toInt()), @bitCast(modulus.toInt()));

            if (ext.gcd != 1) {
                @panic("GCD must be one");
            }

            const result = if (ext.x < 0)
                ext.x + @as(i256, @bitCast(modulus.toInt()))
            else
                ext.x;

            return Self.fromInt(u256, @bitCast(result));
        }

        /// Calculate the square of a field element.
        ///
        /// Computes the square of the current field element.
        pub fn square(self: Self) Self {
            var ret: F.MontgomeryDomainFieldElement = undefined;
            F.square(&ret, self.fe);
            return .{ .fe = ret };
        }

        /// Raise a field element to a power of 2.
        ///
        /// Computes the current field element raised to the power of 2 to the `exponent` power.
        /// The result is equivalent to repeatedly squaring the field element.
        pub fn pow2(self: Self, comptime exponent: u8) Self {
            var ret = self;
            inline for (exponent) |_| ret = ret.mul(&ret);
            return ret;
        }

        /// Raise a field element to a general power.
        ///
        /// Computes the field element raised to a general power specified by the `exponent`.
        pub fn pow(self: Self, exponent: u256) Self {
            var res = one();
            var exp = exponent;
            var base = self;

            while (exp > 0) : (exp /= 2) {
                if (exp & 1 == 1) res = res.mul(&base);
                base = base.mul(&base);
            }
            return res;
        }

        /// Bitand operation
        pub fn bitAnd(self: Self, rhs: Self) Self {
            return Self.fromInt(u256, self.toInt() & rhs.toInt());
        }

        /// Batch inversion of multiple field elements.
        ///
        /// Performs batch inversion of a slice of field elements in place.
        pub fn batchInv(out: []Self, in: []const Self) !void {
            std.debug.assert(out.len == in.len);

            var acc = one();
            for (0..in.len) |i| {
                out[i] = acc;
                acc = acc.mul(&in[i]);
            }
            acc = acc.inv() orelse return error.CantInvertZeroElement;
            for (0..in.len) |i| {
                out[in.len - i - 1] = out[in.len - i - 1].mul(&acc);
                acc = acc.mul(&in[in.len - i - 1]);
            }
        }

        pub fn rand(r: std.Random) Self {
            return Self.fromInt(u256, r.int(u256));
        }

        /// Calculate the multiplicative inverse of a field element.
        ///
        /// Computes the multiplicative inverse of the current field element.
        pub fn inv(self: Self) ?Self {
            var r: u256 = Modulo;
            var t: i512 = 0;

            var newr: u256 = self.toInt();
            var newt: i512 = 1;

            while (newr != 0) {
                const quotient = r / newr;
                const tempt = t - quotient * newt;
                const tempr = r - quotient * newr;

                r = newr;
                t = newt;
                newr = tempr;
                newt = tempt;
            }

            // Not invertible
            if (r > 1) return null;

            if (t < 0) t = t + Modulo;

            return Self.fromInt(u256, @intCast(t));
        }

        /// Divide one field element by another.
        ///
        /// Divides the current field element by another field element.
        pub fn div(self: Self, den: Self) !Self {
            return self.mul(&(den.inv() orelse return error.DivisionByZero));
        }

        /// Check if two field elements are equal.
        ///
        /// Determines whether the current field element is equal to another field element.
        pub fn eql(self: Self, rhs: Self) bool {
            return std.mem.eql(u64, &self.fe, &rhs.fe);
        }

        /// Convert the field element to a u256 integer.
        ///
        /// Converts the field element to a u256 integer.
        pub fn toInt(self: Self) u256 {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            F.fromMontgomery(&non_mont, self.fe);

            var bytes: [BytesSize]u8 = [_]u8{0} ** BytesSize;
            F.toBytes(&bytes, non_mont);

            return std.mem.readInt(
                u256,
                &bytes,
                std.builtin.Endian.little,
            );
        }

        /// Try to convert the field element to a u64 if its value is small enough.
        ///
        /// Attempts to convert the field element to a u64 if its value is within the representable range.
        pub fn toU64(self: Self) !u64 {
            const asU256 = self.toInt();
            // Check if the value is small enough to fit into a u64
            if (asU256 > std.math.maxInt(u64)) return error.ValueTooLarge;

            // Otherwise, it's safe to cast
            return @intCast(asU256);
        }

        /// Calculate the Legendre symbol of a field element.
        ///
        /// Computes the Legendre symbol of the field element using Euler's criterion.
        pub fn legendre(a: Self) i2 {
            // Compute the Legendre symbol a|p using
            // Euler's criterion. p is a prime, a is
            // relatively prime to p (if p divides
            // a, then a|p = 0)
            // Returns 1 if a has a square root modulo
            // p, -1 otherwise.
            const ls = a.pow(comptime QMinOneDiv2);

            if (ls.toInt() == comptime Modulo - 1) return -1;

            if (ls.isZero()) return 0;

            return 1;
        }

        /// Compare two field elements and return the ordering result.
        ///
        /// # Parameters
        /// - `self` - The first field element to compare.
        /// - `rhs` - The second field element to compare.
        ///
        /// # Returns
        /// A `std.math.Order` enum indicating the ordering relationship.
        pub fn cmp(self: Self, rhs: Self) std.math.Order {
            var a_non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            var b_non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            F.fromMontgomery(&a_non_mont, self.fe);
            F.fromMontgomery(&b_non_mont, rhs.fe);
            _ = std.mem.reverse(u64, a_non_mont[0..]);
            _ = std.mem.reverse(u64, b_non_mont[0..]);
            return std.mem.order(u64, &a_non_mont, &b_non_mont);
        }

        /// Check if this field element is less than the rhs.
        ///
        /// # Parameters
        /// - `self` - The field element to check.
        /// - `rhs` - The field element to compare against.
        ///
        /// # Returns
        /// `true` if `self` is less than `rhs`, `false` otherwise.
        pub fn lt(self: Self, rhs: Self) bool {
            return switch (self.cmp(rhs)) {
                .lt => true,
                else => false,
            };
        }

        /// Check if this field element is less than or equal to the rhs.
        ///
        /// # Parameters
        /// - `self` - The field element to check.
        /// - `rhs` - The field element to compare against.
        ///
        /// # Returns
        /// `true` if `self` is less than or equal to `rhs`, `false` otherwise.
        pub fn le(self: Self, rhs: Self) bool {
            return switch (self.cmp(rhs)) {
                .lt, .eq => true,
                else => false,
            };
        }

        /// Check if this field element is greater than the rhs.
        ///
        /// # Parameters
        /// - `self` - The field element to check.
        /// - `rhs` - The field element to compare against.
        ///
        /// # Returns
        /// `true` if `self` is greater than `rhs`, `false` otherwise.
        pub fn gt(self: Self, rhs: Self) bool {
            return switch (self.cmp(rhs)) {
                .gt => true,
                else => false,
            };
        }

        /// Check if this field element is greater than or equal to the rhs.
        ///
        /// # Parameters
        /// - `self` - The field element to check.
        /// - `rhs` - The field element to compare against.
        ///
        /// # Returns
        /// `true` if `self` is greater than or equal to `rhs`, `false` otherwise.
        pub fn ge(self: Self, rhs: Self) bool {
            return switch (self.cmp(rhs)) {
                .gt, .eq => true,
                else => false,
            };
        }

        /// Left shift by `rhs` bits with overflow detection.
        ///
        /// This function shifts the value left by `rhs` bits and detects overflow.
        /// It returns the result of the shift and a boolean indicating whether overflow occurred.
        ///
        /// If the product $\mod{\mathtt{value} ⋅ 2^{\mathtt{rhs}}}_{2^{\mathtt{BITS}}}$ is greater than or equal to 2^BITS, it returns true.
        /// In rhs words, it returns true if the bits shifted out are non-zero.
        ///
        /// # Parameters
        ///
        /// - `self`: The value to be shifted.
        /// - `rhs`: The number of bits to shift left.
        ///
        /// # Returns
        ///
        /// A tuple containing the shifted value and a boolean indicating overflow.
        pub fn overflowing_shl(
            self: Self,
            rhs: usize,
        ) std.meta.Tuple(&.{ Self, bool }) {
            const limbs = rhs / 64;
            const bits = @mod(rhs, 64);

            if (limbs >= Limbs) {
                return .{ Self.zero(), !self.eql(Self.zero()) };
            }
            var res = self;
            if (bits == 0) {
                // Check for overflow
                var overflow = false;
                for (Limbs - limbs..Limbs) |i| {
                    overflow = overflow or (res.fe[i] != 0);
                }
                if (res.fe[Limbs - limbs - 1] > Self.Mask) {
                    overflow = true;
                }

                // Shift
                var idx = Limbs - 1;
                while (idx >= limbs) : (idx -= 1) {
                    res.fe[idx] = res.fe[idx - limbs];
                }
                for (0..limbs) |i| {
                    res.fe[i] = 0;
                }
                res.fe[Limbs - 1] &= Self.Mask;
                return .{ res, overflow };
            }

            // Check for overflow
            var overflow = false;
            for (Limbs - limbs..Limbs) |i| {
                overflow = overflow or (res.fe[i] != 0);
            }

            if (std.math.shr(
                u64,
                res.fe[Limbs - limbs - 1],
                64 - bits,
            ) != 0) {
                overflow = true;
            }
            if (std.math.shl(
                u64,
                res.fe[Limbs - limbs - 1],
                bits,
            ) > Self.Mask) {
                overflow = true;
            }

            // Shift
            var idx = Limbs - 1;
            while (idx > limbs) : (idx -= 1) {
                res.fe[idx] = std.math.shl(
                    u64,
                    res.fe[idx - limbs],
                    bits,
                ) | std.math.shr(
                    u64,
                    res.fe[idx - limbs - 1],
                    64 - bits,
                );
            }

            res.fe[limbs] = std.math.shl(
                u64,
                res.fe[0],
                bits,
            );
            for (0..limbs) |i| {
                res.fe[i] = 0;
            }
            res.fe[Limbs - 1] &= Self.Mask;
            return .{ res, overflow };
        }

        /// Left shift by `rhs` bits with wrapping behavior.
        ///
        /// This function shifts the value left by `rhs` bits, and it wraps around if an overflow occurs.
        /// It returns the result of the shift.
        ///
        /// # Parameters
        ///
        /// - `self`: The value to be shifted.
        /// - `rhs`: The number of bits to shift left.
        ///
        /// # Returns
        ///
        /// The shifted value with wrapping behavior.
        pub fn wrapping_shl(self: Self, rhs: usize) Self {
            return self.overflowing_shl(rhs)[0];
        }

        /// Left shift by `rhs` bits with saturation.
        ///
        /// This function shifts the value left by `rhs` bits with saturation behavior.
        /// If an overflow occurs, it returns `Self.Max`, otherwise, it returns the result of the shift.
        ///
        /// # Parameters
        ///
        /// - `self`: The value to be shifted.
        /// - `rhs`: The number of bits to shift left.
        ///
        /// # Returns
        ///
        /// The shifted value with saturation behavior, or `Self.Max` on overflow.
        pub fn saturating_shl(self: Self, rhs: usize) Self {
            const shl = self.overflowing_shl(rhs);
            return if (!shl[1]) shl[0] else Self.Max;
        }

        /// Checked left shift by `rhs` bits.
        ///
        /// This function performs a left shift of `self` by `rhs` bits. It returns `Some(value)` if the result is less than `2^BITS`, where `value` is the shifted result. If the result
        /// would be greater than or equal to `2^BITS`, it returns [`null`], indicating an overflow condition where the shifted-out bits would be non-zero.
        ///
        /// # Parameters
        ///
        /// - `self`: The value to be shifted.
        /// - `rhs`: The number of bits to shift left.
        ///
        /// # Returns
        ///
        /// - `Some(value)`: The shifted value if no overflow occurs.
        /// - [`null`]: If the bits shifted out would be non-zero.
        pub fn checked_shl(self: Self, rhs: usize) ?Self {
            const shl = self.overflowing_shl(rhs);
            return if (!shl[1]) shl[0] else null;
        }

        /// Right shift by `rhs` bits with underflow detection.
        ///
        /// This function performs a right shift of `self` by `rhs` bits. It returns the
        /// floor value of the division $\floor{\frac{\mathtt{self}}{2^{\mathtt{rhs}}}}$
        /// and a boolean indicating whether the division was exact (false) or rounded down (true).
        ///
        /// # Parameters
        ///
        /// - `self`: The value to be shifted.
        /// - `rhs`: The number of bits to shift right.
        ///
        /// # Returns
        ///
        /// A tuple containing the shifted value and a boolean indicating underflow.
        pub fn overflowing_shr(
            self: Self,
            rhs: usize,
        ) std.meta.Tuple(&.{ Self, bool }) {
            const limbs = rhs / 64;
            const bits = @mod(rhs, 64);

            if (limbs >= Limbs)
                return .{ Self.zero(), !self.eql(Self.zero()) };

            var res = self;
            if (bits == 0) {
                // Check for overflow
                var overflow = false;
                for (0..limbs) |i| {
                    overflow = overflow or (res.fe[i] != 0);
                }

                // Shift
                for (0..Limbs - limbs) |i| {
                    res.fe[i] = res.fe[i + limbs];
                }
                for (Limbs - limbs..Limbs) |i| {
                    res.fe[i] = 0;
                }
                return .{ res, overflow };
            }

            // Check for overflow
            var overflow = false;
            for (0..limbs) |i| {
                overflow = overflow or (res.fe[i] != 0);
            }
            overflow = overflow or (std.math.shr(
                u64,
                res.fe[limbs],
                bits,
            ) != 0);

            // Shift
            for (0..Limbs - limbs - 1) |i| {
                res.fe[i] = std.math.shr(
                    u64,
                    res.fe[i + limbs],
                    bits,
                ) | std.math.shl(
                    u64,
                    res.fe[i + limbs + 1],
                    64 - bits,
                );
            }

            res.fe[Limbs - limbs - 1] = std.math.shr(
                u64,
                res.fe[Limbs - 1],
                bits,
            );
            for (Limbs - limbs..Limbs) |i| {
                res.fe[i] = 0;
            }
            return .{ res, overflow };
        }

        /// Right shift by `rhs` bits with checked underflow.
        ///
        /// This function performs a right shift of `self` by `rhs` bits. It returns `Some(value)` with the result of the shift if no underflow occurs. If underflow happens (bits are shifted out), it returns [`null`].
        ///
        /// # Parameters
        ///
        /// - `self`: The value to be shifted.
        /// - `rhs`: The number of bits to shift right.
        ///
        /// # Returns
        ///
        /// - `Some(value)`: The shifted value if no underflow occurs.
        /// - [`null`]: If the division is not exact.
        pub fn checked_shr(self: Self, rhs: usize) ?Self {
            const shl = self.overflowing_shr(rhs);
            return if (!shl[1]) shl[0] else null;
        }

        /// Right shift by `rhs` bits with wrapping behavior.
        ///
        /// This function performs a right shift of `self` by `rhs` bits, and it wraps around if an underflow occurs. It returns the result of the shift.
        ///
        /// # Parameters
        ///
        /// - `self`: The value to be shifted.
        /// - `rhs`: The number of bits to shift right.
        ///
        /// # Returns
        ///
        /// The shifted value with wrapping behavior.
        pub fn wrapping_shr(self: Self, rhs: usize) Self {
            return self.overflowing_shr(rhs)[0];
        }
    };
}
