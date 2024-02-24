const std = @import("std");
const builtin = @import("builtin");
const ArrayList = std.ArrayList;

const tonelliShanks = @import("./helper.zig").tonelliShanks;
const extendedGCD = @import("./helper.zig").extendedGCD;
const arithmetic = @import("./arithmetic.zig");
const bigInt = @import("./biginteger.zig").bigInt;

pub const ModSqrtError = error{
    InvalidInput,
};

/// Represents a finite field element.
pub fn Field(comptime F: type, comptime modulo: u256) type {
    return struct {
        const Self = @This();

        // Reprensentation of - modulus^{-1} mod 2^{64}
        pub const Inv: u64 = 0xffffffffffffffff;
        // One before the modulus
        pub const MaxField: bigInt(Limbs) = bigInt(Limbs).init(.{ 32, 0, 0, 544 });
        // Modulus in non Montgomery format
        // pub const Modulus: Self = .{ .fe = .{ 1, 0, 0, 576460752303423505 } };
        pub const Modulus: bigInt(Limbs) = bigInt(Limbs).init(.{ 1, 0, 0, 576460752303423505 });
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
        pub const Max: bigInt(Limbs) = bigInt(Limbs).init(.{
            std.math.maxInt(u64),
            std.math.maxInt(u64),
            std.math.maxInt(u64),
            std.math.maxInt(u64),
        });
        /// R2 = R^2 % Self::MODULUS (used for Montgomery operations)
        pub const R2: bigInt(Limbs) = bigInt(Limbs).init(.{
            18446741271209837569,
            5151653887,
            18446744073700081664,
            576413109808302096,
        });

        fe: bigInt(Limbs),

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
                0...63 => F.toMontgomery(&mont, [Limbs]u64{ @intCast(num), 0, 0, 0 }),
                64 => F.toMontgomery(&mont, [Limbs]u64{ num, 0, 0, 0 }),
                65...128 => F.toMontgomery(
                    &mont,
                    [Limbs]u64{
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
                    std.mem.writeInt(u256, lbe[0..], num % Modulo, .little);
                    var nonMont: F.NonMontgomeryDomainFieldElement = undefined;
                    F.fromBytes(&nonMont, lbe);
                    F.toMontgomery(&mont, nonMont);
                },
            }

            return .{ .fe = bigInt(Limbs).init(mont) };
        }

        /// Get the field element representing zero.
        ///
        /// Returns a field element with a value of zero.
        pub inline fn zero() Self {
            comptime {
                return .{ .fe = bigInt(Limbs){} };
            }
        }

        /// Get the field element representing one.
        ///
        /// Returns a field element with a value of one.
        pub inline fn one() Self {
            comptime {
                return .{
                    .fe = bigInt(Limbs).init(
                        .{
                            18446744073709551585,
                            18446744073709551615,
                            18446744073709551615,
                            576460752303422960,
                        },
                    ),
                };
            }
        }

        /// Get the field element representing two.
        ///
        /// Returns a field element with a value of two.
        pub inline fn two() Self {
            comptime {
                return .{
                    .fe = bigInt(Limbs).init(
                        .{
                            18446744073709551553,
                            18446744073709551615,
                            18446744073709551615,
                            576460752303422416,
                        },
                    ),
                };
            }
        }

        /// Get the field element representing three.
        ///
        /// Returns a field element with a value of three.
        pub inline fn three() Self {
            comptime {
                return .{
                    .fe = bigInt(Limbs).init(
                        .{
                            18446744073709551521,
                            18446744073709551615,
                            18446744073709551615,
                            576460752303421872,
                        },
                    ),
                };
            }
        }

        /// Create a field element from a byte array.
        ///
        /// Converts a byte array into a field element in Montgomery representation.
        pub fn fromBytes(bytes: [BytesSize]u8) Self {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            inline for (0..Limbs) |i| {
                non_mont[i] = std.mem.readInt(
                    u64,
                    bytes[i * 8 .. (i + 1) * 8],
                    .little,
                );
            }
            var ret: Self = undefined;
            F.toMontgomery(&ret.fe.limbs, non_mont);

            return ret;
        }

        /// Create a field element from a byte array.
        ///
        /// Converts a byte array into a field element in Montgomery representation.
        pub fn fromBytesBe(bytes: [BytesSize]u8) Self {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            inline for (0..Limbs) |i| {
                non_mont[Limbs - 1 - i] = std.mem.readInt(
                    u64,
                    bytes[i * 8 .. (i + 1) * 8],
                    .big,
                );
            }
            var ret: Self = undefined;
            F.toMontgomery(&ret.fe.limbs, non_mont);

            return ret;
        }

        /// Convert the field element to a bits little endian array.
        ///
        /// This function converts the field element to a byte array for serialization.
        pub fn toBitsLe(self: Self) [@bitSizeOf(u256)]bool {
            return bigInt(Limbs).init(self.fromMontgomery()).toBitsLe();
        }

        pub fn toBitsBe(self: Self) [@bitSizeOf(u256)]bool {
            return bigInt(Limbs).init(self.fromMontgomery()).toBitsBe();
        }

        /// Convert the field element to a byte array.
        ///
        /// This function converts the field element to a byte array for serialization.
        pub fn toBytes(self: Self) [BytesSize]u8 {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            F.fromMontgomery(&non_mont, self.fe.limbs);
            var ret: [BytesSize]u8 = undefined;
            inline for (0..Limbs) |i| {
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
            F.fromMontgomery(&non_mont, self.fe.limbs);
            var ret: [BytesSize]u8 = undefined;
            inline for (0..Limbs) |i| {
                std.mem.writeInt(
                    u64,
                    ret[i * 8 .. (i + 1) * 8],
                    non_mont[Limbs - 1 - i],
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
            inline for (0..Limbs) |i|
                if (nmself[Limbs - 1 - i] != 0)
                    return (Limbs - i) * @bitSizeOf(u64) - @clz(nmself[Limbs - 1 - i]);

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
            F.fromMontgomery(&nonMont, self.fe.limbs);
            return nonMont;
        }

        /// Add two field elements.
        ///
        /// Adds the current field element to another field element.
        pub fn add(self: Self, rhs: Self) Self {
            var ret: F.NonMontgomeryDomainFieldElement = undefined;
            F.add(&ret, self.fe.limbs, rhs.fe.limbs);
            return .{ .fe = bigInt(Limbs).init(ret) };
        }

        /// Double a field element.
        ///
        /// Adds the current field element to itself.
        pub fn double(self: Self) Self {
            var ret: F.NonMontgomeryDomainFieldElement = undefined;
            F.add(&ret, self.fe.limbs, self.fe.limbs);
            return .{ .fe = bigInt(Limbs).init(ret) };
        }

        /// Calculating mod sqrt
        /// TODO: add precomution?
        pub fn sqrt(self: Self) ?Self {
            const v = tonelliShanks(self.toInt(), modulo);
            return if (v[2]) Self.fromInt(u256, @intCast(v[0])) else null;
        }

        /// Subtract one field element from another.
        ///
        /// Subtracts another field element from the current field element.
        pub fn sub(self: Self, rhs: Self) Self {
            var ret: F.MontgomeryDomainFieldElement = undefined;
            F.sub(&ret, self.fe.limbs, rhs.fe.limbs);
            return .{ .fe = bigInt(Limbs).init(ret) };
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

        /// Determines whether the current modulus allows for a specific optimization in modular multiplication.
        ///
        /// This function checks if the highest bit of the modulus is zero and not all of the remaining bits are set,
        /// which is a condition required for a specific optimization in modular multiplication.
        ///
        /// The optimization aims to reduce the number of additions needed in CIOS Montgomery multiplication,
        /// resulting in a significant speed improvement for most moduli.
        ///
        /// # Returns:
        /// `true` if the optimization can be applied to the current modulus, `false` otherwise.
        pub fn canUseNoCarryMulOptimization() bool {
            comptime {
                // Check if all remaining bits are one
                var all_remaining_bits_are_one = Modulus.limbs[Limbs - 1] == std.math.maxInt(u64) >> 1;
                for (1..Limbs) |i| {
                    all_remaining_bits_are_one = all_remaining_bits_are_one and
                        (Modulus.limbs[Limbs - i - 1] == std.math.maxInt(u64));
                }

                // Return true if both conditions are met
                return modulusHasSpareBit() and !all_remaining_bits_are_one;
            }
        }

        /// Determines whether the modulus has a spare bit.
        ///
        /// This function checks if the highest bit of the modulus is zero, indicating that there is a spare bit available.
        /// The spare bit condition is crucial for certain optimizations in modular arithmetic operations.
        ///
        /// # Returns
        ///
        /// `true` if the highest bit of the modulus is zero, indicating the presence of a spare bit; otherwise, `false`.
        ///
        /// # Comptime
        ///
        /// This function is evaluated at compile time to determine the presence of a spare bit in the modulus.
        /// It ensures that the check is performed statically during compilation.
        pub fn modulusHasSpareBit() bool {
            comptime {
                // Check if the highest bit of the modulus is zero
                return Modulus.limbs[Limbs - 1] >> 63 == 0;
            }
        }

        /// Performs multiplication of two field elements and returns the result.
        ///
        /// This function takes two pointers to field elements (`self` and `rhs`),
        /// multiplies them together, and returns the result as a new field element.
        ///
        /// # Arguments:
        /// - `self`: A pointer to the first field element.
        /// - `rhs`: A pointer to the second field element.
        ///
        /// # Returns:
        /// A new field element representing the result of the multiplication.
        pub fn mul(self: *const Self, rhs: *const Self) Self {
            // Dereference the pointer to obtain the actual field element
            var a = self.*;
            // Call the `mulAssign` method to perform the multiplication in place
            a.mulAssign(rhs);
            // Return the result
            return a;
        }

        /// Performs modular multiplication using Montgomery multiplication algorithm.
        ///
        /// Montgomery multiplication is a method used to compute modular products efficiently
        /// without expensive divisions, particularly beneficial for cryptographic protocols
        /// involving large moduli. The function takes two integers `a` and `b` and computes
        /// their modular product with respect to a given modulus `N`. The function assumes that
        /// the inputs `a`, `b`, and `N` are all in Montgomery form.
        ///
        /// The Montgomery form of an integer `a` with respect to a chosen radix `R` is `a * R mod N`.
        /// This representation allows for faster modular products, where `R` is carefully chosen
        /// such that `gcd(R, N) = 1`.
        ///
        /// The algorithm alternates between the multiplication and reduction steps involved in
        /// Montgomery modular multiplication, rather than carrying out full multiplication followed by
        /// reduction.
        ///
        /// Additional "no-carry optimization" is implemented, as outlined [here](https://hackmd.io/@gnark/modular_multiplication)
        /// as modulus has (a) a non-zero most significant bit, and (b) at least one
        /// zero bit in the rest of the modulus.
        ///
        /// For another reference implementation, see [arkworks-rs/algebra](https://github.com/arkworks-rs/algebra/blob/3a6156785e12eeb9083a7a402ac037de01f6c069/ff/src/fields/models/fp/montgomery_backend.rs#L151)
        pub fn mulAssign(self: *Self, rhs: *const Self) void {
            // Initialize the result array
            var r = [_]u64{0} ** Limbs;

            // Iterate over the digits of the right-hand side operand
            inline for (0..Limbs) |i| {
                // Perform the first multiplication and accumulation
                var carry1: u64 = 0;
                r[0] = arithmetic.mac(r[0], self.fe.limbs[0], rhs.fe.limbs[i], &carry1);

                // Compute the Montgomery factor k and perform the corresponding multiplication and reduction
                const k: u64 = r[0] *% comptime Self.Inv;
                var carry2: u64 = 0;
                arithmetic.macDiscard(r[0], k, comptime Self.Modulus.limbs[0], &carry2);

                // Iterate over the remaining digits and perform the multiplications and accumulations
                inline for (1..Limbs) |j| {
                    r[j] = arithmetic.macWithCarry(r[j], self.fe.limbs[j], rhs.fe.limbs[i], &carry1);
                    r[j - 1] = arithmetic.macWithCarry(r[j], k, Self.Modulus.limbs[j], &carry2);
                }

                // Add the final carries
                r[Limbs - 1] = carry1 + carry2;
            }

            // Store the result back into the original object
            @memcpy(&self.fe.limbs, &r);

            // Perform modulus subtraction if needed
            F.subtractModulus(&self.fe.limbs);
        }

        /// Negate a field element.
        ///
        /// Negates the value of the current field element.
        pub fn neg(self: *const Self) Self {
            var ret: F.MontgomeryDomainFieldElement = undefined;
            F.sub(&ret, Self.zero().fe.limbs, self.fe.limbs);
            return .{ .fe = bigInt(Limbs).init(ret) };
        }

        /// Check if the field element is zero.
        ///
        /// Determines if the current field element is equal to zero.
        pub fn isZero(self: *const Self) bool {
            return self.eql(Self.zero());
        }

        /// Check if the field element is one.
        ///
        /// Determines if the current field element is equal to one.
        pub fn isOne(self: *const Self) bool {
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

        /// Computes the square of a finite field element.
        ///
        /// This function computes the square of the given finite field element using the `squareAssign` method
        /// and returns the result as a new field element.
        ///
        /// # Arguments
        ///
        /// - `self`: A pointer to the finite field element to be squared.
        ///
        /// # Returns
        ///
        /// A new finite field element representing the square of the input element.
        pub fn square(self: *const Self) Self {
            // Dereference the pointer to obtain the actual field element
            var a = self.*;
            // Call the `squareAssign` method to compute the square in place
            a.squareAssign();
            // Return the result
            return a;
        }

        /// Computes the square of the current finite field element in place.
        ///
        /// This function calculates the square of the current finite field element and updates the value in place.
        ///
        /// It involves various steps including intermediate multiplication, carry propagation, squaring, and Montgomery reduction.
        /// The algorithm efficiently utilizes inline loops for performance optimization.
        /// Additionally, it supports modulus subtraction if the modulus has a spare bit.
        pub fn squareAssign(self: *Self) void {
            const MulBuffer = struct {
                const S = @This();

                /// A tuple to store intermediate multiplication results.
                buf: std.meta.Tuple(&.{ [Limbs]u64, [Limbs]u64 }) =
                    .{ [_]u64{0} ** Limbs, [_]u64{0} ** Limbs },

                /// Retrieves a pointer to the buffer element at the specified index.
                fn getBuf(s: *S, index: usize) *u64 {
                    return if (index < Limbs)
                        &s.buf[0][index]
                    else
                        &s.buf[1][index - Limbs];
                }
            };

            var r: MulBuffer = .{};
            var carry: u64 = 0;

            // Perform multiplication
            inline for (0..Limbs - 1) |i| {
                inline for (i + 1..Limbs) |j| {
                    r.getBuf(i + j).* = arithmetic.macWithCarry(r.getBuf(i + j).*, self.fe.limbs[i], self.fe.limbs[j], &carry);
                }
                r.buf[1][i] = carry;
                carry = 0;
            }

            // Adjust carry for the last limb
            r.buf[1][Limbs - 1] = r.buf[1][Limbs - 2] >> 63;

            // Propagate carries
            inline for (2..2 * Limbs - 1) |i|
                r.getBuf(2 * Limbs - i).* = (r.getBuf(2 * Limbs - i).* << 1) |
                    (r.getBuf(2 * Limbs - (i + 1)).* >> 63);
            r.buf[0][1] <<= 1;

            // Perform squaring
            inline for (0..Limbs) |i| {
                r.getBuf(2 * i).* = arithmetic.macWithCarry(r.getBuf(2 * i).*, self.fe.limbs[i], self.fe.limbs[i], &carry);
                carry = arithmetic.adc(u64, r.getBuf(2 * i + 1), 0, carry);
            }

            // Montgomery reduction
            var carry2: u64 = 0;

            // Reduce and update buffer
            inline for (0..Limbs) |i| {
                const k: u64 = r.buf[0][i] *% Inv;
                carry = 0;
                arithmetic.macDiscard(r.buf[0][i], k, Modulus.limbs[0], &carry);

                inline for (1..Limbs) |j|
                    r.getBuf(j + i).* = arithmetic.macWithCarry(r.getBuf(j + i).*, k, Modulus.limbs[j], &carry);

                carry2 = arithmetic.adc(u64, &r.buf[1][i], carry, carry2);
            }

            // Copy result back to the field element
            @memcpy(&self.fe.limbs, &r.buf[1]);

            // Perform modulus subtraction if needed
            if (comptime Self.modulusHasSpareBit()) F.subtractModulus(&self.fe.limbs);
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
        pub fn batchinverse(out: []Self, in: []const Self) !void {
            std.debug.assert(out.len == in.len);

            var acc = one();
            for (0..in.len) |i| {
                out[i] = acc;
                acc = acc.mul(&in[i]);
            }
            acc = acc.inverse() orelse return error.CantInvertZeroElement;
            for (0..in.len) |i| {
                out[in.len - i - 1] = out[in.len - i - 1].mul(&acc);
                acc = acc.mul(&in[in.len - i - 1]);
            }
        }

        pub fn rand(r: std.Random) Self {
            return Self.fromInt(u256, r.int(u256));
        }

        /// Subtracts a bigint from another bigint and assigns the result to the first bigint.
        ///
        /// This function subtracts a bigint `b` from another bigint `a` and assigns the result to `a`.
        /// If `b` is greater than `a`, it adds the modulus to `a` first to ensure correct subtraction in a finite field.
        ///
        /// Parameters:
        ///   - a: A pointer to the bigint from which `b` will be subtracted, and the result will be assigned.
        ///   - b: A pointer to the bigint that will be subtracted from `a`.
        ///
        /// Returns:
        ///   - void
        ///
        /// Notes:
        ///   - If `b` is greater than `a`, the modulus of the finite field is added to `a` before subtraction to ensure correct arithmetic in a finite field context.
        ///   - The subtraction operation is performed in place, and the result is assigned to `a`.
        pub fn subAssign(self: *Self, rhs: *const Self) void {
            // If b > a, add the modulus to `a` first.
            if (rhs.fe.cmp(&self.fe) == .gt)
                _ = self.fe.addWithCarryAssign(&Modulus);

            // Perform the subtraction operation
            _ = self.fe.subWithBorrowAssign(&rhs.fe);
        }

        /// Computes the multiplicative inverse of a given element in a finite field using the binary Extended Euclidean Algorithm (BEA).
        ///
        /// Reference: Efficient Software-Implementation of Finite Fields with Applications to Cryptography
        /// DOI: DOI: 10.1007/s10440-006-9046-1
        ///
        /// This function implements the binary Extended Euclidean Algorithm (BEA) to compute the multiplicative inverse of a given element in a finite field.
        /// It follows the steps outlined in the BEA, including successive division and modular arithmetic operations, to determine the inverse.
        ///
        ///  BEA does not require integer divisions but only simple operations such as shifts and additions
        ///
        /// Parameters:
        ///   - self: A pointer to the element for which the inverse is to be computed.
        ///
        /// Returns:
        ///   - On success: A structure containing the computed inverse.
        ///   - On failure (if the input is zero): `null`.
        ///
        /// Notes:
        ///   - The binary Extended Euclidean Algorithm (BEA) is a general and efficient method for computing multiplicative inverses in finite fields.
        ///   - Montgomery parameters are used to optimize the computation, improving performance on digital computers.
        ///   - Overflow handling is performed to ensure correct arithmetic operations during the inversion process.
        pub fn inverse(self: *const Self) ?Self {
            // Check if the input is zero
            if (self.isZero()) return null;

            // Constant representing the value 1 in the field
            const o = comptime bigInt(Limbs).one();

            var u = self.fe;
            var v = Modulus;
            var b: Self = .{ .fe = R2 };
            var c = zero();

            // Iterate while both u and v are not one
            while (!u.eql(o) and !v.eql(o)) {
                // Perform operations while u is even
                while (u.isEven()) {
                    u.div2Assign();

                    if (b.fe.isEven()) {
                        b.fe.div2Assign();
                    } else {
                        const carry = b.fe.addWithCarryAssign(&Modulus);
                        b.fe.div2Assign();
                        // Handle overflow if necessary
                        if (comptime !Self.modulusHasSpareBit() and carry) {
                            b.fe.limbs[Limbs - 1] |= 1 << 63;
                        }
                    }
                }

                // Perform operations while v is even
                while (v.isEven()) {
                    v.div2Assign();
                    if (c.fe.isEven()) {
                        c.fe.div2Assign();
                    } else {
                        const carry = c.fe.addWithCarryAssign(&Modulus);
                        c.fe.div2Assign();
                        // Handle overflow if necessary
                        if (comptime !Self.modulusHasSpareBit() and carry) {
                            c.fe.limbs[Limbs - 1] |= 1 << 63;
                        }
                    }
                }

                // Update based on u vs v values
                if (v.cmp(&u) == .lt) {
                    _ = u.subWithBorrowAssign(&v);
                    b.subAssign(&c);
                } else {
                    _ = v.subWithBorrowAssign(&u);
                    c.subAssign(&b);
                }
            }

            // Return the inverse based on the final values of u and v
            return if (u.eql(o)) b else c;
        }

        /// Divide one field element by another.
        ///
        /// Divides the current field element by another field element.
        pub fn div(self: Self, den: Self) !Self {
            return self.mul(&(den.inverse() orelse return error.DivisionByZero));
        }

        /// Check if two field elements are equal.
        ///
        /// Determines whether the current field element is equal to another field element.
        pub fn eql(self: Self, rhs: Self) bool {
            return std.mem.eql(u64, &self.fe.limbs, &rhs.fe.limbs);
        }

        /// Convert the field element to a u256 integer.
        ///
        /// Converts the field element to a u256 integer.
        pub fn toInt(self: Self) u256 {
            var non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            F.fromMontgomery(&non_mont, self.fe.limbs);

            var bytes: [BytesSize]u8 = [_]u8{0} ** BytesSize;
            F.toBytes(&bytes, non_mont);

            return std.mem.readInt(u256, &bytes, .little);
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
        /// The Legendre symbol is a mathematical function commonly used in number theory
        /// to determine whether a given integer is a quadratic residue modulo a prime number.
        ///
        /// # Arguments:
        /// - `a`: The field element for which the Legendre symbol is calculated.
        ///
        /// # Returns:
        /// - `1` if `a` has a square root modulo the modulus (`p`),
        /// - `-1` if `a` does not have a square root modulo `p`,
        /// - `0` if `a` is zero modulo `p`.
        pub fn legendre(a: Self) i2 {
            // Compute the Legendre symbol a|p using
            // Euler's criterion. p is a prime, a is
            // relatively prime to p (if p divides
            // a, then a|p = 0)
            // Returns 1 if a has a square root modulo
            // p, -1 otherwise.

            // Calculate a^(p-1)/2 modulo p
            const ls = a.pow(comptime QMinOneDiv2);

            // Check if a^(p-1)/2 is equivalent to -1 modulo p
            if (ls.toInt() == comptime Modulo - 1) return -1;

            // Check if a^(p-1)/2 is equivalent to 0 modulo p
            if (ls.isZero()) return 0;

            // Otherwise, a^(p-1)/2 is equivalent to 1 modulo p
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
        pub fn cmp(self: *const Self, rhs: *const Self) std.math.Order {
            var a_non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            var b_non_mont: F.NonMontgomeryDomainFieldElement = undefined;
            F.fromMontgomery(&a_non_mont, self.fe.limbs);
            F.fromMontgomery(&b_non_mont, rhs.fe.limbs);
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
        pub fn lt(self: *const Self, rhs: *const Self) bool {
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
        pub fn le(self: *const Self, rhs: *const Self) bool {
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
        pub fn gt(self: *const Self, rhs: *const Self) bool {
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
        pub fn ge(self: *const Self, rhs: *const Self) bool {
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
                    overflow = overflow or (res.fe.limbs[i] != 0);
                }
                if (res.fe.limbs[Limbs - limbs - 1] > Self.Mask) {
                    overflow = true;
                }

                // Shift
                var idx = Limbs - 1;
                while (idx >= limbs) : (idx -= 1) {
                    res.fe.limbs[idx] = res.fe.limbs[idx - limbs];
                }
                for (0..limbs) |i| {
                    res.fe.limbs[i] = 0;
                }
                res.fe.limbs[Limbs - 1] &= Self.Mask;
                return .{ res, overflow };
            }

            // Check for overflow
            var overflow = false;
            for (Limbs - limbs..Limbs) |i| {
                overflow = overflow or (res.fe.limbs[i] != 0);
            }

            if (std.math.shr(
                u64,
                res.fe.limbs[Limbs - limbs - 1],
                64 - bits,
            ) != 0) {
                overflow = true;
            }
            if (std.math.shl(
                u64,
                res.fe.limbs[Limbs - limbs - 1],
                bits,
            ) > Self.Mask) {
                overflow = true;
            }

            // Shift
            var idx = Limbs - 1;
            while (idx > limbs) : (idx -= 1) {
                res.fe.limbs[idx] = std.math.shl(
                    u64,
                    res.fe.limbs[idx - limbs],
                    bits,
                ) | std.math.shr(
                    u64,
                    res.fe.limbs[idx - limbs - 1],
                    64 - bits,
                );
            }

            res.fe.limbs[limbs] = std.math.shl(
                u64,
                res.fe.limbs[0],
                bits,
            );
            for (0..limbs) |i| {
                res.fe.limbs[i] = 0;
            }
            res.fe.limbs[Limbs - 1] &= Self.Mask;
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
            return if (!shl[1]) shl[0] else .{ .fe = Self.Max };
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
                    overflow = overflow or (res.fe.limbs[i] != 0);
                }

                // Shift
                for (0..Limbs - limbs) |i| {
                    res.fe.limbs[i] = res.fe.limbs[i + limbs];
                }
                for (Limbs - limbs..Limbs) |i| {
                    res.fe.limbs[i] = 0;
                }
                return .{ res, overflow };
            }

            // Check for overflow
            var overflow = false;
            for (0..limbs) |i| {
                overflow = overflow or (res.fe.limbs[i] != 0);
            }
            overflow = overflow or (std.math.shr(
                u64,
                res.fe.limbs[limbs],
                bits,
            ) != 0);

            // Shift
            for (0..Limbs - limbs - 1) |i| {
                res.fe.limbs[i] = std.math.shr(
                    u64,
                    res.fe.limbs[i + limbs],
                    bits,
                ) | std.math.shl(
                    u64,
                    res.fe.limbs[i + limbs + 1],
                    64 - bits,
                );
            }

            res.fe.limbs[Limbs - limbs - 1] = std.math.shr(
                u64,
                res.fe.limbs[Limbs - 1],
                bits,
            );
            for (Limbs - limbs..Limbs) |i| {
                res.fe.limbs[i] = 0;
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
