const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

/// Calculates the result of a + b * c:
/// - returning the lower 64 bits of the result
/// - setting `carry` to the upper 64 bits.
pub inline fn mac(a: u64, b: u64, c: u64, carry: *u64) u64 {
    const tmp = @as(u128, a) + @as(u128, b) * @as(u128, c);
    carry.* = @intCast(tmp >> 64);
    return @truncate(tmp);
}

/// Calculates the result of a + b * c:
/// - returning the lower 64 bits of the result
/// - setting `carry` to the upper 64 bits.
///
/// This function performs the same calculation as the `mac` function but discards the result,
/// making it suitable for cases where only the carry value is needed.
pub inline fn macDiscard(a: u64, b: u64, c: u64, carry: *u64) void {
    const tmp = @as(u128, a) + @as(u128, b) * @as(u128, c);
    carry.* = @intCast(tmp >> 64);
}

/// Calculates the result of a + b * c + carry:
/// - returning the lower 64 bits of the result
/// - setting `carry` to the upper 64 bits.
pub inline fn macWithCarry(a: u64, b: u64, c: u64, carry: *u64) u64 {
    const tmp = @as(u128, a) + @as(u128, b) * @as(u128, c) + @as(u128, carry.*);
    carry.* = @intCast(tmp >> 64);
    return @truncate(tmp);
}

/// Calculates the result of a - b - borrow for 64-bit integers:
/// - returning the result of the subtraction as the lower 64 bits
/// - setting `borrow` to 1 if there is a borrow, and 0 otherwise.
///
/// This function subtracts the values `b` and `borrow` from the value at the memory address `a`.
///
/// It returns the result of the subtraction as the lower 64 bits, and sets `borrow` to 1 if there
/// was a borrow during the subtraction (i.e., if the result would have been negative), and 0 otherwise.
pub inline fn sbb(comptime T: type, a: *u64, b: u64, borrow: T) T {
    const tmp = (@as(u128, 1) << 64) + @as(u128, a.*) -
        @as(u128, b) - @as(u128, @intCast(borrow));
    a.* = @truncate(tmp);
    return @intCast(@intFromBool(tmp >> 64 == 0));
}

/// Sets a = a + b + carry, and returns the new carry.
///
/// This function performs the addition of two 64-bit integers `a` and `b` along with a carry `carry`.
/// It updates the value at the memory address `a` to the sum of `a`, `b`, and `carry`, and returns
/// the new carry resulting from the addition.
pub inline fn adc(comptime T: type, a: *u64, b: u64, carry: T) T {
    const tmp = @as(u128, a.*) + @as(u128, b) + @as(u128, carry);
    a.* = @truncate(tmp);
    return @intCast(tmp >> 64);
}

pub fn powModulus(b: u512, e: u512, modulus: u512) u512 {
    var base: u512 = b;
    var exponent: u512 = e;

    if (modulus == 1) return 0;

    base = base % modulus;

    var result: u512 = 1;

    while (exponent > 0) {
        if ((exponent & 1) == 1) {
            result = @rem(result * base, modulus);
        }

        base = @rem(base * base, modulus);
        exponent = exponent >> 1;
    }

    return result;
}

pub fn legendre(a: u512, p: u512) u512 {
    return powModulus(a, (p - 1) / 2, p);
}

pub fn tonelliShanks(n: u512, p: u512) struct { u512, u512, bool } {
    if (legendre(n, p) != 1) {
        return .{ 0, 0, false };
    }

    // Factor out powers of 2 from p - 1
    var q: u512 = p - 1;
    var s: u512 = 0;
    while (q % 2 == 0) {
        q = q / 2;
        s = s + 1;
    }

    if (s == 1) {
        const result: u512 = powModulus(n, (p + 1) / 4, p);
        return .{ result, p - result, true };
    }

    // Find a non-square z such as ( z | p ) = -1
    var z: u512 = 2;
    while (legendre(z, p) != p - 1) {
        z = z + 1;
    }

    var c: u512 = powModulus(z, q, p);
    var t: u512 = powModulus(n, q, p);
    var m: u512 = s;
    var result: u512 = powModulus(n, (q + 1) >> 1, p);

    while (t != 1) {
        var i: u512 = 1;
        z = @rem(t * t, p);
        while (z != 1 and i < m - 1) {
            i = i + 1;
            z = @rem(z * z, p);
        }

        const b: u512 = powModulus(c, @as(u512, 1) << @intCast(m - i - 1), p);
        c = @rem(b * b, p);
        t = @rem(t * c, p);
        m = i;
        result = @rem(result * b, p);
    }
    return .{ result, p - result, true };
}

pub fn extendedGCD(self: i256, rhs: i256) struct { gcd: i256, x: i256, y: i256 } {
    var s = [_]i256{ 0, 1 };
    var t = [_]i256{ 1, 0 };
    var r = [_]i256{ rhs, self };

    while (r[0] != 0) {
        const q = @divFloor(r[1], r[0]);
        std.mem.swap(i256, &r[0], &r[1]);
        std.mem.swap(i256, &s[0], &s[1]);
        std.mem.swap(i256, &t[0], &t[1]);
        r[0] = r[0] - q * r[1];
        s[0] = s[0] - q * s[1];
        t[0] = t[0] - q * t[1];
    }

    if (r[1] >= 0) {
        return .{ .gcd = r[1], .x = s[1], .y = t[1] };
    } else {
        return .{ .gcd = -r[1], .x = -s[1], .y = -t[1] };
    }
}

test "Multiply accumulate basic test" {
    var carry: u64 = 0;
    try expectEqual(@as(u64, 25), mac(5, 10, 2, &carry));
    try expectEqual(@as(u64, 0), carry);
}

test "Multiply accumulate with overflow" {
    var carry: u64 = 0;
    try expectEqual(9, mac(std.math.maxInt(u64) - 10, 10, 2, &carry));
    try expectEqual(@as(u64, 1), carry);
}

test "Multiply accumulate with overflow in carry" {
    var carry: u64 = 0;
    try expectEqual(0, mac(std.math.maxInt(u64), std.math.maxInt(u64), std.math.maxInt(u64), &carry));
    try expectEqual(@as(u64, std.math.maxInt(u64)), carry);
}

test "Multiply accumulate with 0 as input" {
    var carry: u64 = 0;
    try expectEqual(200, mac(0, 10, 20, &carry));
    try expectEqual(@as(u64, 0), carry);
}

test "Multiply accumulate discard basic test" {
    var carry: u64 = 0;
    macDiscard(5, 10, 2, &carry);
    try expectEqual(@as(u64, 0), carry);
}

test "Multiply accumulate discard with overflow" {
    var carry: u64 = 0;
    macDiscard(std.math.maxInt(u64) - 10, 10, 2, &carry);
    try expectEqual(@as(u64, 1), carry);
}

test "Multiply accumulate discard with overflow in carry" {
    var carry: u64 = 0;
    macDiscard(std.math.maxInt(u64), std.math.maxInt(u64), std.math.maxInt(u64), &carry);
    try expectEqual(@as(u64, std.math.maxInt(u64)), carry);
}

test "Multiply accumulate discard with 0 as input" {
    var carry: u64 = 0;
    macDiscard(0, 10, 20, &carry);
    try expectEqual(@as(u64, 0), carry);
}

test "Multiply accumulate with carry discard with 0 as input and initial carry" {
    var carry: u64 = 123;
    try expectEqual(@as(u64, 123), macWithCarry(0, 0, 0, &carry));
    try expectEqual(@as(u64, 0), carry);
}

test "Multiply accumulate with carry discard with carry at the end" {
    var carry: u64 = 123;
    try expectEqual(@as(u64, 132), macWithCarry(std.math.maxInt(u64) - 10, 10, 2, &carry));
    try expectEqual(@as(u64, 1), carry);
}

test "Multiply accumulate with carry discard with no at the end" {
    var carry: u64 = 0;
    try expectEqual(@as(u64, std.math.maxInt(u64)), macWithCarry(std.math.maxInt(u64), 0, 0, &carry));
    try expectEqual(@as(u64, 0), carry);
}

test "Multiply accumulate with carry discard - some edge cases" {
    var carry: u64 = 123;
    try expectEqual(@as(u64, 123), macWithCarry(std.math.maxInt(u64), 1, 1, &carry));
    try expectEqual(@as(u64, 1), carry);

    carry = 123;
    try expectEqual(@as(u64, 122), macWithCarry(std.math.maxInt(u64), 0, 1, &carry));
    try expectEqual(@as(u64, 1), carry);

    carry = 123;
    try expectEqual(@as(u64, 122), macWithCarry(std.math.maxInt(u64), 1, 0, &carry));
    try expectEqual(@as(u64, 1), carry);
}

test "Subtraction with borrow basic operation" {
    var a: u64 = 10;
    try expectEqual(@as(u64, 0), sbb(u64, &a, 5, 0));
    try expectEqual(@as(u64, 5), a);

    a = 10;
    try expectEqual(@as(u8, 0), sbb(u64, &a, 5, 0));
    try expectEqual(@as(u8, 5), a);
}

test "Subtraction with borrow negative result" {
    var a: u64 = 5;
    try expectEqual(@as(u64, 1), sbb(u64, &a, 10, 0));
    try expectEqual(@as(u64, std.math.maxInt(u64) - 4), a);
}

test "Subtraction with borrow non zero borrow" {
    var a: u64 = 10;
    try expectEqual(@as(u64, 0), sbb(u64, &a, 5, 1));
    try expectEqual(@as(u64, 4), a);
}

test "Subtraction with all zero" {
    var a: u64 = 0;
    try expectEqual(@as(u64, 0), sbb(u64, &a, 0, 0));
    try expectEqual(@as(u64, 0), a);
}

test "Add with carry with no carry" {
    var a: u64 = 100;
    try expectEqual(@as(u64, 0), adc(u64, &a, 50, 0));
    try expectEqual(@as(u64, 150), a);
}

test "Add with carry with carry" {
    var a: u64 = std.math.maxInt(u64);
    try expectEqual(@as(u64, 1), adc(u64, &a, 1, 1));
    try expectEqual(@as(u64, 1), a);
}

test "Add with carry with large numbers" {
    var a: u64 = std.math.maxInt(u64);
    try expectEqual(@as(u64, 1), adc(u64, &a, std.math.maxInt(u64), 1));
    try expectEqual(@as(u64, std.math.maxInt(u64)), a);
}

test "Add with carry with maximum value and no carry" {
    var a: u64 = std.math.maxInt(u64);
    try expectEqual(@as(u64, 0), adc(u64, &a, 0, 0));
    try expectEqual(@as(u64, std.math.maxInt(u64)), a);
}
