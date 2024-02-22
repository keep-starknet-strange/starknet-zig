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
