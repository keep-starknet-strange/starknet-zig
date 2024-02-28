const std = @import("std");

const expectEqual = std.testing.expectEqual;
const expect = std.testing.expect;

pub const ConstChoice = struct {
    const Self = @This();

    /// The underlying word value.
    word: u64 = 0,

    /// The truthy value.
    pub const TRUE: Self = .{ .word = std.math.maxInt(u64) };

    /// The falsy value.
    pub const FALSE: Self = .{};

    /// Retrieves the mask value associated with the ConstChoice.
    /// Returns the mask value as type `T`.
    pub fn asMask(self: *const Self, comptime T: type) T {
        return switch (@typeInfo(T).Int.bits) {
            64 => self.word,
            else => |b| if (b < 64) @as(T, @truncate(self.word)) else @intCast(self.word),
        };
    }

    /// Initializes a ConstChoice instance from a Word mask value.
    /// `value`: The Word mask value.
    /// Returns the initialized ConstChoice instance.
    pub fn initFromWordMask(value: u64) Self {
        std.debug.assert(value == TRUE.word or value == FALSE.word);
        return .{ .word = value };
    }

    /// Initializes a ConstChoice instance from a Word least significant bit (LSB) value.
    /// `value`: The Word LSB value.
    /// Returns the initialized ConstChoice instance.
    pub fn initFromWordLsb(comptime T: type, value: T) Self {
        std.debug.assert(value == 0 or value == 1);

        return .{
            .word = switch (@typeInfo(T).Int.bits) {
                64 => -%value,
                else => -%@as(u64, @intCast(value)),
            },
        };
    }

    /// Initializes a ConstChoice instance from a boolean value.
    /// `flag`: The boolean value.
    /// Returns the truthy value if `flag` is true, and the falsy value if `flag` is false.
    pub fn initFromBool(flag: bool) Self {
        return if (flag) TRUE else FALSE;
    }

    /// Initializes a ConstChoice instance from a non-zero word value.
    /// `T`: The type of the value.
    /// `value`: The word value.
    /// Returns the truthy value if `value != 0`, and the falsy value otherwise.
    pub fn initFromWordNonZero(comptime T: type, value: T) Self {
        return Self.initFromBool(value != 0);
    }

    /// Initializes a ConstChoice instance from the equality comparison of two values.
    /// `T`: The type of the values.
    /// `x`: The first value for comparison.
    /// `y`: The second value for comparison.
    /// Returns the truthy value if `x == y`, and the falsy value otherwise.
    pub fn initFromWordEq(comptime T: type, x: T, y: T) Self {
        return Self.initFromBool(x == y);
    }

    /// Initializes a ConstChoice instance from the comparison of two values where the first value is less than the second.
    /// `T`: The type of the values.
    /// `x`: The first value for comparison.
    /// `y`: The second value for comparison.
    /// Returns the truthy value if `x < y`, and the falsy value otherwise.
    pub fn initFromWordLt(comptime T: type, x: T, y: T) Self {
        return Self.initFromBool(x < y);
    }

    /// Initializes a ConstChoice instance from the comparison of two values where the first value is less than or equal to the second.
    /// `T`: The type of the values.
    /// `x`: The first value for comparison.
    /// `y`: The second value for comparison.
    /// Returns the truthy value if `x <= y`, and the falsy value otherwise.
    pub fn initFromWordLe(comptime T: type, x: T, y: T) Self {
        return Self.initFromBool(x <= y);
    }

    /// Initializes a ConstChoice instance from the comparison of two values where the first value is greater than the second.
    /// `T`: The type of the values.
    /// `x`: The first value for comparison.
    /// `y`: The second value for comparison.
    /// Returns the truthy value if `x > y`, and the falsy value otherwise.
    pub fn initFromWordGt(comptime T: type, x: T, y: T) Self {
        return Self.initFromWordLt(T, y, x);
    }

    /// Initializes a ConstChoice instance from the comparison of two values where the first value is greater than or equal to the second.
    /// `T`: The type of the values.
    /// `x`: The first value for comparison.
    /// `y`: The second value for comparison.
    /// Returns the truthy value if `x >= y`, and the falsy value otherwise.
    pub fn initFromWordGe(comptime T: type, x: T, y: T) Self {
        return Self.initFromBool(x >= y);
    }

    /// Performs logical negation on a ConstChoice instance.
    /// `self`: The ConstChoice instance to negate.
    /// Returns the negated ConstChoice instance.
    pub fn not(self: *const Self) Self {
        return .{ .word = ~self.word };
    }

    /// Performs a bitwise OR operation between two ConstChoice instances.
    /// `self`: The first ConstChoice operand.
    /// `rhs`: The second ConstChoice operand.
    /// Returns the result of the bitwise OR operation.
    pub fn orWord(self: *const Self, rhs: *const Self) Self {
        return .{ .word = self.word | rhs.word };
    }

    /// Performs a bitwise AND operation between two ConstChoice instances.
    /// `self`: The first ConstChoice operand.
    /// `rhs`: The second ConstChoice operand.
    /// Returns the result of the bitwise AND operation.
    pub fn andWord(self: *const Self, rhs: *const Self) Self {
        return .{ .word = self.word & rhs.word };
    }

    /// Returns either `a` or `b` based on the truthiness of `self`.
    /// `self`: The ConstChoice instance determining the selection.
    /// `T`: The type of values `a` and `b`.
    /// `a`: The value to return if `self` is falsy.
    /// `b`: The value to return if `self` is truthy.
    /// Returns `a` if `self` is falsy, otherwise returns `b`.
    pub fn selectWord(self: *const Self, comptime T: type, a: T, b: T) T {
        return if (self.eql(&TRUE)) b else a;
    }

    /// Returns `a` if `self` is truthy, otherwise returns 0.
    /// `self`: The ConstChoice instance determining the selection.
    /// `T`: The type of the value `a`.
    /// `a`: The value to return if `self` is truthy.
    /// Returns `a` if `self` is truthy, otherwise returns 0.
    pub fn ifTrue(self: *const Self, comptime T: type, a: T) T {
        return if (self.eql(&TRUE)) a else 0;
    }

    /// Checks if two ConstChoice instances are equal.
    /// `self`: The first ConstChoice instance.
    /// `rhs`: The second ConstChoice instance to compare with `self`.
    /// Returns `true` if the two instances are equal, otherwise `false`.
    pub fn eql(self: *const Self, rhs: *const Self) bool {
        return self.word == rhs.word;
    }
};

test "ConstChoice: initFromWordMask" {
    try expect(ConstChoice.initFromWordMask(0).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.initFromWordMask(std.math.maxInt(u64)).eql(&ConstChoice.TRUE));
}

test "ConstChoice: initFromWordLsb" {
    // u64
    try expect(ConstChoice.initFromWordLsb(u64, 0).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.initFromWordLsb(u64, 1).eql(&ConstChoice.TRUE));

    // u8
    try expect(ConstChoice.initFromWordLsb(u8, 0).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.initFromWordLsb(u8, 1).eql(&ConstChoice.TRUE));
}

test "ConstChoice: initFromBool" {
    try expect(ConstChoice.initFromBool(true).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.initFromBool(false).eql(&ConstChoice.FALSE));
}

test "ConstChoice: initFromWordNonZero" {
    // u64
    try expect(ConstChoice.initFromWordNonZero(u64, 555).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.initFromWordNonZero(u64, 0).eql(&ConstChoice.FALSE));

    // u32
    try expect(ConstChoice.initFromWordNonZero(u32, 32).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.initFromWordNonZero(u32, 0).eql(&ConstChoice.FALSE));
}

test "ConstChoice: asMask" {
    // To u64
    try expectEqual(@as(u64, 0), ConstChoice.initFromWordMask(0).asMask(u64));
    try expectEqual(
        @as(u64, std.math.maxInt(u64)),
        ConstChoice.initFromWordMask(std.math.maxInt(u64)).asMask(u64),
    );

    // To smaller unsigned integer type u8
    try expectEqual(@as(u8, 0), ConstChoice.initFromWordMask(0).asMask(u8));
    try expectEqual(
        @as(u8, std.math.maxInt(u8)),
        ConstChoice.initFromWordMask(std.math.maxInt(u64)).asMask(u8),
    );

    // To larger unsigned integer type u128
    try expectEqual(@as(u128, 0), ConstChoice.initFromWordMask(0).asMask(u128));
    try expectEqual(
        @as(u128, std.math.maxInt(u64)),
        ConstChoice.initFromWordMask(std.math.maxInt(u64)).asMask(u128),
    );
}

test "ConstChoice: initFromWordEq" {
    try expect(ConstChoice.initFromWordEq(u64, 4, 5).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.initFromWordEq(u64, 5, 5).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.initFromWordEq(u64, 6, 5).eql(&ConstChoice.FALSE));
}

test "ConstChoice: initFromWordLt" {
    try expect(ConstChoice.initFromWordLt(u64, 4, 5).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.initFromWordLt(u64, 5, 5).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.initFromWordLt(u64, 6, 5).eql(&ConstChoice.FALSE));
}

test "ConstChoice: initFromWordLe" {
    try expect(ConstChoice.initFromWordLe(u64, 4, 5).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.initFromWordLe(u64, 5, 5).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.initFromWordLe(u64, 6, 5).eql(&ConstChoice.FALSE));
}

test "ConstChoice: initFromWordGt" {
    try expect(ConstChoice.initFromWordGt(u64, 4, 5).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.initFromWordGt(u64, 5, 5).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.initFromWordGt(u64, 6, 5).eql(&ConstChoice.TRUE));
}

test "ConstChoice: initFromWordGe" {
    try expect(ConstChoice.initFromWordGe(u64, 4, 5).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.initFromWordGe(u64, 5, 5).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.initFromWordGe(u64, 6, 5).eql(&ConstChoice.TRUE));
}

test "ConstChoice: not" {
    try expect(ConstChoice.TRUE.not().eql(&ConstChoice.FALSE));
    try expect(ConstChoice.FALSE.not().eql(&ConstChoice.TRUE));
}

test "ConstChoice: orWord" {
    try expect(ConstChoice.TRUE.orWord(&ConstChoice.TRUE).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.FALSE.orWord(&ConstChoice.TRUE).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.FALSE.orWord(&ConstChoice.FALSE).eql(&ConstChoice.FALSE));
}

test "ConstChoice: andWord" {
    try expect(ConstChoice.TRUE.andWord(&ConstChoice.TRUE).eql(&ConstChoice.TRUE));
    try expect(ConstChoice.FALSE.andWord(&ConstChoice.TRUE).eql(&ConstChoice.FALSE));
    try expect(ConstChoice.FALSE.andWord(&ConstChoice.FALSE).eql(&ConstChoice.FALSE));
}

test "ConstChoice: selectWord" {
    const a: u64 = 1;
    const b: u64 = 2;
    try expect(ConstChoice.TRUE.selectWord(u64, a, b) == b);
    try expect(ConstChoice.FALSE.selectWord(u64, a, b) == a);
}

test "ConstChoice: ifTrue" {
    // u64
    try expectEqual(@as(u64, 10), ConstChoice.TRUE.ifTrue(u64, 10));
    try expectEqual(@as(u64, 0), ConstChoice.FALSE.ifTrue(u64, 10));

    // u32
    try expectEqual(@as(u32, 10), ConstChoice.TRUE.ifTrue(u32, 10));
    try expectEqual(@as(u32, 0), ConstChoice.FALSE.ifTrue(u32, 10));
}
