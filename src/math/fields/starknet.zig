const std = @import("std");
const fields = @import("fields.zig");
const bigInt = @import("biginteger.zig").bigInt;
const STARKNET_PRIME = @import("./constants.zig").STARKNET_PRIME;
const FELT_BYTE_SIZE = @import("./constants.zig").FELT_BYTE_SIZE;
const TEST_ITERATIONS = @import("../../main.zig").TEST_ITERATIONS;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectEqualSlices = std.testing.expectEqualSlices;

// Base field for the Stark curve.
// The prime is 0x800000000000011000000000000000000000000000000000000000000000001.
pub const Felt252 = fields.Field(4, STARKNET_PRIME);

test "Felt252: fromU8 should return a field element from a u8" {
    try expectEqual(
        @as(u256, std.math.maxInt(u8)),
        Felt252.fromInt(u8, std.math.maxInt(u8)).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u8) / 3 * 2),
        Felt252.fromInt(u8, std.math.maxInt(u8) / 3 * 2).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u8) / 3),
        Felt252.fromInt(u8, std.math.maxInt(u8) / 3).toU256(),
    );
}

test "Felt252: fromU16 should return a field element from a u16" {
    try expectEqual(
        @as(u256, std.math.maxInt(u16)),
        Felt252.fromInt(u16, std.math.maxInt(u16)).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u16) / 3 * 2),
        Felt252.fromInt(u16, std.math.maxInt(u16) / 3 * 2).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u16) / 3),
        Felt252.fromInt(u16, std.math.maxInt(u16) / 3).toU256(),
    );
}

test "Felt252: fromU32 should return a field element from a u32" {
    try expectEqual(
        @as(u256, std.math.maxInt(u32)),
        Felt252.fromInt(u32, std.math.maxInt(u32)).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u32) / 3 * 2),
        Felt252.fromInt(u32, std.math.maxInt(u32) / 3 * 2).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u32) / 3),
        Felt252.fromInt(u32, std.math.maxInt(u32) / 3).toU256(),
    );
}

test "Felt252: fromU64 should return a field element from a u64" {
    try expectEqual(
        @as(u256, std.math.maxInt(u64)),
        Felt252.fromInt(u64, std.math.maxInt(u64)).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u64) / 3 * 2),
        Felt252.fromInt(u64, std.math.maxInt(u64) / 3 * 2).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u64) / 3),
        Felt252.fromInt(u64, std.math.maxInt(u64) / 3).toU256(),
    );
}

test "Felt252: fromUsize should return a field element from a usize" {
    try expectEqual(
        @as(u256, std.math.maxInt(usize)),
        Felt252.fromInt(usize, std.math.maxInt(usize)).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(usize) / 3 * 2),
        Felt252.fromInt(usize, std.math.maxInt(usize) / 3 * 2).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(usize) / 3),
        Felt252.fromInt(usize, std.math.maxInt(usize) / 3).toU256(),
    );
}

test "Felt252: fromU128 should return a field element from a u128" {
    try expectEqual(
        @as(u256, std.math.maxInt(u128)),
        Felt252.fromInt(u128, std.math.maxInt(u128)).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u128) / 3 * 2),
        Felt252.fromInt(u128, std.math.maxInt(u128) / 3 * 2).toU256(),
    );
    try expectEqual(
        @as(u256, std.math.maxInt(u128) / 3),
        Felt252.fromInt(u128, std.math.maxInt(u128) / 3).toU256(),
    );
}

test "Felt252 testing for field numBitsLe()" {
    try expectEqual(@as(u64, 1), Felt252.fromInt(u8, 1).numBitsLe());
    try expectEqual(@as(u64, 4), Felt252.fromInt(u8, 10).numBitsLe());
    try expectEqual(@as(u64, 252), Felt252.fromInt(u8, 1).neg().numBitsLe());
    try expectEqual(@as(u64, 0), Felt252.fromInt(u8, 0).numBitsLe());
}

test "Felt252 fromInteger" {
    try expectEqual(
        Felt252{
            .fe = bigInt(4).init(
                .{
                    0xfffffffffffffec1,
                    0xffffffffffffffff,
                    0xffffffffffffffff,
                    0x7ffffffffffead0,
                },
            ),
        },
        Felt252.fromInt(u8, 10),
    );
    try expectEqual(
        Felt252{
            .fe = bigInt(4).init(
                .{
                    0xfffffd737e000421,
                    0x1330fffff,
                    0xffffffffff6f8000,
                    0x7ffd4ab5e008a30,
                },
            ),
        },
        Felt252.fromInt(u256, std.math.maxInt(u256)),
    );
}

test "Felt252 toU256" {
    try expectEqual(
        @as(u256, 10),
        Felt252.fromInt(u8, 10).toU256(),
    );

    try expectEqual(
        @as(
            u256,
            0x7fffffffffffdf0ffffffffffffffffffffffffffffffffffffffffffffffe0,
        ),
        Felt252.fromInt(u256, std.math.maxInt(u256)).toU256(),
    );
}

test "Felt252 one" {
    try expectEqual(
        Felt252{
            .fe = bigInt(4).init(
                .{
                    0xffffffffffffffe1,
                    0xffffffffffffffff,
                    0xffffffffffffffff,
                    0x7fffffffffffdf0,
                },
            ),
        },
        Felt252.one(),
    );
}

test "Felt252 zero" {
    try expectEqual(
        Felt252{
            .fe = bigInt(4).init(
                .{
                    0,
                    0,
                    0,
                    0,
                },
            ),
        },
        Felt252.zero(),
    );
}

test "Felt252 equal" {
    try expect(Felt252.zero().eql(Felt252.zero()));
    try expect(Felt252.fromInt(u8, 10).eql(Felt252.fromInt(u8, 10)));
    try expect(!Felt252.fromInt(u8, 100).eql(Felt252.fromInt(u8, 10)));
}

test "Felt252 isZero" {
    try expect(Felt252.zero().isZero());
    try expect(!Felt252.one().isZero());
    try expect(!Felt252.fromInt(u8, 10).isZero());
}

test "Felt252 isOne" {
    try expect(Felt252.one().isOne());
    try expect(!Felt252.zero().isOne());
    try expect(!Felt252.fromInt(u8, 10).isOne());
}

test "Felt252 fromBytesLe" {
    const a: [FELT_BYTE_SIZE]u8 = .{
        0x4E,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x19,
        0x67,
        0x2F,
        0xDF,
        0x76,
        0xCE,
        0x51,
        0xBA,
        0x69,
        0xC6,
        0x07,
        0x6A,
        0x0F,
        0x77,
        0xEA,
        0xBC,
        0xB2,
        0xA9,
        0x3B,
        0xE6,
        0xF8,
        0x96,
        0x00,
    };
    try expectEqual(
        @as(
            u256,
            0x96f8e63ba9b2bcea770f6a07c669ba51ce76df2f67195f5f5f5f5f5f5f5f4e,
        ),
        Felt252.fromBytesLe(a).toU256(),
    );

    try expectEqual(
        Felt252.fromInt(u256, 0x96f8e63ba9b2bcea770f6a07c669ba51ce76df2f67195f5f5f5f5f5f5f5f4e),
        Felt252.fromBytesLe(a),
    );
}

test "Felt252 toBytesLe" {
    const expected = [_]u8{
        0x4E,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x5F,
        0x19,
        0x67,
        0x2F,
        0xDF,
        0x76,
        0xCE,
        0x51,
        0xBA,
        0x69,
        0xC6,
        0x07,
        0x6A,
        0x0F,
        0x77,
        0xEA,
        0xBC,
        0xB2,
        0xA9,
        0x3B,
        0xE6,
        0xF8,
        0x96,
        0x00,
    };
    try expectEqual(
        expected,
        Felt252.fromInt(u256, 0x96f8e63ba9b2bcea770f6a07c669ba51ce76df2f67195f5f5f5f5f5f5f5f4e).toBytesLe(),
    );
}

test "Felt252 toU64" {
    try expectEqual(
        @as(u64, 10),
        try Felt252.fromInt(u8, 10).toInt(u64),
    );
    try expectEqual(
        @as(u64, std.math.maxInt(u64)),
        try Felt252.fromInt(u64, std.math.maxInt(u64)).toInt(u64),
    );
    try std.testing.expectError(
        error.ValueTooLarge,
        Felt252.fromInt(u128, std.math.maxInt(u64) + 1).toInt(u64),
    );
}

test "Felt252 arithmetic operations" {
    const a = Felt252.one();
    const b = Felt252.two();
    const c = a.add(b);
    try expect(c.eql(Felt252.three()));
}

test "Felt252 add" {
    try expectEqual(
        @as(u256, 0xf),
        Felt252.fromInt(u8, 10).add(Felt252.fromInt(u8, 5)).toU256(),
    );
    try expect(Felt252.one().add(Felt252.zero()).isOne());
    try expect(Felt252.zero().add(Felt252.zero()).isZero());
    try expectEqual(
        @as(
            u256,
            0x7fffffffffffbd0ffffffffffffffffffffffffffffffffffffffffffffffbf,
        ),
        Felt252.fromInt(u256, std.math.maxInt(u256)).add(Felt252.fromInt(u256, std.math.maxInt(u256))).toU256(),
    );
}

test "Felt252 sub" {
    try expectEqual(
        @as(u256, 0x5),
        Felt252.fromInt(u8, 10).sub(&Felt252.fromInt(u8, 5)).toU256(),
    );
    try expect(Felt252.fromInt(u256, std.math.maxInt(u256)).sub(&Felt252.fromInt(u256, std.math.maxInt(u256))).isZero());
    try expect(Felt252.zero().sub(&Felt252.zero()).isZero());
}

test "Felt252 mul" {
    try expect(Felt252.zero().mul(&Felt252.zero()).isZero());
    try expect(Felt252.one().mul(&Felt252.one()).isOne());
    try expectEqual(
        @as(u256, 0x32),
        Felt252.fromInt(u8, 10).mul(&Felt252.fromInt(u8, 5)).toU256(),
    );
    try expectEqual(
        @as(
            u256,
            0x7fffffffffffbd0ffffffffffffffffffffffffffffffffffffffffffffffbf,
        ),
        Felt252.fromInt(u256, std.math.maxInt(u256)).mul(&Felt252.two()).toU256(),
    );
}

test "Felt252 neg" {
    try expectEqual(
        @as(
            u256,
            0x800000000000010fffffffffffffffffffffffffffffffffffffffffffffff7,
        ),
        Felt252.fromInt(u8, 10).neg().toU256(),
    );
    try expectEqual(
        @as(
            u256,
            0x220000000000000000000000000000000000000000000000021,
        ),
        Felt252.fromInt(u256, std.math.maxInt(u256)).neg().toU256(),
    );
}

test "Felt252 square" {
    try expectEqual(
        @as(u256, 0x64),
        Felt252.fromInt(u8, 10).square().toU256(),
    );
    try expectEqual(
        @as(
            u256,
            0x7ffd4ab5e008c50ffffffffff6f800000000001330ffffffffffd737e000442,
        ),
        Felt252.fromInt(u256, std.math.maxInt(u256)).square().toU256(),
    );
}

test "Felt252 pow" {
    try expectEqual(
        @as(u256, 0x2540be400),
        Felt252.fromInt(u8, 10).powToBigInt(bigInt(4).fromInt(u8, 10)).toU256(),
    );
    try expectEqual(
        @as(
            u256,
            0x48ea9fffffffffffffff5ffffffffffffffe5000000000000449f,
        ),
        Felt252.fromInt(u64, std.math.maxInt(u64)).powToBigInt(bigInt(4).fromInt(u64, 5)).toU256(),
    );
}

test "Felt252 inv" {
    try expectEqual(
        @as(
            u256,
            0x733333333333342800000000000000000000000000000000000000000000001,
        ),
        Felt252.fromInt(u8, 10).inverse().?.toU256(),
    );
    try expectEqual(
        @as(
            u256,
            0x538bf4edb6bf78474ef0f1979a0db0bdd364ce7aeda9f3c6c04bea822682ba,
        ),
        Felt252.fromInt(u256, std.math.maxInt(u256)).inverse().?.toU256(),
    );
    try expectEqual(
        @as(?Felt252, null),
        Felt252.zero().inverse(),
    );
}

test "Felt252 batchInv" {
    var out: [2]Felt252 = undefined;
    const in: [2]Felt252 = .{ Felt252.fromInt(u8, 10), Felt252.fromInt(u8, 5) };
    try Felt252.batchinverse(&out, &in);
    try expectEqual(
        @as(
            u256,
            0x733333333333342800000000000000000000000000000000000000000000001,
        ),
        out[0].toU256(),
    );
    try expectEqual(
        @as(
            u256,
            0x666666666666674000000000000000000000000000000000000000000000001,
        ),
        out[1].toU256(),
    );
}

test "Felt252 batchInv with zero" {
    var out: [3]Felt252 = undefined;
    try std.testing.expectError(
        error.CantInvertZeroElement,
        Felt252.batchinverse(&out, &.{ Felt252.fromInt(u8, 10), Felt252.fromInt(u8, 5), Felt252.zero() }),
    );
}

test "Felt252 div" {
    const div_10_by_10 = try Felt252.fromInt(u8, 10).div(Felt252.fromInt(u8, 10));
    try expect(
        div_10_by_10.isOne(),
    );
    try std.testing.expectError(
        error.DivisionByZero,
        Felt252.fromInt(u8, 10).div(Felt252.zero()),
    );
}

test "Felt252 legendre" {
    try expectEqual(
        @as(i2, 0),
        Felt252.fromInt(u256, 0x1000000000000022000000000000000000000000000000000000000000000002).legendre(),
    );
    try expectEqual(
        @as(i2, 1),
        Felt252.fromInt(u8, 10).legendre(),
    );
    try expectEqual(
        @as(i2, -1),
        Felt252.fromInt(u8, 135).legendre(),
    );
}

test "Felt252 cmp" {
    try expect(Felt252.fromInt(u8, 10).cmp(&Felt252.fromInt(u64, 343535)) == .lt);
    try expect(Felt252.fromInt(u64, 433).cmp(&Felt252.fromInt(u64, 343535)) == .lt);
    try expect(Felt252.fromInt(u64, 543636535).cmp(&Felt252.fromInt(u64, 434)) == .gt);
    try expect(Felt252.fromInt(u256, std.math.maxInt(u256)).cmp(&Felt252.fromInt(u64, 21313)) == .gt);
    try expect(Felt252.fromInt(u8, 10).cmp(&Felt252.fromInt(u8, 10)) == .eq);
    try expect(Felt252.one().cmp(&Felt252.one()) == .eq);
    try expect(Felt252.zero().cmp(&Felt252.zero()) == .eq);
    try expect(Felt252.fromInt(u8, 10).cmp(&Felt252.fromInt(u256, 10 + STARKNET_PRIME)) == .eq);
}

test "Felt252 lt" {
    try expect(Felt252.fromInt(u8, 10).lt(&Felt252.fromInt(u64, 343535)));
    try expect(Felt252.fromInt(u64, 433).lt(&Felt252.fromInt(u64, 343535)));
    try expect(!Felt252.fromInt(u64, 543636535).lt(&Felt252.fromInt(u64, 434)));
    try expect(!Felt252.fromInt(u256, std.math.maxInt(u256)).lt(&Felt252.fromInt(u64, 21313)));
    try expect(!Felt252.fromInt(u8, 10).lt(&Felt252.fromInt(u8, 10)));
    try expect(!Felt252.one().lt(&Felt252.one()));
    try expect(!Felt252.zero().lt(&Felt252.zero()));
    try expect(!Felt252.fromInt(u8, 10).lt(
        &Felt252.fromInt(u256, 10 + STARKNET_PRIME),
    ));
}

test "Felt252 lte" {
    try expect(Felt252.fromInt(u8, 10).lte(&Felt252.fromInt(u64, 343535)));
    try expect(Felt252.fromInt(u64, 433).lte(&Felt252.fromInt(u64, 343535)));
    try expect(!Felt252.fromInt(u64, 543636535).lte(&Felt252.fromInt(u64, 434)));
    try expect(!Felt252.fromInt(u256, std.math.maxInt(u256)).lte(&Felt252.fromInt(u64, 21313)));
    try expect(Felt252.fromInt(u8, 10).lte(&Felt252.fromInt(u8, 10)));
    try expect(Felt252.one().lte(&Felt252.one()));
    try expect(Felt252.zero().lte(&Felt252.zero()));
    try expect(Felt252.fromInt(u8, 10).lte(
        &Felt252.fromInt(u256, 10 + STARKNET_PRIME),
    ));
}

test "Felt252 gt" {
    try expect(!Felt252.fromInt(u8, 10).gt(&Felt252.fromInt(u64, 343535)));
    try expect(!Felt252.fromInt(u64, 433).gt(&Felt252.fromInt(u64, 343535)));
    try expect(Felt252.fromInt(u64, 543636535).gt(&Felt252.fromInt(u64, 434)));
    try expect(Felt252.fromInt(u256, std.math.maxInt(u256)).gt(&Felt252.fromInt(u64, 21313)));
    try expect(!Felt252.fromInt(u8, 10).gt(&Felt252.fromInt(u8, 10)));
    try expect(!Felt252.one().gt(&Felt252.one()));
    try expect(!Felt252.zero().gt(&Felt252.zero()));
    try expect(!Felt252.fromInt(u8, 10).gt(
        &Felt252.fromInt(u256, 10 + STARKNET_PRIME),
    ));
}

test "Felt252 gte" {
    try expect(!Felt252.fromInt(u8, 10).gte(&Felt252.fromInt(u64, 343535)));
    try expect(!Felt252.fromInt(u64, 433).gte(&Felt252.fromInt(u64, 343535)));
    try expect(Felt252.fromInt(u64, 543636535).gte(&Felt252.fromInt(u64, 434)));
    try expect(Felt252.fromInt(u256, std.math.maxInt(u256)).gte(&Felt252.fromInt(u64, 21313)));
    try expect(Felt252.fromInt(u8, 10).gte(&Felt252.fromInt(u8, 10)));
    try expect(Felt252.one().gte(&Felt252.one()));
    try expect(Felt252.zero().gte(&Felt252.zero()));
    try expect(Felt252.fromInt(u8, 10).gte(
        &Felt252.fromInt(u256, 10 + STARKNET_PRIME),
    ));
}

test "Felt252 lexographicallyLargest" {
    try expect(!Felt252.zero().lexographicallyLargest());
    try expect(!Felt252.fromInt(
        u256,
        0x400000000000008800000000000000000000000000000000000000000000000,
    ).lexographicallyLargest());
    try expect(!Felt252.fromInt(
        u256,
        0x4000000000000087fffffffffffffffffffffffffffffffffffffffffffffff,
    ).lexographicallyLargest());
    try expect(Felt252.fromInt(
        u256,
        0x400000000000008800000000000000000000000000000000000000000000001,
    ).lexographicallyLargest());
    try expect(Felt252.fromInt(u256, std.math.maxInt(u256)).lexographicallyLargest());
}

test "Felt252: toBitsLe" {
    const one = Felt252.one();
    var bits_one = [_]bool{false} ** @bitSizeOf(u256);
    bits_one[0] = true;
    try expectEqualSlices(bool, &bits_one, &one.toBitsLe());

    const max_u64 = Felt252.fromInt(u64, std.math.maxInt(u64));
    var bits_max_u64 = [_]bool{false} ** @bitSizeOf(u256);
    for (0..64) |i| bits_max_u64[i] = true;
    try expectEqualSlices(bool, &bits_max_u64, &max_u64.toBitsLe());
}

test "Felt252: toBitsBe" {
    const one = Felt252.one();
    var bits_one = [_]bool{false} ** @bitSizeOf(u256);
    bits_one[255] = true;
    try expectEqualSlices(bool, &bits_one, &one.toBitsBe());

    const max_u64 = Felt252.fromInt(u64, std.math.maxInt(u64));
    var bits_max_u64 = [_]bool{false} ** @bitSizeOf(u256);
    for (3 * 64..256) |i| bits_max_u64[i] = true;
    try expectEqualSlices(bool, &bits_max_u64, &max_u64.toBitsBe());
}

test "Felt252: arithmetic addition operations" {

    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        const a = Felt252.rand(random);
        const b = Felt252.rand(random);
        const c = Felt252.rand(random);
        const zero = Felt252.zero();

        // Associativity
        try expect(a.add(b).add(c).eql(a.add(c.add(b))));

        // Identify
        try expect(a.eql(zero.add(a)));
        try expect(b.eql(zero.add(b)));
        try expect(c.eql(zero.add(c)));
        try expect(a.eql(a.add(zero)));
        try expect(b.eql(b.add(zero)));
        try expect(c.eql(c.add(zero)));

        // Negation
        try expect(zero.eql(a.neg().add(a)));
        try expect(zero.eql(b.neg().add(b)));
        try expect(zero.eql(c.neg().add(c)));
        try expect(zero.eql(zero.neg().add(zero)));

        // Commutativity
        try expect(a.add(b).eql(b.add(a)));

        // Associativity and commutativity simultaneously
        try expect(a.add(b).add(c).eql(a.add(c).add(b)));
        try expect(a.add(c).add(b).eql(b.add(c).add(a)));

        // Doubling
        try expect(a.add(a).eql(a.double()));
        try expect(b.add(b).eql(b.double()));
        try expect(c.add(c).eql(c.double()));
        try expect(zero.eql(zero.double()));
        try expect(zero.eql(zero.neg().double()));
    }
}

test "Felt252: arithmetic subtraction operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        const a = Felt252.rand(random);
        const b = Felt252.rand(random);
        const zero = Felt252.zero();

        // Associativity
        try expect(a.sub(&b).add(b.sub(&a)).isZero());

        // Identity
        try expect(zero.sub(&a).eql(a.neg()));
        try expect(zero.sub(&b).eql(b.neg()));
        try expect(a.sub(&zero).eql(a));
        try expect(b.sub(&zero).eql(b));
    }
}

test "Felt252: arithmetic multiplication operations" {

    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        const a = Felt252.rand(random);
        const b = Felt252.rand(random);
        const c = Felt252.rand(random);
        const zero = Felt252.zero();
        const one = Felt252.one();
        const rnd_u8 = random.int(u8);
        const bigint_rnd_u8 = bigInt(4).fromInt(u256, rnd_u8);

        // Associativity
        try expect(a.mul(&b).mul(&c).eql(a.mul(&c.mul(&b))));

        // Commutativity
        try expect(a.mul(&b).eql(b.mul(&a)));

        // Identity
        try expect(one.mul(&a).eql(a));
        try expect(one.mul(&b).eql(b));
        try expect(one.mul(&c).eql(c));

        try expect(zero.mul(&a).eql(zero));
        try expect(zero.mul(&b).eql(zero));
        try expect(zero.mul(&c).eql(zero));

        // Inverses
        try expect(a.mul(&a.inverse().?).eql(one));
        try expect(b.mul(&b.inverse().?).eql(one));
        try expect(c.mul(&c.inverse().?).eql(one));
        try expectEqual(null, zero.inverse());
        try expect(one.inverse().?.eql(one));

        // Associativity and commutativity simultaneously
        try expect(a.mul(&b).mul(&c).eql(a.mul(&c).mul(&b)));
        try expect(a.mul(&c).mul(&b).eql(b.mul(&c).mul(&(a))));

        // Squaring
        try expect(a.mul(&a).eql(a.square()));
        try expect(b.mul(&b).eql(b.square()));
        try expect(c.mul(&c).eql(c.square()));

        // Distributivity
        try expect(a.mul(&b.add(c)).eql(a.mul(&b).add(a.mul(&c))));
        try expect(b.mul(&a.add(c)).eql(b.mul(&a).add(b.mul(&c))));
        try expect(c.mul(&a.add(b)).eql(c.mul(&a).add(c.mul(&b))));
        try expect(a.add(b).square().eql(
            a.square().add(b.square()).add(a.mul(&b).double()),
        ));
        try expect(b.add(c).square().eql(
            b.square().add(c.square()).add(b.mul(&c).double()),
        ));
        try expect(c.add(a).square().eql(
            c.square().add(a.square()).add(c.mul(&a).double()),
        ));

        // Power
        var a_100 = one;
        var b_100 = one;
        var c_100 = one;
        for (0..rnd_u8) |_| {
            a_100 = a_100.mul(&a);
            b_100 = b_100.mul(&b);
            c_100 = c_100.mul(&c);
        }
        try expect(a.powToBigInt(bigint_rnd_u8).eql(a_100));
        try expect(b.powToBigInt(bigint_rnd_u8).eql(b_100));
        try expect(c.powToBigInt(bigint_rnd_u8).eql(c_100));
        try expect(a.powToInt(rnd_u8).eql(a_100));
        try expect(b.powToInt(rnd_u8).eql(b_100));
        try expect(c.powToInt(rnd_u8).eql(c_100));
    }
}

test "Felt252: fromInt operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate random unsigned integers of different sizes.
        const u_8 = random.int(u8);
        const u_16: u16 = u_8;
        const u_32: u32 = u_8;
        const u_64: u64 = u_8;
        const u_128: u128 = u_8;
        const u_256: u256 = u_8;

        // Test the equality of `Felt252` instances created from different-sized integers.
        try expect(Felt252.fromInt(u8, u_8).eql(Felt252.fromInt(u16, u_16)));
        try expect(Felt252.fromInt(u8, u_8).eql(Felt252.fromInt(u32, u_32)));
        try expect(Felt252.fromInt(u8, u_8).eql(Felt252.fromInt(u64, u_64)));
        try expect(Felt252.fromInt(u8, u_8).eql(Felt252.fromInt(u128, u_128)));
        try expect(Felt252.fromInt(u8, u_8).eql(Felt252.fromInt(u256, u_256)));
    }
}

test "Felt252: modulus properties checks" {
    try expect(comptime Felt252.canUseNoCarryMulOptimization());
    try expect(comptime Felt252.modulusHasSpareBit());
}
