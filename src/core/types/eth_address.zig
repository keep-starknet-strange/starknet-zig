const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const Felt252 = @import("../../math/fields/starknet.zig").Felt252;

/// Maximum L1 address.
pub const MAX_L1_ADDRESS = Felt252.fromInt(
    u256,
    0xFFfFfFffFFfffFFfFFfFFFFFffFFFffffFfFFFfF,
);

/// Errors that can occur during hex conversion.
pub const FromHexError = error{
    /// The length of the hex string is unexpected.
    UnexpectedLength,
    /// The hex string is invalid.
    InvalidHexString,
};

/// Ethereum address.
pub const EthAddress = struct {
    const Self = @This();

    /// Inner byte representation of the address.
    inner: [20]u8 = [_]u8{0x00} ** 20,

    /// Constructs an `EthAddress` from a hexadecimal string.
    ///
    /// This function takes an allocator and a hexadecimal string `hex` as input. It constructs an `EthAddress` from the hexadecimal string.
    ///
    /// # Arguments
    ///
    /// - `allocator`: An allocator to allocate memory.
    /// - `hex`: A hexadecimal string representing the address.
    ///
    /// # Returns
    ///
    /// Returns `Self` on success, otherwise returns a `FromHexError`.
    pub fn fromHex(allocator: std.mem.Allocator, hex: []const u8) !Self {
        var idx_start: usize = 0;

        // Check if the string starts with "0x", adjust the index accordingly.
        if (std.mem.indexOf(u8, hex, "0x")) |i| {
            if (i == 0) idx_start = 2;
        }

        // Check if the length of the hexadecimal string is 40 characters.
        if (hex[idx_start..].len == 40) {
            // Concatenate "0x" with the hexadecimal string.
            const h = try std.mem.concat(
                allocator,
                u8,
                &[_][]const u8{ "0x", hex[idx_start..] },
            );
            // Deallocate the concatenated string when function exits.
            defer allocator.free(h);

            // Initialize the result EthAddress.
            var res: Self = .{};

            // Parse the hexadecimal string into a u160 integer and write it to the inner representation of EthAddress.
            std.mem.writeInt(
                u160,
                &res.inner,
                std.fmt.parseInt(u160, h, 0) catch
                    return FromHexError.InvalidHexString,
                .big,
            );
            return res;
        }
        // If the length is not 40 characters, return UnexpectedLength error.
        return FromHexError.UnexpectedLength;
    }

    /// Constructs an `EthAddress` from a `u160` integer.
    ///
    /// # Arguments
    ///
    /// - `int`: A `u160` integer representing the address.
    ///
    /// # Returns
    ///
    /// Returns a new `EthAddress` constructed from the provided `u160` integer.
    pub fn fromInt(int: u160) Self {
        // Initialize a new EthAddress.
        var res: Self = .{};

        // Write the provided u160 integer to the inner representation of EthAddress.
        std.mem.writeInt(
            u160,
            &res.inner,
            int,
            .big,
        );
        return res;
    }

    /// Constructs an `EthAddress` from a `Felt252`.
    ///
    /// This function takes a `Felt252` and constructs an `EthAddress` from it.
    ///
    /// # Arguments
    ///
    /// - `felt`: A `Felt252` representing the address.
    ///
    /// # Returns
    ///
    /// Returns `Self` on success, otherwise returns a `FromFieldElementError`.
    pub fn fromFelt(felt: Felt252) !Self {
        // Check if the provided Felt252 is less than or equal to the maximum L1 address.
        if (felt.lte(&MAX_L1_ADDRESS)) {
            // Initialize a new EthAddress.
            var res: Self = .{};

            // Convert the Felt252 to a u160 integer and write it to the inner representation of EthAddress.
            std.mem.writeInt(
                u160,
                &res.inner,
                try felt.toInt(u160),
                .big,
            );
            return res;
        }
        // If the provided Felt252 is greater than the maximum L1 address, return FromFieldElementError.
        return error.FromFieldElementError;
    }
};

const test_addresses = [_][]const u8{
    "0x00000000219ab540356cbb839cbe05303d7705fa",
    "0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2",
    "0xbe0eb53f46cd790cd13851d5eff43d12404d33e8",
    "0x8315177ab297ba92a06054ce80a67ed4dbd7ed3a",
    "0x40b38765696e3d5d8d9d834d8aad4bb6e418e489",
    "0xda9dfa130df4de4673b89022ee50ff26f6ea73cf",
    "0x47ac0fb4f2d84898e4d9e7b4dab3c24507a6d503",
    "0xf977814e90da44bfa03b6295a0616a897441acec",
    "0xe92d1a43df510f82c66382592a047d288f85226f",
    "0xbeb5fc579115071764c7423a4f12edde41f106ed",
    "0xafcd96e580138cfa2332c632e66308eacd45c5da",
    "0x61edcdf5bb737adffe5043706e7c5bb1f1a56eea",
    "0x7d6149ad9a573a6e2ca6ebf7d4897c1b766841b4",
    "0xc61b9bb3a7a0767e3179713f3a5c7a9aedce193c",
    "0xca8fa8f0b631ecdb18cda619c4fc9d197c8affca",
    "0xde0b295669a9fd93d5f28d9ec85e40f4cb697bae",
    "0x3bfc20f0b9afcace800d73d2191166ff16540258",
    "0x8103683202aa8da10536036edef04cdd865c225e",
    "0x28c6c06298d514db089934071355e5743bf21d60",
    "0xdf9eb223bafbe5c5271415c75aecd68c21fe3d7f",
    "0x8696e84ab5e78983f2456bcb5c199eea9648c8c2",
    "0x267be1c1d684f78cb4f6a176c4911b741e4ffdc0",
    "0x49048044d57e1c92a77f79988d21fa8faf74e97e",
    "0xf3b0073e3a7f747c7a38b36b805247b222c302a3",
    "0xbf3aeb96e164ae67e763d9e050ff124e7c3fdd28",
    "0x9e927c02c9eadae63f5efb0dd818943c7262fb8e",
    "0x8484ef722627bf18ca5ae6bcf031c23e6e922b30",
    "0x32400084c286cf3e17e7b677ea9583e60a000324",
    "0x5b5b69f4e0add2df5d2176d7dbd20b4897bc7ec4",
    "0xe25a329d385f77df5d4ed56265babe2b99a5436e",
    "0x7da82c7ab4771ff031b66538d2fb9b0b047f6cf9",
    "0x15c22df3e71e7380012668fb837c537d0f8b38a1",
    "0x0e58e8993100f1cbe45376c410f97f4893d9bfcd",
    "0x2f2d854c1d6d5bb8936bb85bc07c28ebb42c9b10",
    "0x1db92e2eebc8e0c075a02bea49a2935bcd2dfcf4",
    "0x0c23fc0ef06716d2f8ba19bc4bed56d045581f2d",
    "0xfd898a0f677e97a9031654fc79a27cb5e31da34a",
    "0xb8cda067fabedd1bb6c11c626862d7255a2414fe",
    "0x701c484bfb40ac628afa487b6082f084b14af0bd",
    "0x9c2fc4fc75fa2d7eb5ba9147fa7430756654faa9",
    "0xb20411c403687d1036e05c8a7310a0f218429503",
    "0x9a1ed80ebc9936cee2d3db944ee6bd8d407e7f9f",
    "0xba18ded5e0d604a86428282964ae0bb249ceb9d0",
    "0xb9fa6e54025b4f0829d8e1b42e8b846914659632",
    "0x8d95842b0bca501446683be598e12f1c616770c1",
    "0x35aeed3aa9657abf8b847038bb591b51e1e4c69f",
    "0xb93d8596ac840816bd366dc0561e8140afd0d1cb",
    "0x4ed97d6470f5121a8e02498ea37a50987da0eec0",
    "0x0000000000000000000000000000000000000000",
    "b20411c403687d1036e05c8a7310a0f218429503",
    "9a1ed80ebc9936cee2d3db944ee6bd8d407e7f9f",
    "ba18ded5e0d604a86428282964ae0bb249ceb9d0",
    "b9fa6e54025b4f0829d8e1b42e8b846914659632",
};

test "EthAddress: generate address from hex as string" {
    for (test_addresses) |add| {
        // Determine the start index based on whether the string starts with "0x".
        var idx_start: usize = 0;

        if (std.mem.indexOf(u8, add, "0x")) |i| {
            if (i == 0) idx_start = 2;
        }

        // Concatenate "0x" with the hexadecimal string.
        const int = try std.mem.concat(
            std.testing.allocator,
            u8,
            &[_][]const u8{ "0x", add[idx_start..] },
        );

        // Deallocate the concatenated string when the function exits.
        defer std.testing.allocator.free(int);

        // Assert that the `EthAddress` generated from the integer representation of the hexadecimal
        // string matches the one generated directly from the hexadecimal string.
        try expectEqual(
            EthAddress.fromInt(try std.fmt.parseInt(u160, int, 0)),
            try EthAddress.fromHex(std.testing.allocator, add),
        );
    }
}

test "EthAddress: generate address from hex as string should return an error if hex len is not correct" {
    inline for (test_addresses) |add| {
        // Verify that attempting to generate an `EthAddress` from a hexadecimal string with
        // an incorrect length results in an UnexpectedLength error.
        try expectError(
            FromHexError.UnexpectedLength,
            EthAddress.fromHex(std.testing.allocator, add ++ "32"),
        );
        try expectError(
            FromHexError.UnexpectedLength,
            EthAddress.fromHex(std.testing.allocator, "32" ++ add),
        );
        try expectError(
            FromHexError.UnexpectedLength,
            EthAddress.fromHex(std.testing.allocator, "32" ++ add ++ "32"),
        );
        try expectError(
            FromHexError.UnexpectedLength,
            EthAddress.fromHex(std.testing.allocator, add[0..5]),
        );
    }
}

test "EthAddress: generate address from Felt252" {
    for (test_addresses) |add| {
        // Determine the start index based on whether the string starts with "0x".
        var idx_start: usize = 0;

        if (std.mem.indexOf(u8, add, "0x")) |i| {
            if (i == 0) idx_start = 2;
        }

        // Concatenate "0x" with the hexadecimal string.
        const int = try std.mem.concat(
            std.testing.allocator,
            u8,
            &[_][]const u8{ "0x", add[idx_start..] },
        );

        // Deallocate the concatenated string when the function exits.
        defer std.testing.allocator.free(int);

        // Assert that the `EthAddress` generated directly from the hexadecimal string
        // matches the one generated from the `Felt252` representing the same address.
        try expectEqual(
            try EthAddress.fromHex(std.testing.allocator, add),
            EthAddress.fromFelt(
                Felt252.fromInt(
                    u256,
                    try std.fmt.parseInt(u160, int, 0),
                ),
            ),
        );
    }
}

test "EthAddress: generate address from Felt252 should return error if greater than max address" {
    // Verify that attempting to generate an `EthAddress` from a `Felt252` greater than the
    // maximum address results in a FromFieldElementError.
    try expectError(
        error.FromFieldElementError,
        EthAddress.fromFelt(
            Felt252.fromInt(
                u256,
                MAX_L1_ADDRESS.toU256() + 1,
            ),
        ),
    );
}
