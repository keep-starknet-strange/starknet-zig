const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const Felt252 = @import("../../math/fields/starknet.zig").Felt252;

/// Errors that can occur during hex conversion.
pub const FromHexError = error{
    /// The length of the hex string is unexpected.
    UnexpectedLength,
    /// The hex string is invalid.
    InvalidHexString,
};

/// Hash256 structure representing a 256-bit hash.
pub const Hash256 = struct {
    const Self = @This();

    /// Byte count representing the size of the hash.
    pub const byte_count: usize = 32;

    /// Expected length of the hexadecimal string representation of the hash.
    const expected_hex_length = byte_count * 2;

    /// Inner byte representation of the hash.
    inner: [byte_count]u8 = [_]u8{0x00} ** byte_count,

    /// Constructs a `Hash256` from a hexadecimal string.
    ///
    /// # Arguments
    ///
    /// - `allocator`: An allocator to allocate memory.
    /// - `hex`: A hexadecimal string representing the hash.
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

        var res: Self = .{};

        // Check if the length of the hexadecimal string is within the expected range.
        if (hex[idx_start..].len <= expected_hex_length) {
            // Concatenate "0x0" with the hexadecimal string.
            const h = try std.mem.concat(
                allocator,
                u8,
                &[_][]const u8{ "0x0", hex[idx_start..] },
            );
            // Deallocate the concatenated string when function exits.
            defer allocator.free(h);

            // Parse the hexadecimal string into a u256 integer and write it to the inner representation of Hash256.
            std.mem.writeInt(
                u256,
                &res.inner,
                std.fmt.parseInt(u256, h, 0) catch
                    return FromHexError.InvalidHexString,
                .big,
            );
            return res;
        }
        // If the length is not within the expected range, return UnexpectedLength error.
        return FromHexError.UnexpectedLength;
    }

    /// Constructs a `Hash256` from a `u256` integer.
    ///
    /// # Arguments
    ///
    /// - `int`: A `u256` integer representing the hash.
    ///
    /// # Returns
    ///
    /// Returns a new `Hash256` constructed from the provided `u256` integer.
    pub fn fromInt(int: u256) Self {
        // Initialize a new Hash256.
        var res: Self = .{};

        // Write the provided u256 integer to the inner representation of Hash256.
        std.mem.writeInt(
            u256,
            &res.inner,
            int,
            .big,
        );
        return res;
    }

    /// Constructs a `Hash256` from a `Felt252`.
    ///
    /// # Arguments
    ///
    /// - `felt`: A `Felt252` representing the hash.
    ///
    /// # Returns
    ///
    /// Returns `Self` on success, otherwise returns a `FromFieldElementError`.
    pub fn fromFelt(felt: Felt252) !Self {
        // Initialize a new Hash256.
        var res: Self = .{};

        // Convert the Felt252 to a u256 integer and write it to the inner representation of Hash256.
        std.mem.writeInt(
            u256,
            &res.inner,
            try felt.toInt(u256),
            .big,
        );
        return res;
    }
};

const test_hashes = [_][]const u8{
    "0xcf40670837166aba9d9c05896e551c8f0009ce56cb3096b9839621a16b43aaab",
    "0x269e154d79895caadad93ffe6394f837aadc6eb3c3290467d9f46d70bc47f8fb",
    "0x1c008ae0f44250f18dfcbf847be4411fb6afdbc77caec0125e5b5a6008b84836",
    "0x2031e2f073e17c97b35526f12cfb71b2b3c38dd94b88f7f6f0223dc28cef9cf4",
    "0xbc8343e33697ed71b3d52551e71323cd0d3bd70b569cd88ba061a6134ddd7cc0",
    "0x690636eed190034a52c1abea392a0a066cc1b90688a10c9fd537b1f15559d529",
    "0x6cb12e4dc52d339716f770eb8934fd22231dd11ab2e235e3991bdbafc07cd204",
    "0xf18319b8d679c52123d6af1a151f390503faee900936aa6c8176d94f4bee64c4",
    "0x41adaebc069a454492c60d1641428af95bdbb807de3f6c100a5bea687511f25f",
    "0x86811137bafdd1fd21402cac9c25acabc242bdc3ca4d37fa0cda1792170ce9b5",
    "6853cc9a5e7f757185c2b46956b091b962d492e5f6c0d82de536a13f0b7ace12",
    "3954263a51a4c5ffe847a4cffa9e64c72350230007e097229dc1a04349e14508",
    "2d9574cacaf37c7877447eb9b4ed2c18703ae8c7f4bf93b159a967891d586792",
    "2524148348aa26bd9b03a02db8d0246a89d70962780c81c74b123807da2a3db4",
    "586bbc0e5c42ccbbfb792e9921519bd07c4906a490b18237c37b539a48370bb3",
    "727086b53a1ddcecbef149e44209c001990d2f18990528b0ba3a505f8e003b94",
    "73128e7050d582f67d56ccb16c4cf9159b40e0d26be39ecf29a0083eba585e8c",
    "2a9e8c8149562c7d3ec8eb8f0021b04b9b2a839d8890fb2e038546d8cfb30d07",
    "f572677b5720de866ba2f58fad09a363bc57c013d85fdc4799ce39af8c081517",
    "538ed95bb3e8bfe409cef8d749dba762e88b7ff5d22914204b66de1146cbc5b6",
    "0x5ee691c441b063a2b0a711ff4b15286f3eb71776dccad3935955676a93c59f54",
    "0x333ed4ab6b2aaa25e17abdeba5e3714f2386d3b855d394717560e67f68faa1ec",
    "0x2acfb811e847c2e6dcd7cb192f3ba0a662a9849901f2ddf63eb50a111741807a",
    "0x1ff7216b91f22277aa291a54dca5acb3aa553e42741498fcf3f7473dfe2c7c32",
    "0x4174ae142e7ce83870712803f8dc8975d13b052d47fac006edfb0dfc73318122",
    "0xafb1c1549c75b1c02ed94672bfb5f65a59ce975a6ec12c654bea211e553d62c1",
    "0xc4b33424588bd96b086a8a1394aae642f724c06bc6e33e88d9d418aa280be9d1",
    "0xe7825f3b211fd474dc8f85f95bf7883c5dc6923602039162aa52d8744981cdb5",
    "0x3f22402f226e0c627da26b6bd781f75031a08492cbff0cbbd8ef20370a3bddf8",
    "0x25c5b1592b1743b62d7fabd4373d98219c2ff3750f49ec0608a8355fa3bb060f",
    "0x",
};

test "Hash256: generate hash 256 from hex string" {
    for (test_hashes) |hash| {
        // Determine the start index based on whether the string starts with "0x".
        var idx_start: usize = 0;

        if (std.mem.indexOf(u8, hash, "0x")) |i| {
            if (i == 0) idx_start = 2;
        }

        // Concatenate "0x0" with the hexadecimal string.
        const int = try std.mem.concat(
            std.testing.allocator,
            u8,
            &[_][]const u8{ "0x0", hash[idx_start..] },
        );

        // Deallocate the concatenated string when the function exits.
        defer std.testing.allocator.free(int);

        // Assert that the `Hash256` generated from the integer representation of the hexadecimal
        // string matches the one generated directly from the hexadecimal string.
        try expectEqual(
            try Hash256.fromHex(std.testing.allocator, hash),
            Hash256.fromInt(try std.fmt.parseInt(u256, int, 0)),
        );
    }
}

test "Hash256: generate hash 256 shoul return an error if length is exceeded" {
    // Verify that attempting to generate a `Hash256` from a hexadecimal string with exceeded
    // length results in an UnexpectedLength error.
    try expectError(
        FromHexError.UnexpectedLength,
        Hash256.fromHex(
            std.testing.allocator,
            "0x25c5b1592b1743b62d7fabd4373d98219c2ff3750f49ec0608a8355fa3bb060fF",
        ),
    );
}

test "Hash256: generate hash 256 from Felt" {
    for (test_hashes) |hash| {
        // Determine the start index based on whether the string starts with "0x".
        var idx_start: usize = 0;

        if (std.mem.indexOf(u8, hash, "0x")) |i| {
            if (i == 0) idx_start = 2;
        }

        // Concatenate "0x0" with the hexadecimal string.
        const int = try std.mem.concat(
            std.testing.allocator,
            u8,
            &[_][]const u8{ "0x0", hash[idx_start..] },
        );

        // Deallocate the concatenated string when the function exits.
        defer std.testing.allocator.free(int);

        // Assert that the `Hash256` generated directly from the hexadecimal string
        // matches the one generated from the `Felt252` representing the same hash.
        try expectEqual(
            Hash256.fromInt(
                Felt252.fromInt(
                    u256,
                    try std.fmt.parseInt(u256, int, 0),
                ).toU256(),
            ),
            try Hash256.fromFelt(
                Felt252.fromInt(
                    u256,
                    try std.fmt.parseInt(u256, int, 0),
                ),
            ),
        );
    }
}
