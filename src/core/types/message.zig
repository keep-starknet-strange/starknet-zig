const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;
const expectEqualSlices = std.testing.expectEqualSlices;
const expectEqualDeep = std.testing.expectEqualDeep;

const Felt252 = @import("../../math/fields/starknet.zig").Felt252;
const EthAddress = @import("./eth_address.zig").EthAddress;
const Hash256 = @import("./hash256.zig").Hash256;

// Structure representing a message sent from L2 to L1.
pub const MessageToL2 = struct {
    const Self = @This();

    /// The Ethereum address of the sender on L1.
    from_address: EthAddress,
    /// The target contract address on L2.
    to_address: Felt252,
    /// The function selector for the contract on L1.
    selector: Felt252,
    /// The payload of the message.
    /// This contains the data to be sent to the contract on L1.
    payload: std.ArrayList(Felt252),
    /// Nonce to avoid hash collisions between different L1 handler transactions.
    nonce: u64,

    /// Computes the hash of the message.
    ///
    /// This method calculates the hash of the entire message structure, including
    /// sender address, recipient address, function selector, payload, and nonce. It
    /// utilizes the Keccak256 hashing algorithm to produce a 256-bit hash value.
    ///
    /// Returns: Hash256 - The hash of the message.
    pub fn hash(self: *Self) Hash256 {
        // Initialize a Keccak256 hash function.
        var hasher = std.crypto.hash.sha3.Keccak256.init(.{});

        // Update hash with padding and sender's address.
        hasher.update(&[_]u8{0} ** 12);
        hasher.update(&self.from_address.inner);

        // Update hash with recipient address on L2.
        hasher.update(&self.to_address.toBytesBe());

        // Update hash with nonce.
        hasher.update(&[_]u8{0} ** 24);
        var buf: [8]u8 = undefined;
        std.mem.writeInt(u64, &buf, self.nonce, .big);
        hasher.update(&buf);

        // Update hash with function selector.
        hasher.update(&self.selector.toBytesBe());

        // Update hash with payload length.
        hasher.update(&[_]u8{0} ** 24);
        std.mem.writeInt(u64, &buf, self.payload.items.len, .big);
        hasher.update(&buf);

        // Update hash with payload items.
        for (self.payload.items) |item|
            hasher.update(&item.toBytesBe());

        // Finalize the hash and return the result.
        var hash_bytes: [Hash256.byte_count]u8 = undefined;
        hasher.final(&hash_bytes);
        return .{ .inner = hash_bytes };
    }

    // Deallocate memory
    pub fn deinit(self: *Self) void {
        self.payload.deinit();
    }
};

// Structure representing a message sent from L1 to L2.
pub const MessageToL1 = struct {
    const Self = @This();

    /// The address of the L2 contract sending the message.
    from_address: Felt252,
    /// The target L1 address the message is sent to.
    to_address: Felt252,
    /// The payload of the message.
    /// This contains the data to be sent to the contract on L2.
    payload: std.ArrayList(Felt252),

    /// Computes the hash of the message.
    ///
    /// This method calculates the hash of the entire message structure, including
    /// sender address, recipient address, and payload. It utilizes the Keccak256
    /// hashing algorithm to produce a 256-bit hash value.
    ///
    /// Returns: Hash256 - The hash of the message.
    pub fn hash(self: *Self) Hash256 {
        // Initialize a Keccak256 hash function.
        var hasher = std.crypto.hash.sha3.Keccak256.init(.{});

        // Update hash with sender's address.
        hasher.update(&self.from_address.toBytesBe());

        // Update hash with recipient address on L2.
        hasher.update(&self.to_address.toBytesBe());

        // Update hash with payload length.
        hasher.update(&[_]u8{0} ** 24);
        var buf: [8]u8 = undefined;
        std.mem.writeInt(u64, &buf, self.payload.items.len, .big);
        hasher.update(&buf);

        // Update hash with payload items.
        for (self.payload.items) |item|
            hasher.update(&item.toBytesBe());

        // Finalize the hash and return the result.
        var hash_bytes: [Hash256.byte_count]u8 = undefined;
        hasher.final(&hash_bytes);
        return .{ .inner = hash_bytes };
    }

    // Deallocate memory
    pub fn deinit(self: *Self) void {
        self.payload.deinit();
    }
};

test "MessageToL1: hash a message from L2 to L1" {
    // Define a set of test messages including sender address, recipient address,
    // payload, and expected message hash.
    const messages = [_]struct {
        /// The address of the L2 contract sending the message
        from_address: Felt252,
        /// The target L1 address the message is sent to
        to_address: Felt252,
        /// The payload of the message
        payload: []const Felt252,
        /// Hash of the message
        message_hash: u256,
    }{
        .{
            .from_address = Felt252.fromInt(
                u256,
                0x0710851e5f08a67ef2f7ea6814bfa4dc8976505c20e05519d7694d2c3aca433b,
            ),
            .to_address = Felt252.fromInt(
                u256,
                0x706574cd158bffef3a3bbeb2288efb3ced3db1ff,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(u256, 0xc),
                Felt252.fromInt(u256, 0x22),
            },
            .message_hash = 0x623291a51d0f17c25b434684f150c27387ba16acf0633b3d9d529a08f8a89e86,
        },
        .{
            .from_address = Felt252.fromInt(
                u256,
                0x0164cba33fb7152531f6b4cfc3fff26b4d7b26b4900e0881042edd607b428a92,
            ),
            .to_address = Felt252.fromInt(
                u256,
                0x000000000000000000000000b6dbfaa86bb683152e4fc2401260f9ca249519c0,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(u256, 0x0),
                Felt252.fromInt(u256, 0x0),
                Felt252.fromInt(u256, 0x0182b8),
                Felt252.fromInt(u256, 0x0),
                Felt252.fromInt(u256, 0x0384),
                Felt252.fromInt(u256, 0x0),
            },
            .message_hash = 0x326a04493fc8f24ac6c6ae7bdba23243ce03ec3aae53f0ed3a0d686eb8cac930,
        },
        .{
            .from_address = Felt252.fromInt(
                u256,
                0x024434fb273a1ee1ac0d27638fd7a4486ab415129fee5ec0a84611f2fd77cd7f,
            ),
            .to_address = Felt252.fromInt(
                u256,
                0x600fe6eaacbaefb1afa8faaafaeca5af3dd9bcc7,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(u256, 0xc),
                Felt252.fromInt(u256, 0x22),
            },
            .message_hash = 0x468d136ba58f2d4d89c13989dcc5850b9d50062985a6e9a9c70f9c369a091403,
        },
        .{
            .from_address = Felt252.fromInt(
                u256,
                0x0710851e5f08a67ef2f7ea6814bfa4dc8976505c20e05519d7694d2c3aca433b,
            ),
            .to_address = Felt252.fromInt(
                u256,
                0xadc0bd2dfabaaddafc787c4bfeb0fc87a72eaac2,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(u256, 0xc),
                Felt252.fromInt(u256, 0x22),
            },
            .message_hash = 0x86a4ef9c6e51866c7af125e38af99679e31580449c4e914fd659031611f926bb,
        },
        .{
            .from_address = Felt252.fromInt(
                u256,
                0x024434fb273a1ee1ac0d27638fd7a4486ab415129fee5ec0a84611f2fd77cd7f,
            ),
            .to_address = Felt252.fromInt(
                u256,
                0xfe7816e4f8f5f81b79ae863ef10f60ef1b4a8ae3,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(u256, 0xc),
                Felt252.fromInt(u256, 0x22),
            },
            .message_hash = 0x4516cd907b76da4e53da5a9acbbe016826e6e625195a7afee5d0d632c4f50065,
        },
        .{
            .from_address = Felt252.fromInt(
                u256,
                0x024434fb273a1ee1ac0d27638fd7a4486ab415129fee5ec0a84611f2fd77cd7f,
            ),
            .to_address = Felt252.fromInt(
                u256,
                0xfbc712b24a4fcff673de879f2bf89c5ee0aaa63d,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(u256, 0xc),
                Felt252.fromInt(u256, 0x22),
            },
            .message_hash = 0x0175e45959b1a7e290e96b7f1cc249a1a8852ab41e72d268b19d538c2009638b,
        },
    };

    // Iterate through each test message.
    for (messages) |message| {
        // Initialize an array list to store the payload.
        var payload = std.ArrayList(Felt252).init(std.testing.allocator);

        // Iterate through each item in the message payload and append it to the array list.
        for (message.payload) |p|
            try payload.append(p);

        // Create a MessageToL1 instance with the message details.
        var m: MessageToL1 = .{
            .from_address = message.from_address,
            .to_address = message.to_address,
            .payload = payload,
        };
        // Ensure deallocation of message resources.
        defer m.deinit();

        // Verify that the computed hash matches the expected message hash.
        try expectEqualDeep(Hash256.fromInt(message.message_hash), m.hash());
    }
}

test "MessageToL2: hash a message from L1 to L2" {
    const messages = [_]struct {
        /// The Ethereum address of the sender on L1.
        from_address: EthAddress,
        /// The target L2 address the message is sent to.
        to_address: Felt252,
        /// The function selector for the contract on L1.
        selector: Felt252,
        /// The payload of the message.
        /// This contains the data to be sent to the contract on L1.
        payload: []const Felt252,
        /// Hash of the message.
        message_hash: u256,
        /// Nonce to avoid hash collisions between different L1 handler transactions.
        nonce: u64,
    }{
        .{
            .from_address = EthAddress.fromInt(0xc3511006C04EF1d78af4C8E0e74Ec18A6E64Ff9e),
            .to_address = Felt252.fromInt(
                u256,
                0x73314940630fd6dcda0d772d4c972c4e0a9946bef9dabf4ef84eda8ef542b82,
            ),
            .selector = Felt252.fromInt(
                u256,
                0x2d757788a8d8d6f21d1cd40bce38a8222d70654214e96ff95d8086e684fbee5,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(
                    u256,
                    0x689ead7d814e51ed93644bc145f0754839b8dcb340027ce0c30953f38f55d7,
                ),
                Felt252.fromInt(u256, 0x2c68af0bb140000),
                Felt252.fromInt(u256, 0x0),
            },
            .nonce = 775628,
            .message_hash = 0xc51a543ef9563ad2545342b390b67edfcddf9886aa36846cf70382362fc5fab3,
        },
        .{
            .from_address = EthAddress.fromInt(0xeccd821d0322fbc176497ae39fd2a05a5072573f),
            .to_address = Felt252.fromInt(
                u256,
                0x07fd01e7edd2a555ff389efb8335b75c3e3372f8f77aab4902a0bdb28e885975,
            ),
            .selector = Felt252.fromInt(
                u256,
                0x03636c566f6409560d55d5f6d1eb4ee163b096b4698c503e69e210be79de2afa,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(u256, 0x78),
                Felt252.fromInt(u256, 0x0),
                Felt252.fromInt(u256, 0x5db3cc6d76acec9582cac3a93a061e628a82218f),
                Felt252.fromInt(u256, 0x16345785d8a0000),
                Felt252.fromInt(u256, 0x0),
            },
            .nonce = 4433,
            .message_hash = 0x36a1da35d6bf1166fac4a0eb366f58c1c336a82206b36b652159fa0735872dd8,
        },
        .{
            .from_address = EthAddress.fromInt(0xdf1749d882ead070cc4aa69b74099ca5e4735bde),
            .to_address = Felt252.fromInt(
                u256,
                0x0534233eb95a16b0d7aeb0fc61c28bf4851dd9db65c26da713147158d4921c93,
            ),
            .selector = Felt252.fromInt(
                u256,
                0x03a493c40bf366f3d64e83bea39bf20faadd8299c0639a7c31db908d136ea42e,
            ),
            .payload = &[_]Felt252{
                Felt252.fromInt(u256, 0x11eacac3e378147d46150d6923a183403b05c0cc),
                Felt252.fromInt(u256, 0xf3cf63d2d52e6a4e75028a965f9ce4c5e3d9432a),
                Felt252.fromInt(u256, 0x4eccd262bb9aee6a7a35e5996ab299aca3dfaa560354d8543804e75a127a312),
                Felt252.fromInt(u256, 0x2540be400),
                Felt252.fromInt(u256, 0x0),
                Felt252.fromInt(u256, 0x5f5e100),
                Felt252.fromInt(u256, 0x0),
                Felt252.fromInt(
                    u256,
                    0x4eccd262bb9aee6a7a35e5996ab299aca3dfaa560354d8543804e75a127a312,
                ),
                Felt252.fromInt(u256, 0x9),
                Felt252.fromInt(
                    u256,
                    0x239c3f1deaeeae3d48f2e4fa80eacd798228bd4048a6e7cb49a332123d33270,
                ),
                Felt252.fromInt(
                    u256,
                    0x7fdd30e5c5f665ab0424325a32d2bc98b4c2da77923851d8aa1701dead305aa,
                ),
                Felt252.fromInt(u256, 0x1),
                Felt252.fromInt(u256, 0x989680),
                Felt252.fromInt(u256, 0x0),
                Felt252.fromInt(u256, 0x7a6b787a6b787a6b78),
                Felt252.fromInt(u256, 0x7a6b787a6b787a6b78),
                Felt252.fromInt(
                    u256,
                    0x4a568581c0c94c4c6a0eef518fa67f1976bffa2dfac12ea6bba452ef81e99d5,
                ),
                Felt252.fromInt(
                    u256,
                    0x25bcb079cb1d5bde2931b0655d9990f3dacf75973216b3db793c78e2db518fe,
                ),
            },
            .nonce = 4447,
            .message_hash = 0x16a619b7c4d3e693804979eb6ed8a43b4a2f85a06776bc1ca69d2561bb1b721f,
        },
    };

    // Iterate through each test message.
    for (messages) |message| {
        // Initialize an array list to store the payload.
        var payload = std.ArrayList(Felt252).init(std.testing.allocator);

        // Iterate through each item in the message payload and append it to the array list.
        for (message.payload) |p|
            try payload.append(p);

        // Create a MessageToL2 instance with the message details.
        var m: MessageToL2 = .{
            .from_address = message.from_address,
            .to_address = message.to_address,
            .payload = payload,
            .nonce = message.nonce,
            .selector = message.selector,
        };

        // Ensure deallocation of message resources.
        defer m.deinit();

        // Verify that the computed hash matches the expected message hash.
        try expectEqualDeep(Hash256.fromInt(message.message_hash), m.hash());
    }
}
