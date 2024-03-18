const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const Felt252 = @import("../math/fields/starknet.zig").Felt252;
const field_constants = @import("../math/fields/constants.zig");
const poseidon_constants = @import("./poseidon/constants.zig");
const CurveParams = @import("../math/curve/curve_params.zig");
const ProjectivePoint = @import("../math/curve/short_weierstrass/projective.zig").ProjectivePoint;
const AffinePoint = @import("../math/curve/short_weierstrass/affine.zig").AffinePoint;

/// The PoseidonHasher struct represents a hasher based on the Poseidon cryptographic primitive.
pub const PoseidonHasher = struct {
    /// The type alias for the current struct instance.
    const Self = @This();

    /// The state of the hasher.
    /// Initialized with the default value of Felt252 and repeated 3 times.
    state: [3]Felt252 = [_]Felt252{.{}} ** 3,

    /// The buffer for storing the input message.
    /// Nullable, initialized with null.
    buffer: ?Felt252 = null,

    /// Updates the hasher state with a new message.
    ///
    /// This function updates the state of the Poseidon hasher with a new message. If the hasher has a
    /// pending message buffered, it combines the buffered message with the new message and applies the
    /// permutation computation (`permuteComp()`) to update the hasher state. Otherwise, it buffers the
    /// new message for subsequent hashing.
    ///
    /// Parameters:
    /// - `self`: A pointer to the current struct instance.
    /// - `message`: The Felt252 message to be incorporated into the hasher state.
    pub fn update(self: *Self, message: Felt252) void {
        if (self.buffer) |*previous_message| {
            // Combine buffered message with the new message and update the state.
            self.state[0].addAssign(previous_message);
            self.state[1].addAssign(&message);
            self.permuteComp();
            self.buffer = null;
        } else {
            // Buffer the new message.
            self.buffer = message;
        }
    }

    /// Finalizes the hashing process and returns the resulting hash.
    ///
    /// This function finalizes the hashing process by incorporating any buffered message into the
    /// hasher state. If there is a buffered message, it combines it with a one (Felt252.one()) and
    /// updates the state before applying the permutation computation (`permuteComp()`) to obtain the
    /// final hash. If there is no buffered message, it treats a one as if paired with the last
    /// element of the state.
    ///
    /// Returns:
    /// The resulting hash as a Felt252 element.
    pub fn finalize(self: *Self) Felt252 {
        if (self.buffer) |*last_message| {
            // Combine buffered message with a one and update the state.
            self.state[0].addAssign(last_message);
            self.state[1].addAssign(&Felt252.one());
            self.buffer = null;
        } else {
            // Treat a one as if paired with the last element of the state.
            self.state[0].addAssign(&Felt252.one());
        }
        // Apply the permutation computation to obtain the final hash.
        self.permuteComp();
        return self.state[0];
    }

    /// Performs the Poseidon permutation computation based on the HADES design strategy for hashing.
    ///
    /// The HADES design strategy incorporates different types of rounds within the same permutation
    /// construction, utilizing both full S-box layers and partial S-box layers. This strategy aims to
    /// provide a balance between computational efficiency and security against statistical and
    /// algebraic attacks.
    ///
    /// The permutation consists of three phases:
    /// 1. R_f rounds at the beginning and end of the permutation, applying S-boxes to the full state.
    /// 2. R_p rounds in the middle, containing only a single S-box in each round, while the rest of
    ///    the state remains unchanged (i.e., identity functions are used).
    /// 3. R_f rounds at the end, applying S-boxes to the full state again.
    ///
    /// This approach enhances security against statistical attacks by utilizing full S-box layers at
    /// the beginning and end, together with the wide trail strategy. Meanwhile, the use of partial
    /// S-box layers in the middle rounds increases the overall function's degree, providing additional
    /// protection against algebraic attacks.
    ///
    /// For further details, refer to the paper "The HADES Design Strategy for Hashing."
    pub fn permuteComp(self: *Self) void {
        var idx: usize = 0;

        // Apply full rounds at the beginning.
        for (0..poseidon_constants.POSEIDON_FULL_ROUNDS / 2) |_| {
            self.roundComp(idx, true);
            idx += 3;
        }

        // Apply partial rounds in the middle.
        for (0..poseidon_constants.POSEIDON_PARTIAL_ROUNDS) |_| {
            self.roundComp(idx, false);
            idx += 1;
        }

        // Apply full rounds at the end.
        for (0..poseidon_constants.POSEIDON_FULL_ROUNDS / 2) |_| {
            self.roundComp(idx, true);
            idx += 3;
        }
    }

    /// Performs a single round of the Poseidon permutation computation based on the HADES design strategy,
    /// incorporating AddRoundConstants (ARC), SubWords (S-box), and MixLayer (M).
    ///
    /// Each round function consists of three components:
    /// 1. AddRoundConstants (ARC), denoted by ARC(·).
    /// 2. SubWords (S-box), denoted by S-box(·) or by SB(·).
    /// 3. MixLayer (M), denoted by M(·), which represents the linear layer of the construction.
    ///
    /// In each round, the operations are applied in the following order:
    /// ARC → SB → M
    ///
    /// During the permutation, the following pattern is observed:
    /// - The first and last rounds (R_f + R_f = R_F) have full S-box layers, each consisting of 't'
    ///   S-box functions.
    /// - The middle rounds (R_p) have partial S-box layers, with one S-box and (t - 1) identity functions.
    ///
    /// The MixLayer operation (M) involves multiplying the state with a t × t MDS matrix, which applies
    /// the wide trail strategy to enhance security against cryptographic attacks.
    ///
    /// For more detailed information about the HADES design strategy, refer to [GLR+20].
    ///
    /// Parameters:
    /// - `idx`: The index indicating the position of the round within the permutation.
    /// - `full`: A boolean indicating whether the round contains a full S-box layer (true) or a
    ///   partial S-box layer (false).
    pub fn roundComp(self: *Self, idx: usize, comptime full: bool) void {
        if (full) {
            inline for (0..self.state.len) |i| {
                // AddRoundConstants.
                self.state[i].addAssign(&poseidon_constants.POSEIDON_COMPRESSED_ROUND_CONSTS[idx + i]);
                // SubWords.
                self.state[i] = self.state[i].powToInt(3);
            }
        } else {
            // AddRoundConstants for partial round.
            self.state[2].addAssign(&poseidon_constants.POSEIDON_COMPRESSED_ROUND_CONSTS[idx]);
            self.state[2] = self.state[2].powToInt(3);
        }

        // MixLayer.
        self.mix();
    }

    /// Performs mixing operations on the state as part of the Poseidon permutation computation.
    ///
    /// Mixing involves combining the state elements and applying arithmetic operations to achieve
    /// diffusion and non-linearity, enhancing the security properties of the permutation.
    ///
    /// The mixing operation consists of the following steps:
    /// 1. Summation of the state elements 'self.state[0]', 'self.state[1]', and 'self.state[2]'.
    /// 2. Doubling the value of 'self.state[0]', then adding the computed sum ('t').
    /// 3. Doubling the value of 'self.state[1]', negating it, and then adding 't'.
    /// 4. Multiplying 'self.state[2]' by a compile-time constant Felt252.three(), negating it, and then
    ///    adding 't'.
    ///
    /// Parameters:
    /// - `self`: A pointer to the current struct instance.
    pub inline fn mix(self: *Self) void {
        // Summation of state elements.
        const t = self.state[0].add(&self.state[1]).add(&self.state[2]);

        // Doubling and addition for state[0].
        self.state[0].doubleAssign();
        self.state[0].addAssign(&t);

        // Doubling, negation, and addition for state[1].
        self.state[1].doubleAssign();
        self.state[1].negAssign();
        self.state[1].addAssign(&t);

        // Multiplication, negation, and addition for state[2].
        self.state[2].mulAssign(&comptime Felt252.three());
        self.state[2].negAssign();
        self.state[2].addAssign(&t);
    }

    /// Hashes two elements and returns the resulting hash.
    pub fn hash(self: *Self, x: Felt252, y: Felt252) Felt252 {
        self.state = [_]Felt252{ x, y, Felt252.two() };
        self.permuteComp();
        return self.state[0];
    }

    /// Hashes a single element and returns the resulting hash.
    pub fn hashSingle(self: *Self, x: Felt252) Felt252 {
        self.state = [_]Felt252{ x, .{}, Felt252.one() };
        self.permuteComp();
        return self.state[0];
    }

    /// Hashes an array of elements and returns the resulting hash.
    ///
    /// This function takes an array of Felt252 elements and computes their hash using the Poseidon
    /// permutation. It iterates over the input elements, combining them in pairs and updating the
    /// internal state accordingly. If the array length is odd, it treats the last element as if paired
    /// with a one (Felt252.one()).
    ///
    /// After processing all input elements, the function applies the permutation computation
    /// (`permuteComp()`) to the final state to obtain the resulting hash.
    ///
    /// Parameters:
    /// - `self`: A pointer to the current struct instance.
    /// - `messages`: An array of Felt252 elements to be hashed.
    ///
    /// Returns:
    /// The resulting hash as a Felt252 element.
    pub fn hashMany(self: *Self, messages: []const Felt252) Felt252 {
        // Initialize the state with three Felt252 elements.
        self.state = [_]Felt252{.{}} ** 3;
        var idx: usize = 0;

        const messages_len = messages.len;

        // Process input elements in pairs.
        while (idx + 1 < messages_len) {
            // Combine pairs of elements and update the state.
            self.state[0].addAssign(&messages[idx]);
            self.state[1].addAssign(&messages[idx + 1]);
            self.permuteComp();
            idx += 2;
        }

        // Handle the case where the array length is odd.
        if (@mod(messages_len, 2) != 0) {
            self.state[0].addAssign(&messages[messages_len - 1]);
            self.state[1].addAssign(&Felt252.one());
        } else {
            self.state[0].addAssign(&Felt252.one());
        }

        // Apply the permutation computation to obtain the hash.
        self.permuteComp();
        return self.state[0];
    }
};

test "PoseidonHasher: Poseidon hash two elements" {
    const test_data = [_]std.meta.Tuple(&.{ Felt252, Felt252, Felt252 }){
        .{
            Felt252.fromInt(u256, 0xb662f9017fa7956fd70e26129b1833e10ad000fd37b4d9f4e0ce6884b7bbe),
            Felt252.fromInt(u256, 0x1fe356bf76102cdae1bfbdc173602ead228b12904c00dad9cf16e035468bea),
            Felt252.fromInt(u256, 0x75540825a6ecc5dc7d7c2f5f868164182742227f1367d66c43ee51ec7937a81),
        },
        .{
            Felt252.fromInt(u256, 0xf4e01b2032298f86b539e3d3ac05ced20d2ef275273f9325f8827717156529),
            Felt252.fromInt(u256, 0x587bc46f5f58e0511b93c31134652a689d761a9e7f234f0f130c52e4679f3a),
            Felt252.fromInt(u256, 0xbdb3180fdcfd6d6f172beb401af54dd71b6569e6061767234db2b777adf98b),
        },
    };

    for (test_data) |d| {
        var hasher: PoseidonHasher = .{};
        try expectEqual(d[2], hasher.hash(d[0], d[1]));
    }
}

test "PoseidonHasher: Poseidon hash a single element" {
    const test_data = [_]std.meta.Tuple(&.{ Felt252, Felt252 }){
        .{
            Felt252.fromInt(u256, 0x9dad5d6f502ccbcb6d34ede04f0337df3b98936aaf782f4cc07d147e3a4fd6),
            Felt252.fromInt(u256, 0x11222854783f17f1c580ff64671bc3868de034c236f956216e8ed4ab7533455),
        },
        .{
            Felt252.fromInt(u256, 0x3164a8e2181ff7b83391b4a86bc8967f145c38f10f35fc74e9359a0c78f7b6),
            Felt252.fromInt(u256, 0x79ad7aa7b98d47705446fa01865942119026ac748d67a5840f06948bce2306b),
        },
    };

    for (test_data) |d| {
        var hasher: PoseidonHasher = .{};
        try expectEqual(d[1], hasher.hashSingle(d[0]));
    }
}

test "PoseidonHasher: Poseidon hash many elements" {
    const test_data = [_]std.meta.Tuple(&.{ []const Felt252, Felt252 }){
        .{
            &[_]Felt252{
                Felt252.fromInt(u256, 0x9bf52404586087391c5fbb42538692e7ca2149bac13c145ae4230a51a6fc47),
                Felt252.fromInt(u256, 0x40304159ee9d2d611120fbd7c7fb8020cc8f7a599bfa108e0e085222b862c0),
                Felt252.fromInt(u256, 0x46286e4f3c450761d960d6a151a9c0988f9e16f8a48d4c0a85817c009f806a),
            },
            Felt252.fromInt(u256, 0x1ec38b38dc88bac7b0ed6ff6326f975a06a59ac601b417745fd412a5d38e4f7),
        },
        .{
            &[_]Felt252{
                Felt252.fromInt(u256, 0xbdace8883922662601b2fd197bb660b081fcf383ede60725bd080d4b5f2fd3),
                Felt252.fromInt(u256, 0x1eb1daaf3fdad326b959dec70ced23649cdf8786537cee0c5758a1a4229097),
                Felt252.fromInt(u256, 0x869ca04071b779d6f940cdf33e62d51521e19223ab148ef571856ff3a44ff1),
                Felt252.fromInt(u256, 0x533e6df8d7c4b634b1f27035c8676a7439c635e1fea356484de7f0de677930),
            },
            Felt252.fromInt(u256, 0x2520b8f910174c3e650725baacad4efafaae7623c69a0b5513d75e500f36624),
        },
    };

    for (test_data) |d| {
        var hasher: PoseidonHasher = .{};
        try expectEqual(d[1], hasher.hashMany(d[0]));

        hasher = .{};
        for (d[0]) |msg| {
            hasher.update(msg);
        }
        try expectEqual(d[1], hasher.finalize());
    }
}
