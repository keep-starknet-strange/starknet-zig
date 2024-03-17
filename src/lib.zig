pub const curve = struct {
    pub usingnamespace @import("math/curve/short_weierstrass/affine.zig");
    pub usingnamespace @import("math/curve/short_weierstrass/projective.zig");
    pub usingnamespace @import("math/curve/short_weierstrass/projective_jacobian.zig");
    pub usingnamespace @import("math/curve/curve_params.zig");
};

pub const fields = struct {
    pub usingnamespace @import("math/fields/fields.zig");
    pub usingnamespace @import("math/fields/starknet.zig");
    pub usingnamespace @import("math/fields/arithmetic.zig");
    pub usingnamespace @import("math/fields/biginteger.zig");
    pub usingnamespace @import("math/fields/const_choice.zig");
};

pub const bench = struct {
    pub usingnamespace @import("bench/bench.zig");
    pub usingnamespace @import("bench/bench_field.zig");
};

pub const crypto = struct {
    pub usingnamespace @import("crypto/ecdsa.zig");
    pub usingnamespace @import("crypto/pedersen_hash.zig");
    pub usingnamespace @import("crypto/poseidon_hash.zig");
};

pub const core = struct {
    pub usingnamespace @import("core/eth_address.zig");
};
