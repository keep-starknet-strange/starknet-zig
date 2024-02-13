// Core imports.
const std = @import("std");
const builtin = @import("builtin");

// Local imports.
const customlogFn = @import("utils/log.zig").logFn;
const Felt252 = @import("math/fields/starknet.zig").Felt252;

// *****************************************************************************
// *                     GLOBAL CONFIGURATION                                  *
// *****************************************************************************

/// Standard library options.
pub const std_options = struct {
    /// Define the global log level.
    /// TODO: Make this configurable.
    pub const log_level = .debug;
    /// Define the log scope levels for each library.
    /// TODO: Make this configurable.
    pub const log_scope_levels = &[_]std.log.ScopeLevel{};
    // Define logFn to override the std implementation
    pub const logFn = customlogFn;
};

pub fn main() !void {
    std.log.debug("starknet-zig\n", .{});
    std.debug.print(
        \\Let's add two field elements together.
        \\We will use the Starknet prime field 0x800000000000011000000000000000000000000000000000000000000000001.
        \\We will add 0x800000000000011000000000000000000000000000000000000000000000000 and 0x4.
        \\The result should be 3.
    , .{});
    const a = Felt252.fromInt(u256, 0x800000000000011000000000000000000000000000000000000000000000000);
    const b = Felt252.fromInt(u256, 0x4);
    const c = a.add(b);
    std.debug.print("\nResult: {}\n", .{c.toInteger()});
}

// *****************************************************************************
// *                     VM TESTS                                              *
// *****************************************************************************

// *****************************************************************************
// *                     MATH TESTS                                            *
// *****************************************************************************

test "fields" {
    _ = @import("math/fields/fields.zig");
    _ = @import("math/fields/starknet.zig");
    _ = @import("math/fields/elliptic_curve.zig");
}

test "curve" {
    _ = @import("math/curve/ec_point.zig");
    _ = @import("math/curve/curve_params.zig");
}

// *****************************************************************************
// *                     UTIL TESTS                                            *
// *****************************************************************************

test "util" {
    _ = @import("utils/log.zig");
    _ = @import("utils/time.zig");
}
