// code ported from starknet-curve:
// https://github.com/xJonathanLEI/starknet-rs/blob/0857bd6cd3bd34cbb06708f0a185757044171d8d/starknet-curve/src/ec_point.rs
const std = @import("std");

const Felt252 = @import("../fields/starknet.zig").Felt252;
const ALPHA = @import("./curve_params.zig").ALPHA;
const BETA = @import("./curve_params.zig").BETA;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

pub const EcPointError = error{
    SqrtNotExist,
};

pub const ProjectivePoint = struct {
    const Self = @This();

    x: Felt252 = Felt252.zero(),
    y: Felt252 = Felt252.zero(),
    z: Felt252 = Felt252.one(),
    infinity: bool = false,

    pub fn fromAffinePoint(p: AffinePoint) Self {
        return .{ .x = p.x, .y = p.y };
    }

    fn identity() Self {
        return .{ .infinity = true };
    }

    pub fn doubleAssign(self: *Self) void {
        if (self.infinity) {
            return;
        }

        // t=3x^2+az^2 with a=1 from stark curve
        const t = Felt252.three().mul(self.x).mul(self.x).add(self.z.mul(self.z));
        const u = Felt252.two().mul(self.y).mul(self.z);
        const v = Felt252.two().mul(u).mul(self.x).mul(self.y);
        const w = t.mul(t).sub(Felt252.two().mul(v));

        const uy = u.mul(self.y);

        self.* = .{
            .x = u.mul(w),
            .y = t.mul(v.sub(w)).sub(Felt252.two().mul(uy).mul(uy)),
            .z = u.mul(u).mul(u),
            .infinity = self.infinity,
        };
    }

    pub fn mulByBits(self: Self, rhs: [@bitSizeOf(u256)]bool) Self {
        var product = ProjectivePoint.identity();

        inline for (1..@bitSizeOf(u256) + 1) |idx| {
            product.doubleAssign();
            if (rhs[@bitSizeOf(u256) - idx]) {
                product.addAssign(self);
            }
        }
        return product;
    }

    fn addAssign(self: *Self, rhs: ProjectivePoint) void {
        if (rhs.infinity) {
            return;
        }

        if (self.infinity) {
            self.* = rhs;
            return;
        }

        const u_0 = self.x.mul(rhs.z);
        const u_1 = rhs.x.mul(self.z);
        if (u_0.equal(u_1)) {
            self.doubleAssign();
            return;
        }

        const t0 = self.y.mul(rhs.z);
        const t1 = rhs.y.mul(self.z);
        const t = t0.sub(t1);

        const u = u_0.sub(u_1);
        const u_2 = u.mul(u);

        const v = self.z.mul(rhs.z);

        // t * t * v - u2 * (u0 + u1);
        const w = t.mul(t.mul(v)).sub(u_2.mul(u_0.add(u_1)));
        const u_3 = u.mul(u_2);

        self.* = .{
            .x = u.mul(w),
            .y = t.mul(u_0.mul(u_2).sub(w)).sub(t0.mul(u_3)),
            .z = u_3.mul(v),
            .infinity = self.infinity,
        };
    }

    pub fn addAssignAffinePoint(self: *Self, rhs: AffinePoint) void {
        if (rhs.infinity) {
            return;
        }

        if (self.infinity) {
            self.* = .{
                .x = rhs.x,
                .y = rhs.y,
                .z = Felt252.one(),
                .infinity = rhs.infinity,
            };
            return;
        }

        const u_0 = self.x;
        const u_1 = rhs.x.mul(self.z);
        const t0 = self.y;
        const t1 = rhs.y.mul(self.z);

        if (u_0.equal(u_1)) {
            if (!t0.equal(t1)) {
                self.infinity = true;
            } else {
                self.doubleAssign();
            }
            return;
        }

        const t = t0.sub(t1);
        const u = u_0.sub(u_1);
        const u_2 = u.mul(u);

        const v = self.z;
        const w = t.mul(t).mul(v).sub(u_2.mul(u_0.add(u_1)));
        const u_3 = u.mul(u_2);

        const x = u.mul(w);
        const y = t.mul(u_0.mul(u_2).sub(w)).sub(t0.mul(u_3));
        const z = u_3.mul(v);

        self.* = .{
            .x = x,
            .y = y,
            .z = z,
            .infinity = self.infinity,
        };
    }
};

/// This module defines a struct representing an affine point on an elliptic curve in the Short Weierstrass form.
///
/// Affine points are pairs of field elements (x, y) that satisfy the Short Weierstrass cubic equation
/// y^2 = x^3 + a * x + b, where a and b are constants defining the elliptic curve.
/// Additionally, there is a distinguished symbol 'O', representing the point at infinity.
///
/// The struct `AffinePoint` encapsulates an x-coordinate, a y-coordinate, and a boolean flag indicating
/// whether the point is at infinity.
pub const AffinePoint = struct {
    const Self = @This();

    /// The x-coordinate of the affine point.
    x: Felt252 = Felt252.zero(),
    /// The y-coordinate of the affine point.
    y: Felt252 = Felt252.zero(),
    /// A boolean flag indicating whether the point is at infinity.
    infinity: bool = true,

    /// Initializes a new affine point with the given coordinates.
    ///
    /// This function creates a new affine point with the specified x-coordinate, y-coordinate,
    /// and infinity flag, and returns it.
    ///
    /// # Arguments
    ///
    /// * `x` - The x-coordinate of the affine point.
    /// * `y` - The y-coordinate of the affine point.
    /// * `infinity` - A boolean flag indicating whether the point is at infinity.
    ///
    /// # Returns
    ///
    /// A new affine point initialized with the provided coordinates.
    ///
    /// # Example
    ///
    /// ```zig
    /// const point = AffinePoint.init(x_value, y_value, false);
    /// ```
    ///
    /// This creates a new affine point with the x-coordinate `x_value`, the y-coordinate `y_value`,
    /// and sets the infinity flag to `false`.
    ///
    pub fn init(x: Felt252, y: Felt252, infinity: bool) Self {
        return .{ .x = x, .y = y, .infinity = infinity };
    }

    pub fn add(self: Self, other: Self) Self {
        var cp = self;
        var cp_other = other;

        Self.addAssign(&cp, &cp_other);
        return cp;
    }

    pub fn sub(self: Self, other: Self) Self {
        var cp = self;
        cp.subAssign(other);
        return cp;
    }

    pub fn subAssign(self: *Self, rhs: Self) void {
        var rhs_copy = rhs;

        rhs_copy.y = rhs_copy.y.neg();
        self.addAssign(&rhs_copy);
    }

    /// Adds another affine point to this point in the context of elliptic curve arithmetic.
    ///
    /// This function performs point addition between two affine points on an elliptic curve in Short Weierstrass form.
    ///
    /// # Arguments
    ///
    /// * `self` - A mutable reference to the affine point on which addition is performed.
    /// * `rhs` - A pointer to the affine point being added.
    ///
    /// # Errors
    ///
    /// Returns an error if division by zero occurs during the calculation of the slope.
    pub fn addAssign(self: *Self, rhs: *const AffinePoint) !void {
        // P + 0 = P
        // If the other point is the point at infinity, no operation is needed.
        if (rhs.infinity) return;

        // 0 + P = P
        // If this point is the point at infinity, the result is set to the other point.
        if (self.infinity) {
            self.* = rhs.*;
            return;
        }

        // If both points have the same x-coordinate.
        if (self.x.equal(rhs.x)) {
            // P + (-P) = I
            // If the y-coordinates are negations of each other, resulting in point at infinity.
            if (self.y.equal(rhs.y.neg())) {
                // Set this point to the point at infinity.
                self.* = .{};
            } else {
                // Otherwise, the points are the same, perform point doubling.
                self.doubleAssign();
            }
            return;
        }

        // Calculate the slope of the line passing through the two points.
        // l = (y2-y1)/(x2-x1)
        const lambda = try rhs.y.sub(self.y).div(rhs.x.sub(self.x));

        // Compute x-coordinate of the resulting point: lambda^2 - x1 - x2
        const result_x = lambda.square().sub(self.x).sub(rhs.x);

        // Compute y-coordinate of the resulting point: lambda * (x1 - x3) - y1
        self.y = lambda.mul(self.x.sub(result_x)).sub(self.y);

        // Update the x-coordinate of this point to the computed x-coordinate of the resulting point.
        self.x = result_x;
    }

    /// Performs point doubling on the given affine point in the context of elliptic curve arithmetic.
    ///
    /// This function doubles the given affine point on an elliptic curve in Short Weierstrass form. It calculates the new coordinates of the point after doubling based on the curve equation and the tangent line at the given point.
    ///
    /// # Arguments
    ///
    /// * `self` - A mutable reference to the affine point that will be doubled.
    pub fn doubleAssign(self: *Self) void {
        // If the point is the point at infinity, no operation is needed.
        if (self.infinity) return;

        // l = (3x^2+a)/2y with a=1 from stark curve
        const lambda = Felt252.three().mul(
            self.x.mul(self.x),
        ).add(
            Felt252.one(),
        ).mul(
            Felt252.two().mul(self.y).inv().?,
        );

        // Compute the new x-coordinate of the point after doubling: lambda^2 - 2x
        const result_x = lambda.mul(lambda).sub(self.x).sub(self.x);

        // Compute the new y-coordinate of the point after doubling: lambda * (x - result_x) - y
        self.y = lambda.mul(self.x.sub(result_x)).sub(self.y);

        // Update the coordinates of the point with the new values
        self.x = result_x;
    }

    /// Constructs an elliptic curve point from the x-coordinate in the context of the STARK curve.
    ///
    /// This function constructs an elliptic curve point from the given x-coordinate on the STARK curve,
    /// satisfying the equation 𝑦^2 ≡ 𝑥^3 + 𝛼⋅𝑥 + 𝛽 (mod 𝑝).
    ///
    /// # Arguments
    ///
    /// * `x` - The x-coordinate of the point.
    ///
    /// # Errors
    ///
    /// Returns an error if the square root of the y-coordinate does not exist.
    ///
    /// # Remarks
    ///
    /// The point construction follows the equation of the STARK curve:
    ///
    /// * The x-coordinate is set to the provided value.
    /// * The y-coordinate is calculated as the square root of 𝑥^3 + 𝛼⋅𝑥 + 𝛽 (mod 𝑝).
    /// * If the square root of the y-coordinate does not exist, an error is returned.
    /// * The point is not set to the point at infinity.
    ///
    /// This code snippet constructs an elliptic curve point on the STARK curve from the given x-coordinate.
    pub fn fromX(x: Felt252) EcPointError!Self {
        return .{
            .x = x,
            .y = x.mul(x).mul(x).add(ALPHA.mul(x)).add(BETA).sqrt() orelse return EcPointError.SqrtNotExist,
            .infinity = false,
        };
    }

    pub fn fromProjectivePoint(p: ProjectivePoint) Self {
        // always one, that is why we can unwrap, unreachable will not happen
        const zinv = if (p.z.inv()) |zinv| zinv else unreachable;

        return .{
            .x = p.x.mul(zinv),
            .y = p.y.mul(zinv),
            .infinity = false,
        };
    }
};

test "AffinePoint: default value should correspond to identity" {
    try expectEqual(
        AffinePoint{ .x = Felt252.zero(), .y = Felt252.zero(), .infinity = true },
        AffinePoint{},
    );
}

test "AffinePoint: init should init an affine point with the provided coordinates" {
    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u8, 10),
            .y = Felt252.fromInt(u8, 5),
            .infinity = false,
        },
        AffinePoint.init(
            Felt252.fromInt(u8, 10),
            Felt252.fromInt(u8, 5),
            false,
        ),
    );

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u8, 10),
            .y = Felt252.fromInt(u8, 5),
            .infinity = true,
        },
        AffinePoint.init(
            Felt252.fromInt(u8, 10),
            Felt252.fromInt(u8, 5),
            true,
        ),
    );
}

test "AffinePoint: addAssign P + 0 should give P" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try a.addAssign(&.{});

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        },
        a,
    );
}

test "AffinePoint: addAssign 0 + P should give P" {
    var a: AffinePoint = .{};

    try a.addAssign(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        },
        a,
    );
}

test "AffinePoint: addAssign P + (-P) should give 0" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try a.addAssign(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262).neg(),
        .infinity = false,
    });

    try expectEqual(
        AffinePoint{
            .x = Felt252.zero(),
            .y = Felt252.zero(),
            .infinity = true,
        },
        a,
    );
}

test "AffinePoint: addAssign P + P should give 2P" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try a.addAssign(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 1007300233009797052089600572030536234678420387464749955693412487829103372971),
            .y = Felt252.fromInt(u256, 1628094014246951319213922206675864072767692386561452886899658728389307097247),
            .infinity = false,
        },
        a,
    );
}

test "AffinePoint: addAssign should give the proper point addition" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try a.addAssign(&.{
        .x = Felt252.fromInt(u256, 874739451),
        .y = Felt252.fromInt(u256, 78981980789517450823121602653688575320503877484645249556098070515590001476),
        .infinity = false,
    });

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 1732660995762076585664239316986550513074833679175460014337184483203739567080),
            .y = Felt252.fromInt(u256, 2212051391075121985157657306991376790084194366385999148123095336409007912683),
            .infinity = false,
        },
        a,
    );
}

test "AffinePoint: doubleAssign should return the result of 2P" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464987),
        .y = Felt252.fromInt(u256, 1706810360461260382053322601986439128304438960645702960907418619089749412278),
        .infinity = false,
    };
    a.doubleAssign();

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 2351468578589314139010270743686619948996212672240729424672235643020198087569),
            .y = Felt252.fromInt(u256, 305861574354557676187499619608507066121174188916494330928491058389223641058),
            .infinity = false,
        },
        a,
    );
}

test "AffinePoint: doubleAssign 2*0 should return 0" {
    var a: AffinePoint = .{};

    a.doubleAssign();

    try expectEqual(
        AffinePoint{
            .x = Felt252.zero(),
            .y = Felt252.zero(),
            .infinity = true,
        },
        a,
    );
}

test "AffinePoint: fromX should return an affine point based on the provided x-coordinate" {
    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464987),
            .y = Felt252.fromInt(u256, 1706810360461260382053322601986439128304438960645702960907418619089749412278),
            .infinity = false,
        },
        try AffinePoint.fromX(Felt252.fromInt(u256, 874739451078007766457464987)),
    );
}

test "AffinePoint: fromX should return an affine point based on the provided " {
    try expectError(
        EcPointError.SqrtNotExist,
        AffinePoint.fromX(Felt252.fromInt(u256, 87473945107800776645746498)),
    );
}
