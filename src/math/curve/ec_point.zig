// code ported from starknet-curve:
// https://github.com/xJonathanLEI/starknet-rs/blob/0857bd6cd3bd34cbb06708f0a185757044171d8d/starknet-curve/src/ec_point.rs
const std = @import("std");

const Felt252 = @import("../fields/starknet.zig").Felt252;
const CurveParams = @import("./curve_params.zig");
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
    /// const point = AffinePoint.initUnchecked(x_value, y_value, false);
    /// ```
    ///
    /// This creates a new affine point with the x-coordinate `x_value`, the y-coordinate `y_value`,
    /// and sets the infinity flag to `false`.
    ///
    pub fn initUnchecked(x: Felt252, y: Felt252, infinity: bool) Self {
        return .{ .x = x, .y = y, .infinity = infinity };
    }

    /// Returns the identity element of the elliptic curve.
    ///
    /// This function returns the identity element of the elliptic curve, which is the zero point
    /// represented as the point at infinity (denoted as `O`). The identity element serves as the
    /// neutral element in elliptic curve arithmetic.
    ///
    /// # Returns
    ///
    /// The identity element of the elliptic curve, represented as the zero point with the infinity flag set to true.
    ///
    /// # Remarks
    ///
    /// The identity element (`O`) behaves as the additive identity in elliptic curve arithmetic. Adding
    /// it to any other point (`O + P`) yields the other point `P`, and adding it to itself (`O + O`)
    /// results in the identity element `O`.
    ///
    pub inline fn identity() Self {
        return .{};
    }

    /// Returns the generator point of the elliptic curve.
    ///
    /// This function retrieves and returns the pre-defined generator point G (base point). The generator point G is a constant point on the curve that, when multiplied by integers within a certain range, can generate any other point in its subgroup over the curve.
    ///
    /// # Returns
    ///
    /// The generator point G of the elliptic curve, which serves as the basis for generating all other points
    /// in its subgroup over the curve.
    pub inline fn generator() Self {
        return CurveParams.GENERATOR;
    }

    /// Determines whether the affine point lies on the elliptic curve.
    ///
    /// This function checks if the given affine point lies on the elliptic curve defined by the Short Weierstrass equation:
    /// y^2 = x^3 + a * x + b, where (x, y) are the coordinates of the affine point and a, b are curve parameters.
    ///
    /// # Arguments
    ///
    /// * `self` - A pointer to the affine point to be checked.
    ///
    /// # Returns
    ///
    /// Returns true if the point lies on the elliptic curve, false otherwise.
    ///
    /// # Remarks
    ///
    /// The function handles the case of the point at infinity, which is always considered to be on the curve.
    /// For finite points, it evaluates whether the equation y^2 = x^3 + ax + b holds true.
    /// If the point lies on the curve, it returns true; otherwise, it returns false.
    ///
    pub fn isOnCurve(self: *const Self) bool {
        // Check if the point is at infinity.
        if (self.infinity) return true;

        // Calculate the right-hand side of the elliptic curve equation: x^3 + ax + b.
        const rhs = self.x.square().mul(self.x).add(
            CurveParams.ALPHA.mul(self.x),
        ).add(CurveParams.BETA);

        // Check if the calculated right-hand side is equal to the square of the y-coordinate.
        return rhs.equal(self.y.square());
    }

    /// Computes the negation of the given affine point on the elliptic curve.
    ///
    /// This function calculates the negation of the given affine point on the elliptic curve, which is the point obtained by reflecting the original point across the x-axis.
    ///
    /// If the original point is at infinity, its negation remains the point at infinity.
    ///
    /// # Arguments
    ///
    /// * `self` - The affine point to be negated.
    ///
    /// # Returns
    ///
    /// The negation of the given affine point on the elliptic curve.
    ///
    /// # Remarks
    ///
    /// The negation operation is defined such that if the original point P has coordinates (x, y), its negation -P has coordinates (x, -y).
    /// The negation of the point at infinity remains the point at infinity, as it is the additive identity in elliptic curve arithmetic.
    pub fn neg(self: Self) Self {
        return .{
            .x = self.x,
            .y = self.y.neg(),
            .infinity = self.infinity,
        };
    }

    /// Adds another elliptic curve point to this point.
    ///
    /// Performs point addition between two elliptic curve points.
    ///
    /// # Arguments
    ///
    /// * `self` - The first elliptic curve point.
    /// * `other` - A pointer to the second elliptic curve point being added.
    ///
    /// # Returns
    ///
    /// The resulting elliptic curve point after the addition operation.
    ///
    /// # Errors
    ///
    /// Returns an error if any error occurs during the addition operation.
    pub fn add(self: Self, other: *const Self) !Self {
        // Make a copy of the original point
        var cp = self;
        // Perform point addition in place
        try Self.addAssign(&cp, other);
        // Return the resulting point
        return cp;
    }

    /// Subtracts another affine point from this point in the context of elliptic curve arithmetic.
    ///
    /// This function performs point subtraction between two affine points on an elliptic curve in Short Weierstrass form.
    /// It calculates the difference between the two points and returns the result as a new affine point.
    ///
    /// # Arguments
    ///
    /// * `self` - The affine point from which the other point is subtracted.
    /// * `other` - A pointer to the affine point being subtracted.
    ///
    /// # Returns
    ///
    /// The result of subtracting the other point from this point, represented as a new affine point.
    ///
    /// # Errors
    ///
    /// Returns an error if an error occurs during the calculation, such as division by zero.
    ///
    pub fn sub(self: Self, other: *const Self) !Self {
        var cp = self;
        try cp.addAssign(&other.neg());
        return cp;
    }

    /// Subtracts another affine point from this point in place in the context of elliptic curve arithmetic.
    ///
    /// This function performs point subtraction between two affine points on an elliptic curve in Short Weierstrass form.
    /// It modifies the original point by subtracting the other point from it.
    ///
    /// # Arguments
    ///
    /// * `self` - A mutable reference to the affine point from which the other point is subtracted.
    /// * `rhs` - A pointer to the affine point being subtracted.
    ///
    /// # Errors
    ///
    /// Returns an error if an error occurs during the calculation, such as division by zero.
    ///
    pub fn subAssign(self: *Self, rhs: *const Self) !void {
        try self.addAssign(&rhs.neg());
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
            .y = x.mul(x).mul(x).add(CurveParams.ALPHA.mul(x)).add(CurveParams.BETA).sqrt() orelse return EcPointError.SqrtNotExist,
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

test "AffinePoint: identity function should correspond to identity" {
    try expectEqual(
        AffinePoint{ .x = Felt252.zero(), .y = Felt252.zero(), .infinity = true },
        AffinePoint.identity(),
    );
}

test "AffinePoint: generator function should return the generator of the curve" {
    try expectEqual(
        AffinePoint{
            .x = .{
                .fe = [4]u64{
                    14484022957141291997,
                    5884444832209845738,
                    299981207024966779,
                    232005955912912577,
                },
            },
            .y = .{
                .fe = [4]u64{
                    6241159653446987914,
                    664812301889158119,
                    18147424675297964973,
                    405578048423154473,
                },
            },
            .infinity = false,
        },
        AffinePoint.generator(),
    );
}

test "AffinePoint: isOnCurve should return true if the point is on the curve" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expect(a.isOnCurve());

    const b: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464),
        .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
        .infinity = false,
    };

    try expect(b.isOnCurve());
}

test "AffinePoint: isOnCurve should return false if the point is not on the curve" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 10),
        .y = Felt252.fromInt(u256, 100),
        .infinity = false,
    };

    try expect(!a.isOnCurve());

    const b: AffinePoint = .{
        .x = Felt252.fromInt(u256, 5),
        .y = Felt252.fromInt(u256, 30),
        .infinity = false,
    };

    try expect(!b.isOnCurve());
}

test "AffinePoint: isOnCurve should return true if the point is at infinity" {
    try expect(AffinePoint.identity().isOnCurve());
}

test "AffinePoint: neg identity should return identity" {
    try expectEqual(
        AffinePoint{ .x = Felt252.zero(), .y = Felt252.zero(), .infinity = true },
        AffinePoint.identity().neg(),
    );
}

test "AffinePoint: neg a random point should return (x, -y)" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 3119986168776131983280236261251576523431128963685919687543048209950440350219),
            .infinity = false,
        },
        a.neg(),
    );
}

test "AffinePoint: init should init an affine point with the provided coordinates" {
    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u8, 10),
            .y = Felt252.fromInt(u8, 5),
            .infinity = false,
        },
        AffinePoint.initUnchecked(
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
        AffinePoint.initUnchecked(
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

test "AffinePoint: add P + 0 should give P" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        },
        try a.add(&.{}),
    );
}

test "AffinePoint: add 0 + P should give P" {
    var a: AffinePoint = .{};

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        },
        try a.add(&.{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        }),
    );
}

test "AffinePoint: add P + (-P) should give 0" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.zero(),
            .y = Felt252.zero(),
            .infinity = true,
        },
        try a.add(&.{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262).neg(),
            .infinity = false,
        }),
    );
}

test "AffinePoint: add P + P should give 2P" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 1007300233009797052089600572030536234678420387464749955693412487829103372971),
            .y = Felt252.fromInt(u256, 1628094014246951319213922206675864072767692386561452886899658728389307097247),
            .infinity = false,
        },
        try a.add(&.{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        }),
    );
}

test "AffinePoint: add should give the proper point addition" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 1732660995762076585664239316986550513074833679175460014337184483203739567080),
            .y = Felt252.fromInt(u256, 2212051391075121985157657306991376790084194366385999148123095336409007912683),
            .infinity = false,
        },
        try a.add(&.{
            .x = Felt252.fromInt(u256, 874739451),
            .y = Felt252.fromInt(u256, 78981980789517450823121602653688575320503877484645249556098070515590001476),
            .infinity = false,
        }),
    );
}

test "AffinePoint: sub P - P should give 0" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.zero(),
            .y = Felt252.zero(),
            .infinity = true,
        },
        try a.sub(&a),
    );
}

test "AffinePoint: sub P - 0 should give P" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(a, try a.sub(&.{}));
}

test "AffinePoint: sub 0 - P should give -P" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(a.neg(), try AffinePoint.identity().sub(&a));
}

test "AffinePoint: sub P1 - P2 should give P1 + (-P2)" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 3170839098387265895893008062780951484244114197556826317838387523115006188371),
            .y = Felt252.fromInt(u256, 816850407800303493850322799005343907936137841827655002556778477319881342108),
            .infinity = false,
        },
        try a.sub(&.{
            .x = Felt252.fromInt(u256, 874739451078007766457464),
            .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
            .infinity = false,
        }),
    );
}

test "AffinePoint: subAssign P - P should give 0" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try a.subAssign(&a);

    try expectEqual(
        AffinePoint{
            .x = Felt252.zero(),
            .y = Felt252.zero(),
            .infinity = true,
        },
        a,
    );
}

test "AffinePoint: subAssign P - 0 should give P" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try a.subAssign(&.{});

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        },
        a,
    );
}

test "AffinePoint: subAssign 0 - P should give -P" {
    var a = AffinePoint.identity();

    try a.subAssign(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    try expectEqual(
        AffinePoint.initUnchecked(
            Felt252.fromInt(u256, 874739451078007766457464989),
            Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            false,
        ).neg(),
        a,
    );
}

test "AffinePoint: subAssign P1 - P2 should give P1 + (-P2)" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try a.subAssign(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464),
        .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
        .infinity = false,
    });

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 3170839098387265895893008062780951484244114197556826317838387523115006188371),
            .y = Felt252.fromInt(u256, 816850407800303493850322799005343907936137841827655002556778477319881342108),
            .infinity = false,
        },
        a,
    );
}
