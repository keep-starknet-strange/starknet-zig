// code ported from starknet-curve:
// https://github.com/xJonathanLEI/starknet-rs/blob/0857bd6cd3bd34cbb06708f0a185757044171d8d/starknet-curve/src/ec_point.rs
const std = @import("std");

const Felt252 = @import("../../fields/starknet.zig").Felt252;
const CurveParams = @import("../curve_params.zig");
const EcPointError = @import("../errors.zig").EcPointError;
const AffinePoint = @import("./affine.zig").AffinePoint;
const TEST_ITERATIONS = @import("../../../main.zig").TEST_ITERATIONS;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

/// Represents a point in standard projective coordinates over a given field.
///
/// Standard projective points extend the concept of affine points by introducing an additional coordinate
/// (z-coordinate) to accommodate "points at infinity".
///
/// In standard projective coordinates, a point on the elliptic curve is represented as (X, Y, Z), where Z ≠ 0.
///
/// The actual point is (X/Z, Y/Z).
///
/// This structure encapsulates the x, y, and z coordinates of a point in projective space.
pub const ProjectivePoint = struct {
    const Self = @This();

    /// The x-coordinate of the projective point.
    x: Felt252 = Felt252.zero(),
    /// The y-coordinate of the projective point.
    y: Felt252 = Felt252.one(),
    /// The z-coordinate of the projective point.
    z: Felt252 = Felt252.zero(),

    /// Constructs a projective point from an affine point.
    ///
    /// This function converts an affine point to a projective point, setting its coordinates
    /// accordingly and preserving the infinity flag.
    ///
    /// # Arguments
    ///
    /// * `p` - A pointer to the affine point.
    ///
    /// # Returns
    ///
    /// A projective point constructed from the given affine point.
    pub fn fromAffinePoint(p: *const AffinePoint) Self {
        return if (p.isIdentity())
            .{}
        else
            .{ .x = p.x, .y = p.y, .z = Felt252.one() };
    }

    /// Returns the identity element of the projective space.
    ///
    /// This function returns the identity element of the projective space, which is the zero point
    /// represented as the point at infinity. The identity element serves as the neutral element
    /// in projective space arithmetic.
    ///
    /// # Returns
    ///
    /// The identity element of the projective space, represented as the point at infinity.
    pub inline fn identity() Self {
        return .{};
    }

    /// Checks if the projective point is the identity element.
    ///
    /// This function returns true if the provided projective point is the identity element of the
    /// projective space, which is represented as the point at infinity. Otherwise, it returns false.
    ///
    /// # Returns
    ///
    /// `true` if the projective point is the identity element (point at infinity), otherwise `false`.
    ///
    pub inline fn isIdentity(self: *const Self) bool {
        return self.z.isZero();
    }

    pub fn doubleAssign(self: *Self) void {
        if (self.isIdentity()) return;

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

    /// Adds another projective point to this point and returns the result.
    ///
    /// This function adds the coordinates of the provided projective point (`rhs`) to the coordinates
    /// of this projective point (`self`), without modifying the original point. It returns a new
    /// projective point representing the result of the addition operation.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the projective point to be added to this point.
    ///
    /// # Returns
    ///
    /// A new projective point representing the result of the addition operation.
    ///
    /// # Safety
    ///
    /// This function assumes that both `self` and `rhs` are valid projective points. Passing invalid
    /// points may result in undefined behavior.
    ///
    /// # Note
    ///
    /// The addition operation is performed according to the formulas derived for standard projective
    /// coordinates. For more information, see the source reference.
    pub fn add(self: Self, rhs: *const Self) Self {
        // Make a copy of the original point
        var a = self;
        // Perform point addition in place
        Self.addAssign(&a, rhs);
        // Return the resulting point
        return a;
    }

    /// Returns the negation of this projective point.
    ///
    /// This function returns the negation of the current projective point, where the negation is
    /// defined as the point with the same x and z coordinates but the negated y coordinate.
    ///
    /// # Returns
    ///
    /// The negation of this projective point.
    pub fn neg(self: Self) Self {
        return .{
            .x = self.x,
            .y = self.y.neg(),
            .z = self.z,
        };
    }

    /// Subtracts another projective point from this point and returns the result.
    ///
    /// This function subtracts the coordinates of the provided projective point (`rhs`) from the
    /// coordinates of this projective point (`self`), without modifying the original point. It returns
    /// a new projective point representing the result of the subtraction operation.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the projective point to be subtracted from this point.
    ///
    /// # Returns
    ///
    /// A new projective point representing the result of the subtraction operation.
    ///
    /// # Safety
    ///
    /// This function assumes that both `self` and `rhs` are valid projective points. Passing invalid
    /// points may result in undefined behavior.
    pub fn sub(self: Self, rhs: *const Self) Self {
        // Make a copy of the original point
        var a = self;
        // Add the negation of the rhs point to this point
        a.addAssign(&rhs.neg());
        // Return the resulting point
        return a;
    }

    /// Adds another projective point to this point in projective space.
    ///
    /// This function adds the coordinates of the provided projective point (`rhs`) to the coordinates
    /// of this projective point (`self`), updating the coordinates of `self` with the result.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the projective point to be added to this point.
    ///
    /// # Safety
    ///
    /// This function assumes that both `self` and `rhs` are valid projective points. Passing invalid
    /// points may result in undefined behavior.
    ///
    /// # Note
    ///
    /// The addition operation is performed according to the formulas derived for standard projective
    /// coordinates. For more information, see the source reference.
    pub fn addAssign(self: *Self, rhs: *const Self) void {
        // If the point to be added is the identity point, no operation is needed.
        if (rhs.isIdentity()) return;

        // If this point is the identity point, update it to the provided point and return.
        if (self.isIdentity()) {
            self.* = rhs.*;
            return;
        }

        // x0 * z1
        const u_0 = self.x.mul(rhs.z);
        // x1 * z0
        const u_1 = rhs.x.mul(self.z);

        // slope = (y0 * z1 - y1 * z0) / (x0 * z1 - x1 * z0)
        // Null denominator the slope
        if (u_0.eql(u_1)) {
            if (self.y.eql(rhs.y.neg())) {
                // Set this point to the identity (point at infinity).
                self.* = .{};
            } else {
                // Perform point doubling operation.
                self.doubleAssign();
            }
            return;
        }

        // y0 * z1
        const t0 = self.y.mul(rhs.z);
        // y1 * z0
        const t1 = rhs.y.mul(self.z);
        // t0 - t1
        const t = t0.sub(t1);

        // u0 - u1
        const u = u_0.sub(u_1);
        // u * u
        const u_2 = u.square();
        // u * u * u
        const u_3 = u.mul(u_2);

        // z0 * z1
        const v = self.z.mul(rhs.z);

        // t * t * v - u2 * (u0 + u1);
        const w = t.square().mul(v).sub(u_2.mul(u_0.add(u_1)));

        // Update the coordinates of this point with the result of the addition operation.
        self.* = .{
            .x = u.mul(w),
            .y = t.mul(u_0.mul(u_2).sub(w)).sub(t0.mul(u_3)),
            .z = u_3.mul(v),
        };
    }

    pub fn addAssignAffinePoint(self: *Self, rhs: AffinePoint) void {
        if (rhs.infinity) return;

        if (self.infinity) {
            self.* = .{
                .x = rhs.x,
                .y = rhs.y,
                .z = Felt252.one(),
            };
            return;
        }

        const u_0 = self.x;
        const u_1 = rhs.x.mul(self.z);
        const t0 = self.y;
        const t1 = rhs.y.mul(self.z);

        if (u_0.eql(u_1)) {
            if (t0.eql(t1)) {
                self.doubleAssign();
            } else {
                self.infinity = true;
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
        };
    }
};

test "ProjectivePoint: fromAffinePoint should return a projective point based on an affine point" {
    try expectEqual(
        ProjectivePoint{},
        ProjectivePoint.fromAffinePoint(&.{}),
    );

    try expectEqual(
        ProjectivePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .z = Felt252.one(),
        },
        ProjectivePoint.fromAffinePoint(&.{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        }),
    );
}

test "ProjectivePoint: identity should return the point at infinity" {
    try expectEqual(
        ProjectivePoint{},
        ProjectivePoint.identity(),
    );
}

test "ProjectivePoint: addAssign of P + 0 should return P" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464),
        .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
        .infinity = false,
    };

    var p = ProjectivePoint.fromAffinePoint(&a);

    p.addAssign(&.{});

    try expectEqual(
        ProjectivePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464),
            .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
            .z = Felt252.one(),
        },
        p,
    );
}

test "ProjectivePoint: addAssign of 0 + P should return P" {
    var p: ProjectivePoint = .{};

    p.addAssign(&ProjectivePoint.fromAffinePoint(
        &.{
            .x = Felt252.fromInt(u256, 874739451078007766457464),
            .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
            .infinity = false,
        },
    ));

    try expectEqual(
        ProjectivePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464),
            .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
            .z = Felt252.one(),
        },
        p,
    );
}

test "ProjectivePoint: addAssign P + (-P) should give 0" {
    var p = ProjectivePoint.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    p.addAssign(&ProjectivePoint.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262).neg(),
        .infinity = false,
    }));

    try expectEqual(ProjectivePoint{}, p);
}

test "ProjectivePoint: addAssign P + P should give 2P" {
    var p = ProjectivePoint.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    p.addAssign(&ProjectivePoint.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    }));

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 1007300233009797052089600572030536234678420387464749955693412487829103372971),
            .y = Felt252.fromInt(u256, 1628094014246951319213922206675864072767692386561452886899658728389307097247),
            .infinity = false,
        },
        AffinePoint.fromProjectivePoint(&p),
    );
}

test "ProjectivePoint: addAssign should give the proper point addition" {
    var p = ProjectivePoint.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    p.addAssign(&ProjectivePoint.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451),
        .y = Felt252.fromInt(u256, 78981980789517450823121602653688575320503877484645249556098070515590001476),
        .infinity = false,
    }));

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 1732660995762076585664239316986550513074833679175460014337184483203739567080),
            .y = Felt252.fromInt(u256, 2212051391075121985157657306991376790084194366385999148123095336409007912683),
            .infinity = false,
        },
        AffinePoint.fromProjectivePoint(&p),
    );
}

test "ProjectivePoint: fuzzing testing of arithmetic operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate a random affine point 'a'.
        var a: AffinePoint = .{
            .x = Felt252.fromInt(u256, random.int(u256)),
            .y = Felt252.fromInt(u256, random.int(u256)),
            .infinity = false,
        };

        // Generate another random affine point 'b'.
        const b: AffinePoint = .{
            .x = Felt252.fromInt(u256, random.int(u256)),
            .y = Felt252.fromInt(u256, random.int(u256)),
            .infinity = false,
        };

        // Convert affine points 'a' and 'b' to projective points.
        const a_projective = ProjectivePoint.fromAffinePoint(&a);
        const b_projective = ProjectivePoint.fromAffinePoint(&b);

        // Make a copy of point 'a' to perform in-place addition later.
        var p = ProjectivePoint.fromAffinePoint(&a);

        // Verify the correctness of subtraction operation between affine points 'a' and 'b'.
        try expectEqual(
            a.sub(&b),
            AffinePoint.fromProjectivePoint(&a_projective.sub(&b_projective)),
        );

        // Verify the correctness of subtraction operation between 'a_projective' and identity point.
        try expectEqual(
            a_projective,
            a_projective.sub(&ProjectivePoint.identity()),
        );

        // Verify the correctness of negation operation on 'a_projective'.
        try expectEqual(
            a_projective.neg(),
            ProjectivePoint.identity().sub(&a_projective),
        );

        // Perform in-place addition of 'b' to 'a'.
        try a.addAssign(&b);

        // Verify the correctness of addition operation between affine points 'a' and 'b'.
        try expectEqual(
            a,
            AffinePoint.fromProjectivePoint(
                &p.add(&b_projective),
            ),
        );

        // Perform in-place addition of 'b_projective' to 'p'.
        p.addAssign(&b_projective);

        // Verify the correctness of 'p' after in-place addition.
        try expectEqual(a, AffinePoint.fromProjectivePoint(&p));
    }
}
