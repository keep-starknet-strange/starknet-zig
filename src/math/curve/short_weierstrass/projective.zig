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

    /// Initializes a new projective point with the given coordinates without performing curve validation.
    ///
    /// This function creates a new projective point with the specified x, y, and z coordinates without
    /// performing any validation checks. It is the responsibility of the caller to ensure that the provided
    /// coordinates represent a valid point on the elliptic curve.
    ///
    /// # Arguments
    ///
    /// * `x` - The x-coordinate of the projective point.
    /// * `y` - The y-coordinate of the projective point.
    /// * `z` - The z-coordinate of the projective point.
    ///
    /// # Returns
    ///
    /// A new projective point initialized with the provided coordinates.
    ///
    /// # Example
    ///
    /// ```zig
    /// const point = ProjectivePoint.initUnchecked(x_value, y_value, z_value);
    /// ```
    ///
    /// This creates a new projective point with the x-coordinate `x_value`, the y-coordinate `y_value`,
    /// and the z-coordinate `z_value` without performing any validation checks.
    ///
    pub fn initUnchecked(x: Felt252, y: Felt252, z: Felt252) Self {
        return .{ .x = x, .y = y, .z = z };
    }

    /// Initializes a new projective point with the given coordinates after performing curve validation.
    ///
    /// This function creates a new projective point with the specified x, y, and z coordinates and
    /// performs validation to ensure that the resulting point lies on the elliptic curve defined by
    /// the curve parameters. If the provided coordinates do not correspond to a point on the curve,
    /// it returns an error indicating that the point is not on the curve.
    ///
    /// # Arguments
    ///
    /// * `x` - The x-coordinate of the projective point.
    /// * `y` - The y-coordinate of the projective point.
    /// * `z` - The z-coordinate of the projective point.
    ///
    /// # Returns
    ///
    /// If the provided coordinates result in a point on the elliptic curve, it returns the newly
    /// initialized projective point. Otherwise, it returns an error indicating that the point is not
    /// on the curve.
    ///
    /// # Errors
    ///
    /// Returns an error of type `EcPointError` if the provided coordinates do not correspond to
    /// a point on the elliptic curve.
    ///
    /// # Example
    ///
    /// ```zig
    /// const point = try ProjectivePoint.init(x_value, y_value, z_value);
    /// ```
    ///
    /// This creates a new projective point with the x-coordinate `x_value`, the y-coordinate `y_value`,
    /// and the z-coordinate `z_value`. If the resulting point is not on the curve, it returns an error.
    ///
    pub fn init(x: Felt252, y: Felt252, z: Felt252) !Self {
        const p: Self = .{ .x = x, .y = y, .z = z };
        if (!AffinePoint.fromProjectivePoint(&p).isOnCurve())
            return EcPointError.PointNotOnCurve;
        return p;
    }

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

    /// Checks if this projective point is equal to another projective point.
    ///
    /// This function checks whether this projective point is equal to the provided projective point.
    /// Two projective points are considered equal if their corresponding affine representations
    /// are equal. If either point is the point at infinity, they are considered equal if and only if
    /// both are points at infinity.
    ///
    /// # Arguments
    ///
    /// * `rhs` - The other projective point to compare against.
    ///
    /// # Returns
    ///
    /// `true` if this projective point is equal to the provided projective point, otherwise `false`.
    ///
    /// # Example
    ///
    /// ```zig
    /// const point1 = ProjectivePoint.initUnchecked(x1, y1, z1);
    /// const point2 = ProjectivePoint.initUnchecked(x2, y2, z2);
    /// const result = point1.eql(point2);
    /// ```
    ///
    /// This example checks if `point1` is equal to `point2` and stores the result in the `result` variable.
    ///
    pub fn eql(self: Self, rhs: Self) bool {
        // Check if either point is the point at infinity.
        if (self.isIdentity()) return rhs.isIdentity();
        if (rhs.isIdentity()) return false;

        // Check if the x-coordinates, y-coordinates are equal.
        return self.x.mul(&rhs.z).eql(rhs.x.mul(&self.z)) and
            self.y.mul(&rhs.z).eql(rhs.y.mul(&self.z));
    }

    /// Checks if this projective point lies on the elliptic curve.
    ///
    /// This function determines whether the given projective point lies on the elliptic curve defined
    /// by the curve parameters. If the point is at infinity, it is considered to be on the curve.
    ///
    /// # Returns
    ///
    /// `true` if the projective point lies on the elliptic curve, otherwise `false`.
    pub fn isOnCurve(self: *const Self) bool {
        // Check if the point is at infinity.
        if (self.isIdentity()) return true;

        // Convert the projective point to an affine point and check if it lies on the curve.
        return AffinePoint.fromProjectivePoint(self).isOnCurve();
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

    /// Doubles the projective point.
    ///
    /// This function returns a new projective point that represents the result of
    /// doubling the given projective point, effectively performing point doubling
    /// in elliptic curve arithmetic.
    ///
    /// # Returns
    ///
    /// The resulting projective point after the doubling operation.
    ///
    /// # Remarks
    ///
    /// This function does not modify the original projective point, but instead
    /// returns a new point representing the result of the doubling operation.
    ///
    pub fn double(self: Self) Self {
        var a = self;
        a.doubleAssign();
        return a;
    }

    /// Doubles the projective point in place.
    ///
    /// This function doubles the given projective point in place, effectively performing
    /// point doubling in elliptic curve arithmetic.
    ///
    /// # Remarks
    ///
    /// The point doubling operation doubles the given point in projective coordinates
    /// and stores the result back in the original point.
    ///
    /// # Errors
    ///
    /// Returns without performing any operation if the projective point is the identity element
    /// (point at infinity).
    ///
    pub fn doubleAssign(self: *Self) void {
        // If the point is the point at infinity, no operation is needed.
        if (self.isIdentity()) return;

        // Calculate t = 3*x^2 + a*z^2 with a = 1 (from stark curve).
        const t = Felt252.three().mul(&self.x.square()).add(self.z.mul(&self.z));

        // Calculate u = 2*y*z.
        const u = self.y.double().mul(&self.z);

        // Calculate v = 2*u*x*y.
        const v = u.double().mul(&self.x).mul(&self.y);

        // Calculate w = t^2 - 2*v.
        const w = t.mul(&t).sub(v.double());

        // Calculate uy = u*y.
        const uy = u.mul(&self.y);

        // Update the projective point with the new coordinates after doubling.
        self.* = .{
            .x = u.mul(&w),
            .y = t.mul(&v.sub(w)).sub(uy.square().double()),
            .z = u.square().mul(&u),
        };
    }

    /// Multiplies the projective point by a scalar represented as a bit slice in big-endian format.
    ///
    /// This function performs scalar multiplication of the projective point by a scalar represented
    /// as a bit slice in big-endian format. The scalar multiplication is computed using the double-and-add
    /// algorithm, where each bit of the scalar is processed sequentially, doubling the projective point
    /// at each step and conditionally adding the original point if the corresponding bit is set.
    ///
    /// # Arguments
    ///
    /// * `bits` - A bit slice representing the scalar value in big-endian format.
    ///
    /// # Returns
    ///
    /// The resulting projective point after scalar multiplication.
    ///
    /// # Remarks
    ///
    /// This function does not modify the original projective point, but instead returns a new point
    /// representing the result of the scalar multiplication operation.
    pub fn mulByBitsBe(self: *const Self, bits: [@bitSizeOf(u256)]u1) Self {
        // Initialize the product as the identity element.
        var product = ProjectivePoint.identity();

        // Find the index of the first set bit in the scalar.
        const first_one = std.mem.indexOfScalar(u1, &bits, 1) orelse @bitSizeOf(u256);

        // Iterate over the scalar bits starting from the first set bit.
        for (bits[first_one..]) |bit| {
            // Double the projective point.
            product.doubleAssign();

            // Conditionally add the original point if the corresponding bit is set.
            if (bit == 1) product.addAssign(self);
        }

        // Return the resulting product after scalar multiplication.
        return product;
    }

    /// Multiplies the projective point by a scalar.
    ///
    /// This function multiplies the projective point by a scalar value represented as a Felt252.
    /// It internally converts the scalar into a bit slice in big-endian format and performs the scalar
    /// multiplication using the `mulByBitsBe` method.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the scalar value represented as a Felt252.
    ///
    /// # Returns
    ///
    /// The resulting projective point after scalar multiplication.
    pub fn mulByScalar(self: *const Self, rhs: *const Felt252) Self {
        return self.mulByBitsBe(rhs.toBitsBe());
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
        a.addAssign(rhs);
        // Return the resulting point
        return a;
    }

    /// Adds another affine point to this point in projective space.
    ///
    /// This function adds the coordinates of the provided affine point (`rhs`) to the coordinates
    /// of this projective point (`self`), without modifying the original point. It returns a new
    /// projective point representing the result of the addition operation.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the affine point to be added to this point.
    ///
    /// # Returns
    ///
    /// A new projective point representing the result of the addition operation.
    ///
    /// # Safety
    ///
    /// This function assumes that `self` is a valid projective point and `rhs` is a valid affine point.
    /// Passing invalid points may result in undefined behavior.
    ///
    /// # Note
    ///
    /// The addition operation is performed according to the formulas derived for standard projective
    /// coordinates. For more information, see the source reference.
    pub fn addAffine(self: Self, rhs: *const AffinePoint) Self {
        // Make a copy of the original point
        var a = self;
        // Perform point addition in place
        a.addAffineAssign(rhs);
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
        return if (self.isIdentity())
            .{}
        else
            .{ .x = self.x, .y = self.y.neg(), .z = self.z };
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

    /// Subtracts another affine point from this point in projective space.
    ///
    /// This function subtracts the coordinates of the provided affine point (`rhs`) from the coordinates
    /// of this projective point (`self`), updating the coordinates of `self` with the result.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the affine point to be subtracted from this point.
    ///
    /// # Safety
    ///
    /// This function assumes that `self` is a valid projective point and `rhs` is a valid affine point.
    /// Passing invalid points may result in undefined behavior.
    ///
    /// # Note
    ///
    /// The subtraction operation is performed according to the formulas derived for standard projective
    /// coordinates. For more information, see the source reference.
    pub fn subAffine(self: Self, rhs: *const AffinePoint) Self {
        // Make a copy of the original point
        var a = self;
        // Add the negation of the rhs point to this point
        a.addAffineAssign(&rhs.neg());
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
        const u_0 = self.x.mul(&rhs.z);
        // x1 * z0
        const u_1 = rhs.x.mul(&self.z);

        // slope = (y0 * z1 - y1 * z0) / (x0 * z1 - x1 * z0)
        // Null denominator the slope
        if (u_0.eql(u_1)) {
            if (self.y.mul(&rhs.z).eql(rhs.y.mul(&self.z))) {
                // Perform point doubling operation.
                self.doubleAssign();
            } else {
                // Set this point to the identity (point at infinity).
                self.* = .{};
            }
            return;
        }

        // y0 * z1
        const t0 = self.y.mul(&rhs.z);
        // y1 * z0
        const t1 = rhs.y.mul(&self.z);
        // t0 - t1
        const t = t0.sub(t1);

        // u0 - u1
        const u = u_0.sub(u_1);
        // u * u
        const u_2 = u.square();
        // u * u * u
        const u_3 = u.mul(&u_2);

        // z0 * z1
        const v = self.z.mul(&rhs.z);

        // t * t * v - u2 * (u0 + u1);
        const w = t.square().mul(&v).sub(u_2.mul(&u_0.add(u_1)));

        // Update the coordinates of this point with the result of the addition operation.
        self.* = .{
            .x = u.mul(&w),
            .y = t.mul(&u_0.mul(&u_2).sub(w)).sub(t0.mul(&u_3)),
            .z = u_3.mul(&v),
        };
    }

    /// Adds another affine point to this point in projective space.
    ///
    /// This function adds the coordinates of the provided affine point (`rhs`) to the coordinates
    /// of this projective point (`self`), updating the coordinates of `self` with the result.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the affine point to be added to this point.
    ///
    /// # Safety
    ///
    /// This function assumes that `self` is a valid projective point and `rhs` is a valid affine point.
    /// Passing invalid points may result in undefined behavior.
    ///
    /// # Note
    ///
    /// The addition operation is performed according to the formulas derived for standard projective
    /// coordinates.
    pub fn addAffineAssign(self: *Self, rhs: *const AffinePoint) void {
        // If rhs is the identity point, no operation is needed.
        if (rhs.isIdentity()) return;

        // If self is the identity point, update self to rhs and return.
        if (self.isIdentity()) {
            self.* = Self.fromAffinePoint(rhs);
            return;
        }

        const u_0 = self.x;
        const u_1 = rhs.x.mul(&self.z);
        const t0 = self.y;
        const t1 = rhs.y.mul(&self.z);

        if (u_0.eql(u_1)) {
            if (t0.eql(t1)) {
                // Point doubling operation
                self.doubleAssign();
            } else {
                // Point at infinity
                self.* = Self.identity();
            }
            return;
        }

        const t = t0.sub(t1);
        const u = u_0.sub(u_1);
        const u_2 = u.mul(&u);

        const v = self.z;
        const w = t.mul(&t).mul(&v).sub(u_2.mul(&u_0.add(u_1)));
        const u_3 = u.mul(&u_2);

        self.* = .{
            .x = u.mul(&w),
            .y = t.mul(&u_0.mul(&u_2).sub(w)).sub(t0.mul(&u_3)),
            .z = u_3.mul(&v),
        };
    }
};

test "ProjectivePoint: initUnchecked should return a projective point (even if not valid)" {
    try expectEqual(
        ProjectivePoint{
            .x = Felt252.fromInt(u256, 10),
            .y = Felt252.fromInt(u256, 20),
            .z = Felt252.one(),
        },
        ProjectivePoint.initUnchecked(
            Felt252.fromInt(u256, 10),
            Felt252.fromInt(u256, 20),
            Felt252.one(),
        ),
    );

    try expectEqual(
        ProjectivePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .z = Felt252.one(),
        },
        ProjectivePoint.initUnchecked(
            Felt252.fromInt(u256, 874739451078007766457464989),
            Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            Felt252.one(),
        ),
    );
}

test "ProjectivePoint: init should return a projective point and throw an error when not valid" {
    try expectError(
        EcPointError.PointNotOnCurve,
        ProjectivePoint.init(
            Felt252.fromInt(u256, 10),
            Felt252.fromInt(u256, 20),
            Felt252.one(),
        ),
    );

    try expectEqual(
        ProjectivePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .z = Felt252.one(),
        },
        try ProjectivePoint.init(
            Felt252.fromInt(u256, 874739451078007766457464989),
            Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            Felt252.one(),
        ),
    );
}

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

test "ProjectivePoint: isOnCurve should return true if the point is on the curve" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    try expect(ProjectivePoint.fromAffinePoint(&a).isOnCurve());

    const b: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464),
        .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
        .infinity = false,
    };

    try expect(ProjectivePoint.fromAffinePoint(&b).isOnCurve());
}

test "ProjectivePoint: isOnCurve should return false if the point is not on the curve" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 10),
        .y = Felt252.fromInt(u256, 100),
        .infinity = false,
    };

    try expect(!ProjectivePoint.fromAffinePoint(&a).isOnCurve());

    const b: AffinePoint = .{
        .x = Felt252.fromInt(u256, 5),
        .y = Felt252.fromInt(u256, 30),
        .infinity = false,
    };

    try expect(!ProjectivePoint.fromAffinePoint(&b).isOnCurve());
}

test "ProjectivePoint: fuzzing testing of arithmetic addition operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate a random affine point 'a'.
        var a = AffinePoint.rand(random);

        // Generate another random affine point 'b'.
        var b = AffinePoint.rand(random);

        // Generate another random affine point 'c'.
        var c = AffinePoint.rand(random);

        // Convert affine points to projective points.
        var a_projective = ProjectivePoint.fromAffinePoint(&a);
        var b_projective = ProjectivePoint.fromAffinePoint(&b);
        var c_projective = ProjectivePoint.fromAffinePoint(&c);
        var zero: ProjectivePoint = .{};

        // Associativity
        try expect(
            a_projective.add(&b_projective).add(&c_projective).eql(
                a_projective.add(&b_projective.add(&c_projective)),
            ),
        );

        // Identify
        try expect(a_projective.eql(zero.add(&a_projective)));
        try expect(b_projective.eql(zero.add(&b_projective)));
        try expect(c_projective.eql(zero.add(&c_projective)));
        try expect(a_projective.eql(a_projective.add(&zero)));
        try expect(b_projective.eql(b_projective.add(&zero)));
        try expect(c_projective.eql(c_projective.add(&zero)));

        // Negation
        try expect(zero.eql(a_projective.neg().add(&a_projective)));
        try expect(zero.eql(b_projective.neg().add(&b_projective)));
        try expect(zero.eql(c_projective.neg().add(&c_projective)));
        try expect(zero.eql(zero.neg()));

        // Commutativity
        try expect(AffinePoint.fromProjectivePoint(&a_projective.add(&b_projective)).eql(
            AffinePoint.fromProjectivePoint(&b_projective.add(&a_projective)),
        ));

        // Associativity and commutativity simultaneously
        try expect(a_projective.add(&b_projective).add(&c_projective).eql(
            a_projective.add(&c_projective).add(&b_projective),
        ));
        try expect(a_projective.add(&c_projective).add(&b_projective).eql(
            b_projective.add(&c_projective).add(&a_projective),
        ));

        // Doubling
        try expect(a_projective.add(&a_projective).eql(a_projective.double()));
        try expect(b_projective.add(&b_projective).eql(b_projective.double()));
        try expect(c_projective.add(&c_projective).eql(c_projective.double()));
        try expect(zero.eql(zero.double()));
        try expect(zero.eql(zero.neg().double()));

        // Operation with an affine point
        try expect(a_projective.addAffine(&b).eql(
            a_projective.add(&b_projective),
        ));
        try expect(b_projective.addAffine(&c).eql(
            b_projective.add(&c_projective),
        ));
        try expect(a_projective.subAffine(&b).eql(
            a_projective.sub(&b_projective),
        ));
        try expect(b_projective.subAffine(&c).eql(
            b_projective.sub(&c_projective),
        ));
        try expect(zero.addAffine(&a).eql(
            a_projective,
        ));
        try expect(a_projective.addAffine(&b).addAffine(&c).eql(
            a_projective.add(&c_projective).add(&b_projective),
        ));
        try expect(a_projective.addAffine(&c).addAffine(&b).eql(
            b_projective.add(&c_projective).add(&a_projective),
        ));
    }
}

test "ProjectivePoint: fuzzing testing of arithmetic subtraction operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate a random affine point 'a'.
        var a = AffinePoint.rand(random);

        // Generate another random affine point 'b'.
        var b = AffinePoint.rand(random);

        // Convert affine points to projective points.
        var a_projective = ProjectivePoint.fromAffinePoint(&a);
        var b_projective = ProjectivePoint.fromAffinePoint(&b);
        var zero: ProjectivePoint = .{};

        // Anti-commutativity
        try expect(a_projective.sub(&b_projective).add(
            &b_projective.sub(&a_projective),
        ).isIdentity());
        try expect(a_projective.subAffine(&b).add(
            &b_projective.subAffine(&a),
        ).isIdentity());
        try expect(a_projective.subAffine(&b).addAffine(
            &try b.sub(&a),
        ).isIdentity());

        // Identity
        try expect(zero.sub(&a_projective).eql(a_projective.neg()));
        try expect(zero.sub(&b_projective).eql(b_projective.neg()));

        try expect(a_projective.sub(&zero).eql(a_projective));
        try expect(b_projective.sub(&zero).eql(b_projective));
    }
}

test "ProjectivePoint: fuzzing testing of arithmetic multiplication operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate a random affine point 'a'.
        var a = AffinePoint.rand(random);

        // Convert affine points to projective points.
        var a_projective = ProjectivePoint.fromAffinePoint(&a);
        var b = Felt252.rand(random);
        var c = Felt252.rand(random);
        var zero = Felt252.zero();
        var one = Felt252.one();

        // Identity
        try expect(a_projective.mulByBitsBe(zero.toBitsBe()).eql(.{}));
        try expect(a_projective.mulByBitsBe(one.toBitsBe()).eql(a_projective));
        try expect(a_projective.mulByScalar(&zero).eql(.{}));
        try expect(a_projective.mulByScalar(&one).eql(a_projective));

        // Commutativity
        try expect(a_projective.mulByScalar(&b).mulByScalar(&c).eql(
            a_projective.mulByScalar(&c).mulByScalar(&b),
        ));

        // Inverses
        try expect(a_projective.mulByScalar(&b.inv().?.mul(&b)).eql(
            a_projective,
        ));
    }
}
