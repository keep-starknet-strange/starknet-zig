// code ported from starknet-curve:
// https://github.com/xJonathanLEI/starknet-rs/blob/0857bd6cd3bd34cbb06708f0a185757044171d8d/starknet-curve/src/ec_point.rs
const std = @import("std");

const Felt252 = @import("../../fields/starknet.zig").Felt252;
const bigInt = @import("../../fields/biginteger.zig").bigInt;
const CurveParams = @import("../curve_params.zig");
const EcPointError = @import("../errors.zig").EcPointError;
const ProjectivePoint = @import("./projective.zig").ProjectivePoint;
const ProjectivePointJacobian = @import("./projective_jacobian.zig").ProjectivePointJacobian;
const TEST_ITERATIONS = @import("../../../main.zig").TEST_ITERATIONS;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

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

    /// Initializes a new affine point with the given coordinates.
    ///
    /// This function creates a new affine point with the specified x-coordinate, y-coordinate,
    /// and infinity flag, and returns it. Additionally, it ensures that the generated point lies
    /// on the elliptic curve.
    ///
    /// # Arguments
    ///
    /// * `x` - The x-coordinate of the affine point.
    /// * `y` - The y-coordinate of the affine point.
    /// * `infinity` - A boolean flag indicating whether the point is at infinity.
    ///
    /// # Returns
    ///
    /// If the provided coordinates result in a point on the elliptic curve, it returns the newly
    /// initialized affine point. Otherwise, it returns an error indicating that the point is not
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
    /// const point = try AffinePoint.init(x_value, y_value, false);
    /// ```
    ///
    /// This creates a new affine point with the x-coordinate `x_value`, the y-coordinate `y_value`,
    /// and sets the infinity flag to `false`. If the resulting point is not on the curve, it returns
    /// an error.
    ///
    pub fn init(x: Felt252, y: Felt252, infinity: bool) EcPointError!Self {
        // Create the affine point using the provided coordinates.
        const point: Self = .{
            .x = x,
            .y = y,
            .infinity = infinity,
        };

        // Check if the point lies on the elliptic curve.
        if (!point.isOnCurve()) return EcPointError.PointNotOnCurve;

        // Return the initialized affine point.
        return point;
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
    /// it to any rhs point (`O + P`) yields the rhs point `P`, and adding it to itself (`O + O`)
    /// results in the identity element `O`.
    ///
    pub inline fn identity() Self {
        return .{};
    }

    /// Returns the generator point of the elliptic curve.
    ///
    /// This function retrieves and returns the pre-defined generator point G (base point). The generator point G is a constant point on the curve that, when multiplied by integers within a certain range, can generate any rhs point in its subgroup over the curve.
    ///
    /// # Returns
    ///
    /// The generator point G of the elliptic curve, which serves as the basis for generating all rhs points
    /// in its subgroup over the curve.
    pub inline fn generator() Self {
        return CurveParams.GENERATOR;
    }

    /// Checks if the affine point is the identity element.
    ///
    /// This function returns true if the provided affine point is the identity element of the
    /// elliptic curve, which is represented as the point at infinity (`O`). Otherwise, it returns false.
    ///
    /// # Returns
    ///
    /// `true` if the affine point is the identity element (`O`), otherwise `false`.
    ///
    pub inline fn isIdentity(self: *const Self) bool {
        return self.infinity;
    }

    /// Checks whether two affine points are equal.
    ///
    /// This function determines whether two affine points are equal by comparing their coordinates.
    /// Two affine points are considered equal if their x-coordinates and y-coordinates are equal.
    ///
    /// # Arguments
    ///
    /// * `self` - The first affine point.
    /// * `rhs` - The second affine point to compare.
    ///
    /// # Returns
    ///
    /// Returns true if the two affine points are equal, false otherwise.
    ///
    /// # Remarks
    ///
    /// Two affine points (x₁, y₁) and (x₂, y₂) are considered equal if and only if:
    ///
    /// * x₁ = x₂
    /// * y₁ = y₂
    ///
    pub fn eql(self: Self, rhs: Self) bool {
        // Check if either point is the point at infinity.
        if (self.isIdentity()) return rhs.isIdentity();
        if (rhs.isIdentity()) return false;

        // Check if the x-coordinates, y-coordinates are equal.
        return self.x.eql(rhs.x) and self.y.eql(rhs.y);
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
        const rhs = self.x.square().mul(&self.x).add(
            CurveParams.ALPHA.mul(&self.x),
        ).add(CurveParams.BETA);

        // Check if the calculated right-hand side is equal to the square of the y-coordinate.
        return rhs.eql(self.y.square());
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
    /// * `rhs` - A pointer to the second elliptic curve point being added.
    ///
    /// # Returns
    ///
    /// The resulting elliptic curve point after the addition operation.
    ///
    /// # Errors
    ///
    /// Returns an error if any error occurs during the addition operation.
    pub fn add(self: Self, rhs: *const Self) !Self {
        // Make a copy of the original point
        var a = self;
        // Perform point addition in place
        try a.addAssign(rhs);
        // Return the resulting point
        return a;
    }

    /// Subtracts another affine point from this point in the context of elliptic curve arithmetic.
    ///
    /// This function performs point subtraction between two affine points on an elliptic curve in Short Weierstrass form.
    /// It calculates the difference between the two points and returns the result as a new affine point.
    ///
    /// # Arguments
    ///
    /// * `self` - The affine point from which the rhs point is subtracted.
    /// * `rhs` - A pointer to the affine point being subtracted.
    ///
    /// # Returns
    ///
    /// The result of subtracting the rhs point from this point, represented as a new affine point.
    ///
    /// # Errors
    ///
    /// Returns an error if an error occurs during the calculation, such as division by zero.
    ///
    pub fn sub(self: Self, rhs: *const Self) !Self {
        var a = self;
        try a.addAssign(&rhs.neg());
        return a;
    }

    /// Subtracts another affine point from this point in place in the context of elliptic curve arithmetic.
    ///
    /// This function performs point subtraction between two affine points on an elliptic curve in Short Weierstrass form.
    /// It modifies the original point by subtracting the rhs point from it.
    ///
    /// # Arguments
    ///
    /// * `self` - A mutable reference to the affine point from which the rhs point is subtracted.
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
        // If the rhs point is the point at infinity, no operation is needed.
        if (rhs.infinity) return;

        // 0 + P = P
        // If this point is the point at infinity, the result is set to the rhs point.
        if (self.infinity) {
            self.* = rhs.*;
            return;
        }

        // If both points have the same x-coordinate.
        if (self.x.eql(rhs.x)) {
            // P + (-P) = I
            // If the y-coordinates are negations of each rhs, resulting in point at infinity.
            if (self.y.eql(rhs.y.neg())) {
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
        self.y = lambda.mul(&self.x.sub(result_x)).sub(self.y);

        // Update the x-coordinate of this point to the computed x-coordinate of the resulting point.
        self.x = result_x;
    }

    /// Doubles the given affine point on the elliptic curve.
    ///
    /// This function calculates the doubling of the given affine point on the elliptic curve,
    /// which involves finding the point that lies on the curve and is collinear with the tangent
    /// line at the original point, and then reflecting it across the x-axis.
    ///
    /// If the original point is at infinity, its doubling remains the point at infinity.
    ///
    /// # Arguments
    ///
    /// * `self` - The affine point to be doubled.
    ///
    /// # Returns
    ///
    /// The result of doubling the given affine point on the elliptic curve.
    pub fn double(self: Self) Self {
        var a = self;
        a.doubleAssign();
        return a;
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
            &self.x.mul(&self.x),
        ).add(
            Felt252.one(),
        ).mul(
            &Felt252.two().mul(&self.y).inverse().?,
        );

        // Compute the new x-coordinate of the point after doubling: lambda^2 - 2x
        const result_x = lambda.mul(&lambda).sub(self.x).sub(self.x);

        // Compute the new y-coordinate of the point after doubling: lambda * (x - result_x) - y
        self.y = lambda.mul(&self.x.sub(result_x)).sub(self.y);

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
            .y = x.mul(&x).mul(&x).add(CurveParams.ALPHA.mul(&x)).add(CurveParams.BETA).sqrt() orelse
                return EcPointError.SqrtNotExist,
            .infinity = false,
        };
    }

    /// Generates a random affine point on the elliptic curve.
    ///
    /// This function generates a random affine point on the elliptic curve defined by the Short Weierstrass equation: 𝑦^2 = 𝑥^3 + 𝛼⋅𝑥 + 𝛽, where (𝑥, 𝑦) are the coordinates of the affine point and 𝛼, 𝛽 are curve parameters.
    ///
    /// # Arguments
    ///
    /// * `r` - An instance of the random number generator used to generate the x-coordinate of the point.
    ///
    /// # Returns
    ///
    /// A random affine point on the elliptic curve.
    ///
    /// # Remarks
    ///
    /// This function repeatedly generates random x-coordinates until it constructs a valid point on the elliptic curve.
    /// The resulting point is returned as an affine point with the x-coordinate generated randomly and the y-coordinate computed based on the curve equation.
    pub fn rand(r: std.Random) Self {
        // Continuously generate random x-coordinates until a valid point on the curve is constructed.
        while (true) {
            // Generate a random x-coordinate within the field.
            const random_x = Felt252.fromInt(u256, r.int(u256));
            // Attempt to construct a point on the curve using the generated x-coordinate.
            if (Self.fromX(random_x) catch null) |p| return p;
        }
    }

    /// Converts a projective point to an affine point on the elliptic curve.
    ///
    /// This function converts a projective point representation to an affine point representation on the elliptic curve.
    /// Projective coordinates are used to represent points on elliptic curves efficiently.
    ///
    /// # Arguments
    ///
    /// * `p` - A pointer to the projective point to be converted.
    ///
    /// # Returns
    ///
    /// An affine point on the elliptic curve derived from the provided projective point.
    ///
    /// # Errors
    ///
    /// Returns an error if the inverse of the `z` coordinate of the projective point cannot be computed, such as when `z` is zero.
    pub fn fromProjectivePoint(p: *const ProjectivePoint) Self {
        // Point at infinity
        if (p.isIdentity()) return .{};

        // Compute the inverse of the `z` coordinate of the projective point.
        // Note: `zinv` is always one, which is why we can unwrap the result.
        const zinv = p.z.inverse().?;

        // Create and return the resulting affine point.
        return .{
            .x = p.x.mul(&zinv),
            .y = p.y.mul(&zinv),
            .infinity = false,
        };
    }

    /// Converts a projective point in Jacobian coordinates to an affine point on the elliptic curve.
    ///
    /// This function converts a projective point representation in Jacobian coordinates to an affine point representation on the elliptic curve.
    /// Jacobian coordinates are an optimized representation for elliptic curve operations, offering improved efficiency compared to affine coordinates.
    ///
    /// # Arguments
    ///
    /// * `p` - A pointer to the projective point in Jacobian coordinates to be converted.
    ///
    /// # Returns
    ///
    /// An affine point on the elliptic curve derived from the provided projective point in Jacobian coordinates.
    ///
    /// # Remarks
    ///
    /// The `z` coordinate of the projective point is always assumed to be non-zero in Jacobian coordinates, ensuring that it has a valid inverse in the field.
    pub fn fromProjectivePointJacobian(p: *const ProjectivePointJacobian) Self {
        // Point at infinity
        if (p.isIdentity()) return .{};

        // Compute the inverse of the `z` coordinate of the projective point.
        // Note: `z` is always non zero, so that it must have an inverse in the field.
        const zinv = p.z.inverse().?;
        const zinv_squared = zinv.square();

        // Create and return the resulting affine point.
        return .{
            .x = p.x.mul(&zinv_squared),
            .y = p.y.mul(&zinv_squared).mul(&zinv),
            .infinity = false,
        };
    }

    /// Multiplies the affine point by a scalar represented as a bit slice in big-endian format.
    ///
    /// This function performs scalar multiplication of the affine point by a scalar represented
    /// as a bit slice in big-endian format.
    ///
    /// # Arguments
    ///
    /// * `bits` - A bit slice representing the scalar value in big-endian format.
    ///
    /// # Returns
    ///
    /// The resulting affine point after scalar multiplication.
    ///
    /// # Errors
    ///
    /// Returns an error if any error occurs during the multiplication operation.
    pub fn mulByBitsBe(self: *const Self, bits: [@bitSizeOf(u256)]bool) !Self {
        var product = AffinePoint.identity();

        // Find the index of the first one bit in the bit slice.
        const first_one = std.mem.indexOfScalar(bool, &bits, true) orelse @bitSizeOf(u256);

        // Iterate over the bits in the scalar value.
        for (bits[first_one..]) |bit| {
            // Double the current product.
            product.doubleAssign();
            // If the current bit is one, add the original affine point to the product.
            if (bit) try product.addAssign(self);
        }

        return product;
    }

    /// Multiplies the affine point by a scalar represented as a field element.
    ///
    /// This function performs scalar multiplication of the affine point by a scalar represented
    /// as a field element.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the scalar value.
    ///
    /// # Returns
    ///
    /// The resulting affine point after scalar multiplication.
    ///
    /// # Errors
    ///
    /// Returns an error if any error occurs during the multiplication operation.
    pub fn mulByScalar(self: *const Self, rhs: *const Felt252) !Self {
        // Convert the scalar value to a bit slice in big-endian format and perform scalar multiplication.
        return try self.mulByBitsBe(rhs.toBitsBe());
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
                .fe = bigInt(4).init(
                    .{
                        14484022957141291997,
                        5884444832209845738,
                        299981207024966779,
                        232005955912912577,
                    },
                ),
            },
            .y = .{
                .fe = bigInt(4).init(
                    .{
                        6241159653446987914,
                        664812301889158119,
                        18147424675297964973,
                        405578048423154473,
                    },
                ),
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

test "AffinePoint: initUnchecked should initialize an affine point with the provided coordinates" {
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

test "AffinePoint: init should return an error is the provided point is not on the curve" {
    try expectError(
        EcPointError.PointNotOnCurve,
        AffinePoint.init(
            Felt252.fromInt(u8, 10),
            Felt252.fromInt(u8, 5),
            false,
        ),
    );
}

test "AffinePoint: init should initialize a point if point is on the curve" {
    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        },
        try AffinePoint.init(
            Felt252.fromInt(u256, 874739451078007766457464989),
            Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            false,
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

test "AffinePoint: double should return the result of 2P" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464987),
        .y = Felt252.fromInt(u256, 1706810360461260382053322601986439128304438960645702960907418619089749412278),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 2351468578589314139010270743686619948996212672240729424672235643020198087569),
            .y = Felt252.fromInt(u256, 305861574354557676187499619608507066121174188916494330928491058389223641058),
            .infinity = false,
        },
        a.double(),
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

test "AffinePoint: add should give the proper point addition (P + Q)" {
    var a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    };

    const b: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451),
        .y = Felt252.fromInt(u256, 78981980789517450823121602653688575320503877484645249556098070515590001476),
        .infinity = false,
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 1732660995762076585664239316986550513074833679175460014337184483203739567080),
            .y = Felt252.fromInt(u256, 2212051391075121985157657306991376790084194366385999148123095336409007912683),
            .infinity = false,
        },
        try a.add(&b),
    );

    // Commutativity
    try expectEqual(try b.add(&a), try a.add(&b));
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

test "AffinePoint: fromProjectivePoint should give an AffinePoint from a ProjectivePoint" {
    const a: ProjectivePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .z = Felt252.one(),
    };

    try expectEqual(
        AffinePoint{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        },
        AffinePoint.fromProjectivePoint(&a),
    );
}

test "AffinePoint: fuzzing testing of arithmetic addition operations" {
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

        const zero = AffinePoint.identity();

        // Associativity
        try expect((try (try a.add(&b)).add(&c)).eql(try (try a.add(&b)).add(&c)));

        // Identify
        try expect(a.eql(try zero.add(&a)));
        try expect(b.eql(try zero.add(&b)));
        try expect(c.eql(try zero.add(&c)));
        try expect(a.eql(try a.add(&zero)));
        try expect(b.eql(try b.add(&zero)));
        try expect(c.eql(try c.add(&zero)));

        // Negation
        try expect(zero.eql(try a.neg().add(&a)));
        try expect(zero.eql(try b.neg().add(&b)));
        try expect(zero.eql(try c.neg().add(&c)));
        try expect(zero.eql(zero.neg()));

        // Commutativity
        try expect((try a.add(&b)).eql(try b.add(&a)));
        try expect((try a.add(&c)).eql(try c.add(&a)));
        try expect((try b.add(&c)).eql(try c.add(&b)));

        // Associativity and commutativity simultaneously
        try expect((try (try a.add(&b)).add(&c)).eql(try (try a.add(&c)).add(&b)));
        try expect((try (try a.add(&c)).add(&b)).eql(try (try b.add(&c)).add(&a)));

        // Doubling
        try expect((try a.add(&a)).eql(a.double()));
        try expect((try b.add(&b)).eql(b.double()));
        try expect((try c.add(&c)).eql(c.double()));
        try expect(zero.eql(zero.double()));
        try expect(zero.eql(zero.neg().double()));
    }
}

test "AffinePoint: fuzzing testing of arithmetic multiplication operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate a random affine point 'a'.
        var a = AffinePoint.rand(random);

        // Convert affine points to projective points.
        var b = Felt252.rand(random);
        var c = Felt252.rand(random);
        var zero = Felt252.zero();
        var one = Felt252.one();

        // Identity
        try expect((try a.mulByBitsBe(zero.toBitsBe())).eql(.{}));
        try expect((try a.mulByBitsBe(one.toBitsBe())).eql(a));
        try expect((try a.mulByScalar(&zero)).eql(.{}));
        try expect((try a.mulByScalar(&one)).eql(a));

        // Commutativity
        try expect((try (try a.mulByScalar(&b)).mulByScalar(&c)).eql(
            try (try a.mulByScalar(&c)).mulByScalar(&b),
        ));

        // Inverses
        try expect((try a.mulByScalar(&b.inverse().?.mul(&b))).eql(
            a,
        ));
    }
}
