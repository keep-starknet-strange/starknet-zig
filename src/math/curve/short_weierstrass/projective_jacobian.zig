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

/// Represents a point in projective space using Jacobian coordinates.
///
/// Jacobian coordinates optimize operations in elliptic curve cryptography.
/// They add a z-coordinate for representing points in projective space.
/// In Jacobian coordinates, a point is represented as (X, Y, Z), where Z ≠ 0.
/// The actual point is (X/Z^2, Y/Z^3).
///
/// This struct holds x, y, and z coordinates along with an infinity flag.
pub const ProjectivePointJacobian = struct {
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
    /// const point = ProjectivePointJacobian.initUnchecked(x_value, y_value, z_value);
    /// ```
    ///
    /// This creates a new projective point with the x-coordinate `x_value`, the y-coordinate `y_value`,
    /// and the z-coordinate `z_value` without performing any validation checks.
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
    /// const point = try ProjectivePointJacobian.init(x_value, y_value, z_value);
    /// ```
    ///
    /// This creates a new projective point with the x-coordinate `x_value`, the y-coordinate `y_value`,
    /// and the z-coordinate `z_value`. If the resulting point is not on the curve, it returns an error.
    pub fn init(x: Felt252, y: Felt252, z: Felt252) !Self {
        const p: Self = .{ .x = x, .y = y, .z = z };
        if (!AffinePoint.fromProjectivePointJacobian(&p).isOnCurve())
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

    /// Checks whether two projective points are equal.
    ///
    /// This function determines whether two projective points are equal by comparing their coordinates.
    /// Two projective points are considered equal if they represent the same affine point on the elliptic curve.
    ///
    /// # Arguments
    ///
    /// * `self` - The first projective point.
    /// * `rhs` - The second projective point to compare.
    ///
    /// # Returns
    ///
    /// Returns true if the two projective points are equal, false otherwise.
    ///
    /// # Remarks
    ///
    /// Two projective points (X₁, Y₁, Z₁) and (X₂, Y₂, Z₂) are considered equal if the following conditions hold:
    ///
    /// * X₁ * Z₂^2 = X₂ * Z₁^2
    /// * Y₁ * Z₂^3 = Y₂ * Z₁^3
    ///
    /// These conditions ensure that the two projective points represent the same affine point on the elliptic curve.
    /// If either point is the point at infinity, they are considered equal if and only if both points are the point at infinity.
    pub fn eql(self: Self, rhs: Self) bool {
        // Check if either point is the point at infinity.
        if (self.isIdentity()) return rhs.isIdentity();
        if (rhs.isIdentity()) return false;

        // Compute Z₁^2 and Z₂^2.
        const z1z1 = self.z.square();
        const z2z2 = rhs.z.square();

        // Check if X₁ * Z₂^2 equals X₂ * Z₁^2.
        if (!self.x.mul(z2z2).eql(rhs.x.mul(z1z1))) return false;

        // Check if Y₁ * Z₂^3 equals Y₂ * Z₁^3.
        return self.y.mul(z2z2.mul(rhs.z)).eql(rhs.y.mul(z1z1.mul(self.z)));
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
    /// Returns without performing any operation if the projective point is the identity element
    /// (point at infinity).
    ///
    /// # Cost
    ///
    /// The cost of this operation is calculated as follows:
    /// - 2 multiplications (2M)
    /// - 5 squarings (5S)
    /// - 6 additions (6add)
    /// - 3 multiplications by constants (3*2)
    /// - 1 multiplication by a curve parameter (1*3)
    /// - 1 constant-time multiplication by 8 (1*8)
    pub fn doubleAssign(self: *Self) void {
        // If the point is the point at infinity, no operation is needed.
        if (self.isIdentity()) return;

        // Calculate X1^2
        const xx = self.x.square();

        // Calculate Y1^2
        const yy = self.y.square();

        // Calculate YY^2
        const yyyy = yy.square();

        // Calculate Z1^2
        const zz = self.z.square();

        // Calculate 2*((X1+YY)^2-XX-YYYY)
        const s = self.x.add(yy).square().sub(xx).sub(yyyy).double();

        // Calculate 3*XX+a*ZZ^2
        const m = xx.double().add(xx).add(CurveParams.ALPHA.mul(zz.square()));

        // Calculate T = M^2-2*S
        // X3 = T
        self.x = m.square().sub(s.double());

        // Calculate Z3 = 2*Y1*Z1
        // This is a faster way to compute (Y1+Z1)^2-YY-ZZ
        self.z = self.z.mul(self.y).double();

        // Calculate Y3 = M*(S-X3)-8*YYYY
        self.y = s.sub(self.x).mul(m).sub(yyyy.double().double().double());
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
    pub fn add(self: Self, rhs: *const Self) Self {
        // Make a copy of the original point
        var a = self;
        // Perform point addition in place
        Self.addAssign(&a, rhs);
        // Return the resulting point
        return a;
    }

    /// Negates this projective point.
    ///
    /// This function negates the coordinates of this projective point (`self`) and returns the result.
    /// Negation operation involves negating the y-coordinate while keeping the x and z-coordinates unchanged.
    ///
    /// # Returns
    ///
    /// The negated projective point.
    pub fn neg(self: Self) Self {
        return if (self.isIdentity())
            .{}
        else
            .{ .x = self.x, .y = self.y.neg(), .z = self.z };
    }

    /// Subtracts another projective point from this point and returns the result.
    ///
    /// This function subtracts the coordinates of the provided projective point (`rhs`) from the coordinates
    /// of this projective point (`self`), without modifying the original point. It returns a new
    /// projective point representing the result of the subtraction operation.
    ///
    /// # Arguments
    ///
    /// * `rhs` - A pointer to the projective point to be subtracted from this point.
    ///
    /// # Returns
    ///
    /// A new projective point representing the result of the subtraction operation.
    pub fn sub(self: Self, rhs: *const Self) Self {
        // Make a copy of the original point
        var a = self;
        // Add the negation of the rhs point to this point
        a.addAssign(&rhs.neg());
        // Return the resulting point
        return a;
    }

    /// Performs point addition in Jacobian projective coordinates.
    ///
    /// This function adds the point represented by `rhs` to the point represented by `self`.
    /// Points are represented in Jacobian projective coordinates, which optimize elliptic curve
    /// cryptography operations. The function returns void and updates the current point (`self`)
    /// to the result of the addition operation.
    ///
    /// # Arguments
    ///
    /// * `self` - A mutable reference to the current point.
    /// * `rhs` - A pointer to the point to be added to `self`.
    ///
    /// # Cost Analysis
    ///
    /// The function performs the point addition operation with the following costs:
    /// - 11M (multiplications)
    /// - 5S (squares)
    /// - 9add (additions)
    /// - 4*2 (doublings)
    pub fn addAssign(self: *Self, rhs: *const Self) void {
        // If rhs is the identity point, no operation is needed.
        if (rhs.isIdentity()) {
            return;
        }

        // If self is the identity point, update self to rhs and return.
        if (self.isIdentity()) {
            self.* = rhs.*;
            return;
        }

        // Precomputations for optimization based on the formulas from EFD.
        // See: https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl

        // Z1Z1 = Z1^2
        const z1z1 = self.z.square();

        // Z2Z2 = Z2^2
        const z2z2 = rhs.z.square();

        // U1 = X1*Z2Z2
        const u_1 = self.x.mul(z2z2);

        // U2 = X2*Z1Z1
        const u_2 = rhs.x.mul(z1z1);

        // S1 = Y1*Z2*Z2Z2
        const s1 = self.y.mul(rhs.z).mul(z2z2);

        // S2 = Y2*Z1*Z1Z1
        const s2 = rhs.y.mul(self.z).mul(z1z1);

        // Check if points are equal, leading to point doubling or point at infinity.
        if (u_1.eql(u_2)) {
            if (s1.eql(s2)) {
                // Point doubling operation
                self.doubleAssign();
            } else {
                // Point at infinity
                self.* = Self.identity();
            }
            return;
        }

        // If we're adding -a and a together, self.z becomes zero as H becomes zero.

        // H = U2-U1
        const h = u_2.sub(u_1);

        // I = (2*H)^2
        const i = h.double().square();

        // J = -H*I
        const j = h.neg().mul(i);

        // r = 2*(S2-S1)
        const r = s2.sub(s1).double();

        // V = U1*I
        const v = u_1.mul(i);

        // X3 = r^2 + J - 2*V
        self.x = r.square().add(j).sub(v.double());

        // Y3 = r*(V - X3) + 2*S1*J
        self.y = r.mul(v.sub(self.x)).add(s1.double().mul(j));

        // Z3 = ((Z1+Z2)^2 - Z1Z1 - Z2Z2)*H
        // This is equal to Z3 = 2 * Z1 * Z2 * H, and computing it this way is faster.
        self.z = rhs.z.double().mul(h);
    }
};

test "ProjectivePointJacobian: initUnchecked should return a projective point (even if not valid)" {
    try expectEqual(
        ProjectivePointJacobian{
            .x = Felt252.fromInt(u256, 10),
            .y = Felt252.fromInt(u256, 20),
            .z = Felt252.one(),
        },
        ProjectivePointJacobian.initUnchecked(
            Felt252.fromInt(u256, 10),
            Felt252.fromInt(u256, 20),
            Felt252.one(),
        ),
    );

    try expectEqual(
        ProjectivePointJacobian{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .z = Felt252.one(),
        },
        ProjectivePointJacobian.initUnchecked(
            Felt252.fromInt(u256, 874739451078007766457464989),
            Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            Felt252.one(),
        ),
    );
}

test "ProjectivePointJacobian: init should return a projective point and throw an error when not valid" {
    try expectError(
        EcPointError.PointNotOnCurve,
        ProjectivePointJacobian.init(
            Felt252.fromInt(u256, 10),
            Felt252.fromInt(u256, 20),
            Felt252.one(),
        ),
    );

    try expectEqual(
        ProjectivePointJacobian{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .z = Felt252.one(),
        },
        try ProjectivePointJacobian.init(
            Felt252.fromInt(u256, 874739451078007766457464989),
            Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            Felt252.one(),
        ),
    );
}

test "ProjectivePointJacobian: fromAffinePoint should return a projective point based on an affine point" {
    try expectEqual(
        ProjectivePointJacobian{},
        ProjectivePointJacobian.fromAffinePoint(&.{}),
    );

    try expectEqual(
        ProjectivePointJacobian{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .z = Felt252.one(),
        },
        ProjectivePointJacobian.fromAffinePoint(&.{
            .x = Felt252.fromInt(u256, 874739451078007766457464989),
            .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
            .infinity = false,
        }),
    );
}

test "ProjectivePointJacobian: identity should return the point at infinity" {
    try expectEqual(
        ProjectivePointJacobian{},
        ProjectivePointJacobian.identity(),
    );
}

test "ProjectivePointJacobian: addAssign of P + 0 should return P" {
    const a: AffinePoint = .{
        .x = Felt252.fromInt(u256, 874739451078007766457464),
        .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
        .infinity = false,
    };

    var p = ProjectivePointJacobian.fromAffinePoint(&a);

    p.addAssign(&.{});

    try expectEqual(
        ProjectivePointJacobian{
            .x = Felt252.fromInt(u256, 874739451078007766457464),
            .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
            .z = Felt252.one(),
        },
        p,
    );
}

test "ProjectivePointJacobian: addAssign of 0 + P should return P" {
    var p: ProjectivePointJacobian = .{};

    p.addAssign(&ProjectivePointJacobian.fromAffinePoint(
        &.{
            .x = Felt252.fromInt(u256, 874739451078007766457464),
            .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
            .infinity = false,
        },
    ));

    try expectEqual(
        ProjectivePointJacobian{
            .x = Felt252.fromInt(u256, 874739451078007766457464),
            .y = Felt252.fromInt(u256, 3202429691477156140440114086107030603959626074522568741397770080517060801394),
            .z = Felt252.one(),
        },
        p,
    );
}

test "ProjectivePointJacobian: addAssign P + (-P) should give 0" {
    var p = ProjectivePointJacobian.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    p.addAssign(&ProjectivePointJacobian.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262).neg(),
        .infinity = false,
    }));

    try expectEqual(ProjectivePointJacobian{}, p);
}

test "ProjectivePointJacobian: addAssign P + P should give 2P" {
    var p = ProjectivePointJacobian.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    p.addAssign(&ProjectivePointJacobian.fromAffinePoint(&.{
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
        AffinePoint.fromProjectivePointJacobian(&p),
    );
}

test "ProjectivePointJacobian: addAssign should give the proper point addition" {
    var p = ProjectivePointJacobian.fromAffinePoint(&.{
        .x = Felt252.fromInt(u256, 874739451078007766457464989),
        .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
        .infinity = false,
    });

    p.addAssign(&ProjectivePointJacobian.fromAffinePoint(&.{
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
        AffinePoint.fromProjectivePointJacobian(&p),
    );
}

test "ProjectivePointJacobian: fuzzing testing of arithmetic operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate a random affine point 'a'.
        var a = AffinePoint.rand(random);

        // Generate a random affine point 'b'.
        var b = AffinePoint.rand(random);

        // Generate a random affine point 'c'.
        var c = AffinePoint.rand(random);

        // Convert affine points to Jacobian projective points.
        var a_projective = ProjectivePointJacobian.fromAffinePoint(&a);
        var b_projective = ProjectivePointJacobian.fromAffinePoint(&b);
        var c_projective = ProjectivePointJacobian.fromAffinePoint(&c);
        var zero: ProjectivePointJacobian = .{};

        // Associativity
        try expect(a_projective.add(&b_projective).add(&c_projective).eql(
            a_projective.add(&b_projective).add(&c_projective),
        ));

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
        try expect(a_projective.add(&b_projective).eql(b_projective.add(&a_projective)));

        //  Associativity and commutativity simultaneously
        const a_p_b = ProjectivePointJacobian.fromAffinePoint(
            &AffinePoint.fromProjectivePointJacobian(&a_projective.add(&b_projective)),
        );
        const a_p_c = ProjectivePointJacobian.fromAffinePoint(
            &AffinePoint.fromProjectivePointJacobian(&a_projective.add(&c_projective)),
        );
        const b_p_c = ProjectivePointJacobian.fromAffinePoint(
            &AffinePoint.fromProjectivePointJacobian(&b_projective.add(&c_projective)),
        );
        try expectEqual(
            AffinePoint.fromProjectivePointJacobian(&a_p_b.add(&c_projective)),
            AffinePoint.fromProjectivePointJacobian(&a_p_c.add(&b_projective)),
        );
        try expectEqual(
            AffinePoint.fromProjectivePointJacobian(&a_p_c.add(&b_projective)),
            AffinePoint.fromProjectivePointJacobian(&b_p_c.add(&a_projective)),
        );

        // Doubling
        try expect(a_projective.add(&a_projective).eql(a_projective.double()));
        try expect(b_projective.add(&b_projective).eql(b_projective.double()));
        try expect(c_projective.add(&c_projective).eql(c_projective.double()));
        try expect(zero.eql(zero.double()));
        try expect(zero.eql(zero.neg().double()));
    }
}
