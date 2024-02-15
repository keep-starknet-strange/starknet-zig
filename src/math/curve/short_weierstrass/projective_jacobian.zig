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
        return .{
            .x = self.x,
            .y = self.y.neg(),
            .z = self.z,
        };
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

// test "ProjectivePointJacobian: addAssign P + P should give 2P" {
//     var p = ProjectivePointJacobian.fromAffinePoint(&.{
//         .x = Felt252.fromInt(u256, 874739451078007766457464989),
//         .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
//         .infinity = false,
//     });

//     p.addAssign(&ProjectivePointJacobian.fromAffinePoint(&.{
//         .x = Felt252.fromInt(u256, 874739451078007766457464989),
//         .y = Felt252.fromInt(u256, 498516619889999230417086521843493582191978251645677012430043846185431670262),
//         .infinity = false,
//     }));

//     try expectEqual(
//         AffinePoint{
//             .x = Felt252.fromInt(u256, 1007300233009797052089600572030536234678420387464749955693412487829103372971),
//             .y = Felt252.fromInt(u256, 1628094014246951319213922206675864072767692386561452886899658728389307097247),
//             .infinity = false,
//         },
//         AffinePoint.fromProjectivePointJacobian(&p),
//     );
// }

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

        // Convert affine points 'a' and 'b' to Jacobian projective points.
        const a_projective = ProjectivePointJacobian.fromAffinePoint(&a);
        const b_projective = ProjectivePointJacobian.fromAffinePoint(&b);

        // Make a copy of point 'a' to perform in-place addition later.
        var p = ProjectivePointJacobian.fromAffinePoint(&a);

        // Verify the correctness of subtraction operation between affine points 'a' and 'b'.
        try expectEqual(
            a.sub(&b),
            AffinePoint.fromProjectivePointJacobian(&a_projective.sub(&b_projective)),
        );

        // Verify the correctness of subtraction operation between 'a_projective' and identity point.
        try expectEqual(
            a_projective,
            a_projective.sub(&ProjectivePointJacobian.identity()),
        );

        // Verify the correctness of negation operation on 'a_projective'.
        try expectEqual(
            a_projective.neg(),
            ProjectivePointJacobian.identity().sub(&a_projective),
        );

        // Perform in-place addition of 'b' to 'a'.
        try a.addAssign(&b);

        // Verify the correctness of addition operation between affine points 'a' and 'b'.
        try expectEqual(
            a,
            AffinePoint.fromProjectivePointJacobian(
                &p.add(&b_projective),
            ),
        );

        // Perform in-place addition of 'b_projective' to 'p'.
        p.addAssign(&b_projective);

        // Verify the correctness of 'p' after in-place addition.
        try expectEqual(a, AffinePoint.fromProjectivePointJacobian(&p));
    }
}
