const std = @import("std");
const arithmetic = @import("./arithmetic.zig");
const Field = @import("./fields.zig").Field;
const ConstChoice = @import("./const_choice.zig").ConstChoice;
const TEST_ITERATIONS = @import("../../main.zig").TEST_ITERATIONS;

const expectEqual = std.testing.expectEqual;
const expect = std.testing.expect;

/// This function generates a new type representing an arbitrary-precision integer with a fixed number of limbs.
/// Each limb is a 64-bit unsigned integer, allowing the representation of integers larger than the native machine word size.
///
/// Parameters:
///   - N: The number of limbs for the big integer.
///
/// Returns:
///   - A struct representing a big integer with the specified number of limbs.
pub fn bigInt(comptime N: usize) type {
    return struct {
        const Self = @This();

        /// The `limbs` field is an array of u64 integers that store the individual limbs of the big integer.
        ///
        /// Each limb contributes to the overall magnitude of the integer, allowing representation of large numbers.
        limbs: [N]u64 = [_]u64{0} ** N,

        /// Initializes a big integer with the specified limbs.
        ///
        /// This function initializes a big integer with the given array of limbs.
        /// It creates a new instance of the `bigInt` struct and assigns the provided limbs to the `limbs` field.
        ///
        /// Parameters:
        ///   - limbs: An array of u64 integers representing the limbs of the big integer.
        ///
        /// Returns:
        ///   - A new instance of the `bigInt` struct with the specified limbs.
        pub fn init(limbs: [N]u64) Self {
            return .{ .limbs = limbs };
        }

        /// Converts an integer value to a big integer.
        ///
        /// This function converts an integer value to a big integer representation. The big integer type has a fixed number of limbs, each being a 64-bit unsigned integer. The function handles conversion for various sizes of integer values.
        ///
        /// Parameters:
        ///   - T: The type of the integer to convert.
        ///   - num: The integer value to convert.
        ///
        /// Returns:
        ///   - A big integer representation of the provided integer value.
        ///
        /// Remarks:
        ///   - The function assumes that the provided integer value is non-negative.
        ///   - For integers up to 63 bits, the function directly initializes the field element.
        ///   - For 64-bit integers, the function initializes the field element directly.
        ///   - For integers from 65 to 128 bits, the function performs truncation and division to fit into the limbs of the big integer.
        ///   - For larger integers, the function converts the integer to bytes and then initializes the field element.
        pub fn fromInt(comptime T: type, num: T) Self {
            std.debug.assert(num >= 0);

            // Switch based on the size of the integer value
            return switch (@typeInfo(T).Int.bits) {
                // For integers up to 63 bits, directly initialize the field element
                0...63 => .{ .limbs = .{ @intCast(num), 0, 0, 0 } },
                // For 64-bit integers, initialize the field element directly
                64 => .{ .limbs = .{ num, 0, 0, 0 } },
                // For integers from 65 to 128 bits, perform truncation and division
                65...128 => .{
                    .limbs = .{
                        @truncate(@mod(num, @as(u128, @intCast(std.math.maxInt(u64))) + 1)),
                        @truncate(@divTrunc(num, @as(u128, @intCast(std.math.maxInt(u64))) + 1)),
                        0,
                        0,
                    },
                },
                // For larger integers, convert to bytes and then initialize the field element
                else => blk: {
                    var lbe = [_]u8{0} ** (N * @sizeOf(u64));
                    std.mem.writeInt(T, &lbe, num, .little);
                    break :blk Self.fromBytesLe(lbe);
                },
            };
        }

        /// Convert the field element to a u256 integer.
        ///
        /// Converts the field element to a u256 integer.
        ///
        /// Parameters:
        ///   - self: The field element to convert.
        ///
        /// Returns:
        ///   - A u256 integer representing the field element.
        pub fn toU256(self: Self) u256 {
            return std.mem.readInt(
                u256,
                &self.toBytesLe(),
                .little,
            );
        }

        /// Try to convert the field element to a u64 if its value is small enough.
        ///
        /// Attempts to convert the field element to a u64 if its value is within the representable range.
        ///
        /// Parameters:
        ///   - self: The field element to convert.
        ///   - T: The target type for conversion (must be u64 or smaller).
        ///
        /// Returns:
        ///   - A u64 representation of the field element if conversion succeeds.
        ///   - Error(ValueTooLarge) if the value exceeds the representable range of the target type.
        pub fn toInt(self: Self, comptime T: type) !T {
            const asU256 = self.toU256();
            // Check if the value is small enough to fit into a type T integer
            if (asU256 > std.math.maxInt(T)) return error.ValueTooLarge;

            // Otherwise, it's safe to cast
            return @intCast(asU256);
        }

        /// Returns a big integer representing the value one.
        ///
        /// This function generates a big integer with a value of one. It creates a new instance of the `bigInt` struct
        /// where all limbs are initialized to zero, except for the first limb which is set to one, representing the value one.
        ///
        /// Returns:
        ///   - A new instance of the `bigInt` struct representing the value one.
        pub fn one() Self {
            // Compile-time computation to generate a big integer with a value of one
            comptime {
                // Initialize an array of limbs with all zeros
                var o = [_]u64{0} ** N;
                // Set the first limb to one
                o[0] = 1;
                // Return a new instance of the `bigInt` struct with the generated limbs
                return .{ .limbs = o };
            }
        }

        /// Checks if a big integer is zero.
        ///
        /// This function iterates through each limb of the big integer to determine if it is zero.
        /// If any limb is non-zero, the function returns false, indicating that the big integer is not zero.
        /// If all limbs are zero, the function returns true, indicating that the big integer is zero.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be checked.
        ///
        /// Returns:
        ///   - true if the big integer is zero, false otherwise.
        pub inline fn isZero(self: *const Self) bool {
            // Iterate through each limb of the big integer
            for (0..N) |i| {
                // Check if the current limb is non-zero
                if (self.limbs[i] != 0) return false;
            }
            // If all limbs are zero, return true
            return true;
        }

        /// Generates a random big integer with the specified limbs.
        ///
        /// This function generates a random big integer with the specified number of limbs using a provided random number generator.
        /// It creates a new instance of the `bigInt` struct and assigns randomly generated values to each limb within the specified range.
        ///
        /// Parameters:
        ///   - r: An instance of the `std.Random` random number generator used to generate random limb values.
        ///
        /// Returns:
        ///   - A new instance of the `bigInt` struct representing a randomly generated big integer.
        pub fn rand(r: std.Random) Self {
            // Create a new instance of the `bigInt` struct
            var big_int: Self = .{};
            // Iterate over each limb
            for (0..N) |i|
                // Generate a random u64 value and assign it to the current limb
                big_int.limbs[i] = r.int(u64);

            // Return the randomly generated big integer
            return big_int;
        }

        /// Checks if two big integers are equal.
        ///
        /// This function compares two big integers for equality by performing a byte-wise memory comparison of their limbs.
        /// It returns true if the big integers have identical limb values, indicating equality, and false otherwise.
        ///
        /// Parameters:
        ///   - self: The first big integer to compare.
        ///   - rhs: The second big integer to compare.
        ///
        /// Returns:
        ///   - true if the big integers are equal, false otherwise.
        pub fn eql(self: Self, rhs: Self) bool {
            return std.mem.eql(u64, &self.limbs, &rhs.limbs);
        }

        /// Checks if two big integers are not equal.
        ///
        /// This function compares two big integers for inequality by iterating over their limbs and checking if any corresponding pair of limbs is not equal.
        ///
        /// Parameters:
        ///   - self: The first big integer to compare.
        ///   - rhs: The second big integer to compare.
        ///
        /// Returns:
        ///   - true if the big integers are not equal, false otherwise.
        pub fn ne(self: Self, rhs: Self) bool {
            // Iterate over each limb pair of the big integers
            inline for (self.limbs, rhs.limbs) |ll, rl| {
                // Check if the corresponding limbs are not equal
                if (ll != rl) return true;
            }
            // If all corresponding limbs are equal, return false
            return false;
        }

        /// Checks if a big integer is odd.
        ///
        /// This function determines whether a given big integer is odd by examining the least significant bit of its first limb.
        /// It returns true if the integer is odd (i.e., the LSB is set), and false otherwise.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be checked.
        ///
        /// Returns:
        ///   - true if the big integer is odd, false otherwise.
        pub fn isOdd(self: *const Self) bool {
            return self.limbs[0] & 1 == 1;
        }

        /// Checks if a big integer is even.
        ///
        /// This function determines whether a given big integer is even by negating the result of the `isOdd` function.
        /// It returns true if the integer is even (i.e., not odd), and false otherwise.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be checked.
        ///
        /// Returns:
        ///   - true if the big integer is even, false otherwise.
        pub fn isEven(self: *const Self) bool {
            return !self.isOdd();
        }

        /// Divides a big integer by two.
        ///
        /// This function divides the value of the provided big integer (`self`) by two and returns the result.
        /// It effectively performs a right shift operation on each limb of the big integer.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be divided by two.
        ///
        /// Returns:
        ///   - The big integer resulting from the division by two.
        ///
        /// Notes:
        ///   - This function does not modify the original big integer; it returns a new big integer representing the result of the division.
        ///   - The division is performed in place, and the result is updated in the original big integer.
        ///   - Inline loops are used for performance optimization.
        ///   - The operation effectively performs a right shift of each limb by one bit, equivalent to division by two.
        pub inline fn div2(self: *const Self) Self {
            // Dereference the pointer to obtain the actual big integer
            var a = self.*;
            // Divide the big integer by two using the div2Assign function
            a.div2Assign();
            // Return the result of the division
            return a;
        }

        /// Divides a big integer by two in place.
        ///
        /// This function divides a big integer by two in place, effectively performing a right shift operation on each limb.
        /// It iterates through each limb of the big integer, starting from the most significant limb, and performs the division operation.
        /// During the iteration, it propagates the carry bit from the higher-order bits to the lower-order bits to maintain precision.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be divided by two.
        ///
        /// Returns:
        ///   - void
        ///
        /// Notes:
        ///   - This function modifies the big integer in place, effectively dividing it by two.
        ///   - The carry bit from the higher-order bits is propagated to the lower-order bits to maintain precision during the division operation.
        ///   - Inline loops are used for performance optimization.
        ///   - The operation effectively performs a right shift of each limb by one bit, equivalent to division by two.
        ///   - The division is performed in place, and the result is updated in the original big integer.
        pub inline fn div2Assign(self: *Self) void {
            // Initialize a variable to hold the carry
            var t: u64 = 0;

            // Compile-time variable to iterate through limbs
            comptime var i = N;

            // Iterate through limbs starting from the most significant
            inline while (i > 0) {
                // Decrement the iterator
                i -= 1;
                // Get a pointer to the current limb
                const a = &self.limbs[i];
                // Shift the carry bit to the left
                const t2 = a.* << 63;
                // Divide the limb by 2 (right shift)
                a.* >>= 1;
                // Add the carry bit to the current limb
                a.* |= t;
                // Update the carry with the previous carry bit
                t = t2;
            }
        }

        /// Multiplies a big integer by two.
        ///
        /// This function multiplies the value of the provided big integer (`self`) by two and returns the result along with the carry bit.
        /// It effectively performs a left shift operation on each limb of the big integer.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be multiplied by two.
        ///
        /// Returns:
        ///   - A tuple containing the result of the multiplication and a boolean indicating whether there was a carry.
        ///
        /// Notes:
        ///   - This function does not modify the original big integer; it returns a new big integer representing the result of the multiplication.
        ///   - The multiplication is performed in place, and the result is updated in the original big integer.
        ///   - Inline loops are used for performance optimization.
        ///   - The operation effectively performs a left shift of each limb by one bit, equivalent to multiplication by two.
        pub inline fn mul2(self: *const Self) std.meta.Tuple(&.{ Self, bool }) {
            // Dereference the pointer to obtain the actual big integer
            var a = self.*;
            // Multiply the big integer by two using the mul2Assign function
            const c = a.mul2Assign();
            // Return the result of the multiplication along with the carry bit
            return .{ a, c };
        }

        /// Multiplies a big integer by two in place.
        ///
        /// This function multiplies the value of the provided big integer (`self`) by two in place, modifying the original big integer.
        /// It iterates through each limb of the big integer, starting from the least significant limb, and performs the multiplication operation.
        /// During the iteration, it propagates the carry bit from the lower-order bits to the higher-order bits to maintain precision.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be multiplied by two.
        ///
        /// Returns:
        ///   - A boolean indicating whether there was a carry during the multiplication.
        ///
        /// Notes:
        ///   - This function modifies the big integer in place, effectively multiplying it by two.
        ///   - The carry bit from the lower-order bits is propagated to the higher-order bits to maintain precision during the multiplication operation.
        ///   - Inline loops are used for performance optimization.
        ///   - The operation effectively performs a left shift of each limb by one bit, equivalent to multiplication by two.
        ///   - The multiplication is performed in place, and the result is updated in the original big integer.
        pub inline fn mul2Assign(self: *Self) bool {
            // Initialize a variable to hold the carry
            var last: u64 = 0;

            // Iterate through limbs starting from the least significant
            inline for (0..N) |i| {
                // Get a pointer to the current limb
                const a = &self.limbs[i];
                // Extract the least significant bit
                const tmp = a.* >> 63;
                // Left shift the limb by one bit
                a.* <<= 1;
                // Add the carry bit to the current limb
                a.* |= last;
                // Update the carry with the previous least significant bit
                last = tmp;
            }

            // Return true if there was a carry during the multiplication, false otherwise
            return last != 0;
        }

        /// Adds a big integer to another big integer with carry and returns the result along with a carry flag.
        ///
        /// This function adds a big integer `rhs` to another big integer `self` with carry and returns the result along with a carry flag.
        /// It dereferences the pointers to obtain the actual big integers, performs the addition operation using the `addWithCarryAssign` function,
        /// and then returns a tuple containing the result of the addition operation (`a`) and a boolean flag indicating whether there was a carry.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer to which the second big integer will be added.
        ///   - rhs: A pointer to the second big integer that will be added to the first big integer.
        ///
        /// Returns:
        ///   - A tuple containing the result of the addition operation and a boolean flag indicating whether there was a carry.
        ///
        /// Notes:
        ///   - This function does not modify the original big integers; it only performs the addition operation.
        ///   - Addition with carry is performed using the `addWithCarryAssign` function.
        ///   - The result of the addition operation and the carry flag are returned as a tuple.
        ///   - The carry flag can be used to detect overflow during addition operations.
        pub fn addWithCarry(self: *const Self, rhs: *const Self) std.meta.Tuple(&.{ Self, bool }) {
            // Dereference the pointer to obtain the actual big integer
            var a = self.*;
            // Perform addition with carry and obtain the carry flag
            const carry = a.addWithCarryAssign(rhs);
            // Return a tuple containing the result of the addition operation and the carry flag
            return .{ a, carry };
        }

        /// Adds a big integer to another big integer with carry and assigns the result to the first big integer.
        ///
        /// This function performs addition with carry between two big integers and assigns the result to the first big integer.
        /// It iterates through each limb of the big integers, adding the corresponding limbs along with the carry bit.
        /// At the end of the addition operation, it returns a flag indicating whether there was a carry during the addition process.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer to which the addition result will be assigned.
        ///   - rhs: A pointer to the second big integer that will be added to the first big integer.
        ///
        /// Returns:
        ///   - A boolean flag indicating whether there was a carry during the addition operation.
        ///
        /// Notes:
        ///   - This function modifies the first big integer in place, assigning the result of the addition operation to it.
        ///   - Addition with carry is performed for each corresponding limb of the big integers, starting from the least significant limb.
        ///   - The carry bit from each addition operation is propagated to the next higher-order limb to ensure correct arithmetic.
        ///   - Inline loops are used for performance optimization.
        ///   - At the end of the addition operation, the function returns true if there was a carry, and false otherwise.
        ///   - The carry flag can be used to detect overflow during addition operations.
        ///
        pub fn addWithCarryAssign(self: *Self, rhs: *const Self) bool {
            // Initialize a variable to hold the carry
            var carry: u8 = 0;

            // Iterate through each limb and perform addition with carry
            inline for (0..N) |i|
                // Perform addition with carry for the current limb
                carry = arithmetic.adc(u8, &self.limbs[i], rhs.limbs[i], carry);

            // Return a flag indicating whether there was a carry during addition
            return carry != 0;
        }

        /// Subtracts a big integer from another big integer with borrow and returns the result along with a borrow flag.
        ///
        /// This function subtracts a big integer `rhs` from another big integer `self` with borrow and returns the result along with a borrow flag.
        /// It dereferences the pointers to obtain the actual big integers, performs the subtraction operation using the `subWithBorrowAssign` function,
        /// and then returns a tuple containing the result of the subtraction operation (`a`) and a boolean flag indicating whether there was a borrow.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer from which the second big integer will be subtracted.
        ///   - rhs: A pointer to the second big integer that will be subtracted from the first big integer.
        ///
        /// Returns:
        ///   - A tuple containing the result of the subtraction operation and a boolean flag indicating whether there was a borrow.
        ///
        /// Notes:
        ///   - This function does not modify the original big integers; it only performs the subtraction operation.
        ///   - Subtraction with borrow is performed using the `subWithBorrowAssign` function.
        ///   - The result of the subtraction operation and the borrow flag are returned as a tuple.
        ///   - The borrow flag can be used to detect underflow during subtraction operations.
        pub fn subWithBorrow(self: *const Self, rhs: *const Self) std.meta.Tuple(&.{ Self, bool }) {
            // Dereference the pointer to obtain the actual big integer
            var a = self.*;
            // Perform subtraction with borrow and obtain the borrow flag
            const borrow = a.subWithBorrowAssign(rhs);
            // Return a tuple containing the result of the subtraction operation and the borrow flag
            return .{ a, borrow };
        }

        /// Subtracts a big integer from another big integer with borrow and assigns the result to the first big integer.
        ///
        /// This function performs subtraction with borrow between two big integers and assigns the result to the first big integer.
        /// It iterates through each limb of the big integers, subtracting the corresponding limbs along with the borrow bit.
        /// At the end of the subtraction operation, it returns a flag indicating whether there was a borrow during the subtraction process.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer from which the second big integer will be subtracted, and the result will be assigned.
        ///   - rhs: A pointer to the second big integer that will be subtracted from the first big integer.
        ///
        /// Returns:
        ///   - A boolean flag indicating whether there was a borrow during the subtraction operation.
        ///
        /// Notes:
        ///   - This function modifies the first big integer in place, assigning the result of the subtraction operation to it.
        ///   - Subtraction with borrow is performed for each corresponding limb of the big integers, starting from the least significant limb.
        ///   - The borrow bit from each subtraction operation is propagated to the next higher-order limb to ensure correct arithmetic.
        ///   - Inline loops are used for performance optimization.
        ///   - At the end of the subtraction operation, the function returns true if there was a borrow, and false otherwise.
        ///   - The borrow flag can be used to detect underflow during subtraction operations.
        pub fn subWithBorrowAssign(self: *Self, rhs: *const Self) bool {
            // Initialize a variable to hold the borrow
            var borrow: u8 = 0;

            // Iterate through each limb and perform subtraction with borrow
            inline for (0..N) |i|
                // Perform subtraction with borrow for the current limb
                borrow = arithmetic.sbb(u8, &self.limbs[i], rhs.limbs[i], borrow);

            // Return a flag indicating whether there was a borrow during subtraction
            return borrow != 0;
        }

        /// This function performs a multiplication operation between two big integers.
        /// It multiplies the big integer pointed to by `self` with the big integer pointed to by `rhs`.
        /// The result of the multiplication is stored in the big integer pointed to by `self`.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer operand.
        ///   - rhs: A pointer to the second big integer operand.
        ///
        /// Returns:
        ///   - A tuple containing the updated value of the big integer pointed to by `self` and the result of the multiplication.
        pub fn mul(self: *const Self, rhs: *const Self) std.meta.Tuple(&.{ Self, Self }) {
            // Dereference the pointer to obtain the actual big integer
            var a = self.*;

            // Call the `mulAssign` method to perform the multiplication
            return a.mulAssign(rhs);
        }

        /// This function performs a high multiplication operation between two big integers.
        /// It multiplies the big integer pointed to by `self` with the big integer pointed to by `rhs`,
        /// and returns the high part of the result.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer operand.
        ///   - rhs: A pointer to the second big integer operand.
        ///
        /// Returns:
        ///   - The high part of the result of the multiplication.
        pub fn mulHigh(self: *const Self, rhs: *const Self) Self {
            // Dereference the pointer to obtain the actual big integer
            var a = self.*;

            // Call the `mulAssign` method to perform the multiplication and return the high part
            return a.mulAssign(rhs)[1];
        }

        /// This function performs an in-place multiplication operation between two big integers.
        /// It multiplies the big integer pointed to by `self` with the big integer pointed to by `rhs`,
        /// and stores the result in the big integer pointed to by `self`.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer operand.
        ///   - rhs: A pointer to the second big integer operand.
        ///
        /// Returns:
        ///   - A tuple containing the updated value of the big integer pointed to by `self` and the result of the multiplication.
        pub fn mulAssign(self: *Self, rhs: *const Self) std.meta.Tuple(&.{ Self, Self }) {
            // Check if either operand is zero
            if (self.isZero() or rhs.isZero()) {
                // If either operand is zero, set the result to zero and return
                self.* = .{};
                return .{ .{}, .{} };
            }

            // Define a buffer to store intermediate multiplication results
            const MulBuffer = struct {
                const S = @This();

                // A tuple to store intermediate multiplication results
                buf: std.meta.Tuple(&.{ [N]u64, [N]u64 }) =
                    .{ [_]u64{0} ** N, [_]u64{0} ** N },

                // Retrieves a pointer to the buffer element at the specified index
                fn getBuf(s: *S, index: usize) *u64 {
                    return if (index < N)
                        &s.buf[0][index]
                    else
                        &s.buf[1][index - N];
                }
            };

            // Initialize variables for intermediate results and carry
            var r: MulBuffer = .{};
            var carry: u64 = 0;

            // Perform the multiplication using schoolbook multiplication algorithm
            for (0..N) |i| {
                for (0..N - i) |j|
                    // Perform multiplication with carry and update the buffer
                    r.getBuf(i + j).* = arithmetic.macWithCarry(r.getBuf(i + j).*, self.limbs[i], rhs.limbs[j], &carry);
                // Store the carry in the high buffer
                r.buf[1][i] = carry;
                // Reset the carry for the next iteration
                carry = 0;
            }

            // Copy the result from the buffer to the big integer pointed to by `self`
            @memcpy(&self.limbs, &r.buf[0]);

            // Return a tuple containing the updated value of `self` and the result of the multiplication
            return .{ Self.init(r.buf[0]), Self.init(r.buf[1]) };
        }

        /// This function performs a low multiplication operation between two big integers.
        /// It multiplies the big integer pointed to by `self` with the big integer pointed to by `rhs`,
        /// and returns the low part of the result.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer operand.
        ///   - rhs: A pointer to the second big integer operand.
        ///
        /// Returns:
        ///   - The low part of the result of the multiplication.
        pub fn mulLow(self: *const Self, rhs: *const Self) Self {
            // Dereference the pointer to obtain the actual big integer
            var a = self.*;

            // Call the `mulLowAssign` method to perform the low multiplication and return the result
            a.mulLowAssign(rhs);
            return a;
        }

        /// This function performs an in-place low multiplication operation between two big integers.
        /// It multiplies the big integer pointed to by `self` with the big integer pointed to by `rhs`,
        /// and stores the low part of the result in the big integer pointed to by `self`.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer operand.
        ///   - rhs: A pointer to the second big integer operand.
        ///
        /// Returns:
        ///   - void
        pub fn mulLowAssign(self: *Self, rhs: *const Self) void {
            // Check if either operand is zero
            if (self.isZero() or rhs.isZero())
                // If either operand is zero, set the result to zero and return
                self.* = .{};

            // Initialize a variable to store the result
            var r: Self = .{};
            // Initialize a variable to hold the carry
            var carry: u64 = 0;

            // Perform the low multiplication using schoolbook multiplication algorithm
            for (0..N) |i| {
                for (0..N - i) |j|
                    // Perform multiplication with carry and update the result
                    r.limbs[i + j] = arithmetic.macWithCarry(r.limbs[i + j], self.limbs[i], rhs.limbs[j], &carry);
                // Reset the carry for the next iteration
                carry = 0;
            }

            // Copy the result to the big integer pointed to by `self`
            @memcpy(&self.limbs, &r.limbs);
        }

        /// Compares two big integers and returns their relative order.
        ///
        /// This function compares two big integers `self` and `rhs` and returns their relative order.
        /// It first reverses the order of limbs from little-endian to big-endian to ensure correct comparison.
        /// Then, it compares the big integers using byte-wise comparison to determine their relative order.
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer to be compared.
        ///   - rhs: A pointer to the second big integer to be compared.
        ///
        /// Returns:
        ///   - An enum value representing the relative order of the two big integers:
        ///     - `std.math.Order.lt` if `self` is less than `rhs`.
        ///     - `std.math.Order.eq` if `self` is equal to `rhs`.
        ///     - `std.math.Order.gt` if `self` is greater than `rhs`.
        ///
        /// Notes:
        ///   - This function does not modify the original big integers; it only performs the comparison operation.
        ///   - The big integers are compared in a byte-wise manner after converting their limbs to big-endian order.
        ///   - The comparison result is returned as an enum value indicating the relative order.
        ///   - This function can be used to determine the relative order of big integers for sorting or comparison purposes.
        pub fn cmp(self: *const Self, rhs: *const Self) std.math.Order {
            // Obtain pointers to the limbs of the big integers
            var a = self.limbs;
            var b = rhs.limbs;

            // Reverse the order of limbs from little-endian to big-endian
            _ = std.mem.reverse(u64, a[0..]);
            _ = std.mem.reverse(u64, b[0..]);

            // Compare the big integers using byte-wise comparison
            return std.mem.order(u64, &a, &b);
        }

        /// Checks if a big integer is less than another big integer.
        ///
        /// This function compares the current big integer (`self`) with another big integer (`rhs`) and returns true if `self` is less than `rhs`, and false otherwise.
        ///
        /// Parameters:
        ///   - self: A pointer to the current big integer.
        ///   - rhs: A pointer to the big integer to compare against.
        ///
        /// Returns:
        ///   - `true` if `self` is less than `rhs`, otherwise `false`.
        pub fn lt(self: *const Self, rhs: *const Self) bool {
            // Compare the big integers and return true if self is less than rhs
            return self.cmp(rhs) == .lt;
        }

        /// Checks if a big integer is less than or equal to another big integer.
        ///
        /// This function compares the current big integer (`self`) with another big integer (`rhs`) and returns true if `self` is less than or equal to `rhs`, and false otherwise.
        ///
        /// Parameters:
        ///   - self: A pointer to the current big integer.
        ///   - rhs: A pointer to the big integer to compare against.
        ///
        /// Returns:
        ///   - `true` if `self` is less than or equal to `rhs`, otherwise `false`.
        pub fn lte(self: *const Self, rhs: *const Self) bool {
            // Compare the big integers and return true if self is less than or equal to rhs
            return self.cmp(rhs).compare(.lte);
        }

        /// Checks if a big integer is greater than another big integer.
        ///
        /// This function compares the current big integer (`self`) with another big integer (`rhs`) and returns true if `self` is greater than `rhs`, and false otherwise.
        ///
        /// Parameters:
        ///   - self: A pointer to the current big integer.
        ///   - rhs: A pointer to the big integer to compare against.
        ///
        /// Returns:
        ///   - `true` if `self` is greater than `rhs`, otherwise `false`.
        pub fn gt(self: *const Self, rhs: *const Self) bool {
            // Compare the big integers and return true if self is greater than rhs
            return self.cmp(rhs) == .gt;
        }

        /// Checks if a big integer is greater than or equal to another big integer.
        ///
        /// This function compares the current big integer (`self`) with another big integer (`rhs`) and returns true if `self` is greater than or equal to `rhs`, and false otherwise.
        ///
        /// Parameters:
        ///   - self: A pointer to the current big integer.
        ///   - rhs: A pointer to the big integer to compare against.
        ///
        /// Returns:
        ///   - `true` if `self` is greater than or equal to `rhs`, otherwise `false`.
        pub fn gte(self: *const Self, rhs: *const Self) bool {
            // Compare the big integers and return true if self is greater than or equal to rhs
            return self.cmp(rhs).compare(.gte);
        }

        /// Converts a big integer to a little-endian bit representation.
        ///
        /// This function converts a big integer to its little-endian bit representation.
        /// It iterates through each limb of the big integer, starting from the least significant limb,
        /// and generates a bit representation where each bit corresponds to a single limb.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be converted to a little-endian bit representation.
        ///
        /// Returns:
        ///   - An array of boolean values representing the little-endian bit representation of the big integer.
        ///
        /// Notes:
        ///   - The function generates a bit representation where the least significant bit of the big integer corresponds to the first bit of the array.
        ///   - Each limb of the big integer contributes 64 bits to the overall bit representation.
        ///   - The resulting bit representation is little-endian, with the least significant bits appearing first.
        ///   - Inline loops are used for performance optimization.
        ///   - The function returns an array of boolean values representing the bit representation of the big integer.
        pub fn toBitsLe(self: *const Self) [N * 64]bool {
            // Initialize an array to hold the bit representation
            var bits = [_]bool{false} ** (N * 64);

            // Iterate through each limb of the big integer
            inline for (0..N) |idx_limb| {
                // Calculate the starting index for the current limb
                const i = idx_limb * 64;
                // Iterate through each bit of the current limb
                inline for (0..64) |ind_bit|
                    // Extract the bit value and assign it to the corresponding position in the bit representation array
                    bits[i + ind_bit] = (self.limbs[idx_limb] >> ind_bit) & 1 == 1;
            }

            // Return the little-endian bit representation of the big integer
            return bits;
        }

        /// Converts a big integer to a big-endian bit representation.
        ///
        /// This function converts a big integer to its big-endian bit representation.
        /// It iterates through each limb of the big integer, starting from the most significant limb,
        /// and generates a bit representation where each bit corresponds to a single limb.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be converted to a big-endian bit representation.
        ///
        /// Returns:
        ///   - An array of boolean values representing the big-endian bit representation of the big integer.
        ///
        /// Notes:
        ///   - The function generates a bit representation where the most significant bit of the big integer corresponds to the first bit of the array.
        ///   - Each limb of the big integer contributes 64 bits to the overall bit representation.
        ///   - The resulting bit representation is big-endian, with the most significant bits appearing first.
        ///   - Inline loops are used for performance optimization.
        ///   - The function returns an array of boolean values representing the bit representation of the big integer.
        pub fn toBitsBe(self: *const Self) [N * 64]bool {
            // Initialize an array to hold the bit representation
            var bits = [_]bool{false} ** (N * 64);

            // Iterate through each limb of the big integer
            inline for (0..N) |idx_limb| {
                // Calculate the starting index for the current limb in the big-endian bit representation
                const pre_index = (N - idx_limb - 1) * 64 + 63;
                // Iterate through each bit of the current limb
                inline for (0..64) |ind_bit|
                    // Calculate the index in the bit representation array and extract the bit value
                    bits[pre_index - ind_bit] = (self.limbs[idx_limb] >> ind_bit) & 1 == 1;
            }

            // Return the big-endian bit representation of the big integer
            return bits;
        }

        /// Converts a big integer to a little-endian byte representation.
        ///
        /// This function converts a big integer to its little-endian byte representation.
        /// It iterates through each limb of the big integer, starting from the least significant limb,
        /// and generates a byte representation where each byte corresponds to a single limb.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be converted to a little-endian byte representation.
        ///
        /// Returns:
        ///   - An array of bytes representing the little-endian byte representation of the big integer.
        ///
        /// Notes:
        ///   - The function generates a byte representation where the least significant byte of the big integer corresponds to the first byte of the array.
        ///   - Each limb of the big integer contributes 8 bytes to the overall byte representation.
        ///   - The resulting byte representation is little-endian, with the least significant bytes appearing first.
        ///   - Inline loops are used for performance optimization.
        ///   - The function returns an array of bytes representing the byte representation of the big integer.
        pub fn toBytesLe(self: *const Self) [@sizeOf(u256)]u8 {
            // Initialize an array to hold the byte representation
            var buf: [@sizeOf(u256)]u8 = undefined;

            // Iterate through each limb of the big integer
            inline for (0..N) |i| {
                // Calculate the starting index for the current limb in the little-endian byte representation
                const idx_bytes = i * 8;
                // Write the current limb to the byte representation array using little-endian byte order
                std.mem.writeInt(
                    u64,
                    buf[idx_bytes .. idx_bytes + 8],
                    self.limbs[i],
                    .little,
                );
            }

            // Return the little-endian byte representation of the big integer
            return buf;
        }

        /// Converts a big integer to a big-endian byte representation.
        ///
        /// This function converts a big integer to its big-endian byte representation.
        /// It iterates through each limb of the big integer, starting from the most significant limb,
        /// and generates a byte representation where each byte corresponds to a single limb.
        ///
        /// Parameters:
        ///   - self: The big integer to be converted to a big-endian byte representation.
        ///
        /// Returns:
        ///   - An array of bytes representing the big-endian byte representation of the big integer.
        ///
        /// Notes:
        ///   - The function generates a byte representation where the most significant byte of the big integer corresponds to the first byte of the array.
        ///   - Each limb of the big integer contributes 8 bytes to the overall byte representation.
        ///   - The resulting byte representation is big-endian, with the most significant bytes appearing first.
        ///   - Inline loops are used for performance optimization.
        ///   - The function returns an array of bytes representing the byte representation of the big integer.
        pub fn toBytesBe(self: Self) [@sizeOf(u256)]u8 {
            // Initialize an array to hold the byte representation
            var buf: [@sizeOf(u256)]u8 = undefined;

            // Iterate through each limb of the big integer
            inline for (0..N) |i| {
                // Calculate the starting index for the current limb in the big-endian byte representation
                const idx_bytes = i * 8;
                // Write the current limb to the byte representation array using big-endian byte order
                std.mem.writeInt(
                    u64,
                    buf[idx_bytes .. idx_bytes + 8],
                    self.limbs[N - 1 - i],
                    .big,
                );
            }

            // Return the big-endian byte representation of the big integer
            return buf;
        }

        /// Creates a big integer from a byte array in little-endian order.
        ///
        /// This function constructs a big integer from a byte array by converting each set of 8 bytes
        /// (corresponding to one limb) into a u64 integer and storing it in the big integer's limbs array.
        /// The byte array is assumed to represent the limbs of the big integer in little-endian order.
        ///
        /// Parameters:
        ///   - bytes: A byte array representing the limbs of the big integer in little-endian order.
        ///
        /// Returns:
        ///   - A big integer constructed from the provided byte array.
        pub fn fromBytesLe(bytes: [@sizeOf(u256)]u8) Self {
            // Initialize a new big integer with all limbs set to zero.
            var r: Self = .{};

            // Iterate through each limb and populate it with data from the byte array.
            inline for (0..N) |i| {
                // Calculate the index of the first byte of the current limb.
                const idx_byte = i * 8;

                // Read 8 bytes from the byte array and convert them to a u64 integer in little-endian order.
                // Store the resulting u64 integer in the current limb of the big integer.
                r.limbs[i] = std.mem.readInt(u64, bytes[idx_byte .. idx_byte + 8], .little);
            }

            // Return the constructed big integer.
            return r;
        }

        /// Creates a big integer from a byte array in big-endian order.
        ///
        /// This function constructs a big integer from a byte array by converting each set of 8 bytes
        /// (corresponding to one limb) into a u64 integer and storing it in the big integer's limbs array.
        /// The byte array is assumed to represent the limbs of the big integer in big-endian order.
        ///
        /// Parameters:
        ///   - bytes: A byte array representing the limbs of the big integer in big-endian order.
        ///
        /// Returns:
        ///   - A big integer constructed from the provided byte array.
        pub fn fromBytesBe(bytes: [@sizeOf(u256)]u8) Self {
            // Initialize a new big integer with all limbs set to zero.
            var r: Self = .{};

            // Iterate through each limb and populate it with data from the byte array.
            inline for (0..N) |i| {
                // Calculate the index of the first byte of the current limb.
                const idx_byte = i * 8;

                // Read 8 bytes from the byte array and convert them to a u64 integer in big-endian order.
                // Store the resulting u64 integer in the current limb of the big integer.
                r.limbs[N - 1 - i] = std.mem.readInt(u64, bytes[idx_byte .. idx_byte + 8], .big);
            }

            // Return the constructed big integer.
            return r;
        }

        /// Creates a big integer from a little-endian bit representation.
        ///
        /// This function constructs a big integer from a little-endian bit representation stored in a boolean array.
        ///
        /// Parameters:
        ///   - bits: A boolean array representing the little-endian bit representation of the big integer.
        ///
        /// Returns:
        ///   - A new instance of the big integer constructed from the little-endian bit representation.
        pub fn fromBitsLe(bits: [@bitSizeOf(u256)]bool) Self {
            // Initialize the result big integer
            var res: Self = .{};

            // Iterate over each limb of the big integer
            inline for (&res.limbs, 0..) |*res_limb, i| {
                // Calculate the starting index for the current limb in the bit array
                const limb_start_index = i * 64;
                // Iterate over each bit within the current limb
                inline for (0..@bitSizeOf(u64)) |j| {
                    // Convert the boolean value to an integer (0 or 1) and shift it to its position within the limb
                    // Then, bitwise OR it with the current limb of the result big integer
                    res_limb.* |= @as(u64, @intCast(@intFromBool(bits[limb_start_index + j]))) << j;
                }
            }

            // Return the constructed big integer
            return res;
        }

        /// Constructs a big integer from a big-endian array of bits.
        ///
        /// This function constructs a big integer from a big-endian array of bits and returns the result.
        ///
        /// # Parameters
        /// - `bits`: A big-endian array of bits representing the big integer.
        ///
        /// # Returns
        /// The big integer constructed from the big-endian array of bits.
        pub fn fromBitsBe(bits: [@bitSizeOf(u256)]bool) Self {
            // Create a copy of the input bits array to work with little-endian representation.
            var bits_le: [@bitSizeOf(u256)]bool = bits;
            // Reverse the bits array to convert it to little-endian representation.
            std.mem.reverse(bool, &bits_le);
            // Construct the big integer from the little-endian bits representation.
            return Self.fromBitsLe(bits_le);
        }

        /// Retrieves the value of the bit at the specified index in the big integer.
        ///
        /// This function checks if the bit at the specified index is set (1) or unset (0) in the big integer.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer from which the bit value will be retrieved.
        ///   - i: The index of the bit to retrieve. Indices start from 0 for the least significant bit.
        ///
        /// Returns:
        ///   - `true` if the bit at the specified index is set (1), `false` otherwise.
        ///
        /// Notes:
        ///   - If the specified index is greater than or equal to the total number of bits in the big integer, the function returns `false`.
        ///   - The function calculates the index of the limb and the position within the limb corresponding to the specified bit index.
        ///   - It then checks if the bit at the calculated position within the corresponding limb is set.
        pub fn getBit(self: *const Self, i: usize) bool {
            // Check if the specified index exceeds the total number of bits in the big integer.
            if (i >= comptime 64 * N) return false;

            // Calculate the index of the limb containing the specified bit.
            const limb: usize = i / 64;
            // Calculate the position within the limb corresponding to the specified bit index.
            // Check if the bit at the calculated position within the limb is set.
            return (self.limbs[limb] & (@as(usize, 1) << @intCast(i - (64 * limb)))) != 0;
        }

        /// Performs a bitwise left shift operation on a big integer.
        ///
        /// This function shifts the bits of the big integer to the left by the specified number of positions.
        /// The shift is performed in place, and the result is returned as a new instance of the `BigInt` struct.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be shifted.
        ///   - rhs: The number of positions to shift the bits to the left.
        ///
        /// Returns:
        ///   - A new instance of the `BigInt` struct representing the result of the bitwise left shift operation.
        pub fn shl(self: *const Self, rhs: u32) Self {
            // Dereference the pointer to obtain the actual big integer.
            var a = self.*;
            // Call the shlAssign function to perform the bitwise left shift operation in place.
            a.shlAssign(rhs);
            // Return the resulting big integer after the shift operation.
            return a;
        }

        /// Performs a bitwise left shift operation on a big integer in place.
        ///
        /// This function shifts the bits of the big integer to the left by the specified number of positions.
        /// The shift is performed in place, modifying the original big integer.
        ///
        /// The operation does not return an overflow if the number of bit shifted is greater than N * 64.
        /// Result will be saturated to zero in this scenario.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be shifted.
        ///   - rhs: The number of positions to shift the bits to the left.
        ///
        /// Returns:
        ///   - void
        ///
        /// Notes:
        ///   - If the number of positions to shift is greater than or equal to `64 * N`, where `N` is the number of limbs of the big integer,
        ///     the big integer is set to zero and the function returns early.
        ///   - The shift is performed by shifting each limb for one position to the left. If a shift of more than 64 positions is required,
        ///     multiple iterations are performed until the remaining shift is less than 64.
        pub fn shlAssign(self: *Self, rhs: u32) void {
            // Check for overflow.
            // If the number of positions to shift is greater than or equal to the total bit width of the big integer,
            // set the big integer to zero and return early.
            if (rhs >= comptime 64 * N) {
                self.* = .{};
                return;
            }

            // Initialize the remaining shift count.
            var shift = rhs;

            // Perform the shift operation in blocks of 64 bits until the remaining shift count is less than 64.
            while (shift >= 64) {
                // Temporary variable to hold the shifted out bits.
                var t: u64 = 0;
                // Shift each limb for one position to the left within the block of 64 bits.
                inline for (0..N) |i| {
                    std.mem.swap(u64, &t, &self.limbs[i]);
                }
                // Update the remaining shift count.
                shift -= 64;
            }

            // If there are remaining shifts to perform.
            if (shift > 0) {
                // Temporary variable to hold the shifted out bits.
                var t: u64 = 0;
                // Iterate through each limb and perform the remaining shifts.
                inline for (0..N) |i| {
                    // Dereference the pointer to the current limb.
                    const a = &self.limbs[i];
                    // Perform a logical right shift on the current limb to get the bits shifted out.
                    const t2 = a.* >> @intCast(64 - shift);
                    // Perform the left shift operation on the current limb.
                    a.* <<= @intCast(shift);
                    // Combine the shifted out bits with the current limb using bitwise OR.
                    a.* |= t;
                    // Update the temporary variable with the shifted out bits for the next iteration.
                    t = t2;
                }
            }
        }

        /// Performs a bitwise right shift operation on a big integer.
        ///
        /// This function shifts the bits of the big integer to the right by the specified number of positions.
        /// The shift is performed in place, and the result is returned as a new instance of the `BigInt` struct.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be shifted.
        ///   - rhs: The number of positions to shift the bits to the right.
        ///
        /// Returns:
        ///   - A new instance of the `BigInt` struct representing the result of the bitwise right shift operation.
        pub fn shr(self: *const Self, rhs: u32) Self {
            // Dereference the pointer to obtain the actual big integer.
            var a = self.*;
            // Call the shrAssign function to perform the bitwise right shift operation in place.
            a.shrAssign(rhs);
            // Return the resulting big integer after the shift operation.
            return a;
        }

        /// Performs a bitwise right shift operation on a big integer in place.
        ///
        /// This function shifts the bits of the big integer to the right by the specified number of positions.
        /// The shift is performed in place, modifying the original big integer.
        ///
        /// The operation does not return an overflow if the number of bit shifted is greater than N * 64.
        /// Result will be saturated to zero in this scenario.
        ///
        /// Parameters:
        ///   - self: A pointer to the big integer to be shifted.
        ///   - rhs: The number of positions to shift the bits to the right.
        ///
        /// Returns:
        ///   - void
        ///
        /// Notes:
        ///   - If the number of positions to shift is greater than or equal to `64 * N`, where `N` is the number of limbs of the big integer,
        ///     the big integer is set to zero and the function returns early.
        ///   - The shift is performed by shifting each limb for one position to the right. If a shift of more than 64 positions is required,
        ///     multiple iterations are performed until the remaining shift is less than 64.
        pub fn shrAssign(self: *Self, rhs: u32) void {
            // Check for overflow.
            // If the number of positions to shift is greater than or equal to the total bit width of the big integer,
            // set the big integer to zero and return early.
            if (rhs >= comptime 64 * N) {
                self.* = .{};
                return;
            }

            // Initialize the remaining shift count.
            var shift = rhs;

            // Perform the shift operation in blocks of 64 bits until the remaining shift count is less than 64.
            while (shift >= 64) {
                // Temporary variable to hold the shifted out bits.
                var t: u64 = 0;
                // Start from the most significant limb and shift each limb for one position to the right.
                var limb = N;
                while (limb > 0) {
                    limb -= 1;
                    std.mem.swap(u64, &t, &self.limbs[limb]);
                }
                // Update the remaining shift count.
                shift -= 64;
            }

            // If there are remaining shifts to perform.
            if (shift > 0) {
                // Temporary variable to hold the shifted out bits.
                var t: u64 = 0;
                // Start from the most significant limb and perform the remaining shifts.
                var limb = N;
                while (limb > 0) {
                    limb -= 1;
                    // Dereference the pointer to the current limb.
                    const a = &self.limbs[limb];
                    // Perform a logical left shift on the current limb to get the bits shifted out.
                    const t2 = a.* << @intCast(64 - shift);
                    // Perform the right shift operation on the current limb.
                    a.* >>= @intCast(shift);
                    // Combine the shifted out bits with the current limb using bitwise OR.
                    a.* |= t;
                    // Update the temporary variable with the shifted out bits for the next iteration.
                    t = t2;
                }
            }
        }

        /// Generates a new instance of `Self` with all limbs set to the maximum value of `u64`.
        ///
        /// This function creates and returns a new instance of `Self` with each limb initialized to the maximum value of `u64`.
        ///
        /// Returns:
        ///   - A new instance of `Self` with all limbs set to the maximum value of `u64`.
        pub fn max() Self {
            // Creates a new instance of `Self` with all limbs set to the maximum value of `u64`.
            return .{
                .limbs = .{
                    std.math.maxInt(u64),
                    std.math.maxInt(u64),
                    std.math.maxInt(u64),
                    std.math.maxInt(u64),
                },
            };
        }

        /// Returns the number of bits needed to represent the number as little endian.
        ///
        /// This function calculates and returns the number of bits needed to represent the number as little endian format.
        ///
        /// # Parameters
        /// - `self`: A pointer to the struct instance.
        ///
        /// # Returns
        /// The number of bits needed to represent the number as little endian.
        pub fn numBitsLe(self: *const Self) usize {
            // Initialize the variable `l` to the number of limbs.
            var l: usize = N;
            // Iterate over each limb in reverse order.
            while (l > 0) {
                // Decrement `l`.
                l -= 1;
                // Check if the current limb is non-zero.
                if (self.limbs[l] != 0) {
                    // Calculate the number of bits needed to represent the non-zero limb.
                    return @bitSizeOf(u64) * (l + 1) - @clz(self.limbs[l]);
                }
            }
            // Return 0 if all limbs are zero.
            return 0;
        }

        /// Performs a bitwise OR operation between two big integers.
        ///
        /// This function calculates the bitwise OR between two big integers and returns the result.
        ///
        /// # Parameters
        /// - `self`: A pointer to the first big integer.
        /// - `rhs`: A pointer to the second big integer.
        ///
        /// # Returns
        /// The result of the bitwise OR operation between the two big integers.
        pub fn bitOr(self: *const Self, rhs: *const Self) Self {
            // Dereference the pointer to obtain the actual big integer.
            var a = self.*;
            // Perform the bitwise OR operation and assign the result to `a`.
            a.bitOrAssign(rhs);
            // Return the result of the operation.
            return a;
        }

        /// Performs a bitwise OR operation in place on a big integer.
        ///
        /// This function calculates the bitwise OR between two big integers and assigns the result to the first big integer.
        ///
        /// # Parameters
        /// - `self`: A pointer to the big integer to be modified.
        /// - `rhs`: A pointer to the big integer used for the OR operation.
        pub fn bitOrAssign(self: *Self, rhs: *const Self) void {
            // Perform a bitwise OR operation on each limb of the big integers.
            inline for (0..N) |i|
                self.limbs[i] |= rhs.limbs[i];
        }

        /// Performs a bitwise AND operation between two big integers.
        ///
        /// This function calculates the bitwise AND between two big integers and returns the result.
        ///
        /// # Parameters
        /// - `self`: A pointer to the first big integer.
        /// - `rhs`: A pointer to the second big integer.
        ///
        /// # Returns
        /// The result of the bitwise AND operation between the two big integers.
        pub fn bitAnd(self: *const Self, rhs: *const Self) Self {
            // Dereference the pointer to obtain the actual big integer.
            var a = self.*;
            // Perform the bitwise AND operation and assign the result to `a`.
            a.bitAndAssign(rhs);
            // Return the result of the operation.
            return a;
        }

        /// Performs a bitwise AND operation in place on a big integer.
        ///
        /// This function calculates the bitwise AND between two big integers and assigns the result to the first big integer.
        ///
        /// # Parameters
        /// - `self`: A pointer to the big integer to be modified.
        /// - `rhs`: A pointer to the big integer used for the AND operation.
        pub fn bitAndAssign(self: *Self, rhs: *const Self) void {
            // Perform a bitwise AND operation on each limb of the big integers.
            inline for (0..N) |i|
                self.limbs[i] &= rhs.limbs[i];
        }

        /// Performs a bitwise XOR operation between two big integers.
        ///
        /// This function performs a bitwise XOR operation between two big integers and returns the result.
        ///
        /// # Parameters
        /// - `self`: A pointer to the first big integer operand.
        /// - `rhs`: A pointer to the second big integer operand.
        ///
        /// # Returns
        /// The result of the bitwise XOR operation.
        pub fn bitXor(self: *const Self, rhs: *const Self) Self {
            // Dereference the pointer to obtain the actual big integer.
            var a = self.*;
            // Perform a bitwise XOR operation between the two big integers.
            a.bitXorAssign(rhs);
            // Return the result of the operation.
            return a;
        }

        /// Performs an in-place bitwise XOR operation with another big integer.
        ///
        /// This function performs an in-place bitwise XOR operation with another big integer.
        ///
        /// # Parameters
        /// - `self`: A pointer to the big integer to be modified.
        /// - `rhs`: A pointer to the second big integer operand.
        pub fn bitXorAssign(self: *Self, rhs: *const Self) void {
            // Iterate over the limbs of the big integers and perform the bitwise XOR operation.
            inline for (0..N) |i|
                self.limbs[i] ^= rhs.limbs[i];
        }

        /// Selects between two big integers based on a constant choice.
        ///
        /// This function selects between two big integers based on a constant choice provided as an argument. If the constant choice is `TRUE`, the function returns the second big integer (`rhs`), otherwise, it returns the first big integer (`self`).
        ///
        /// Parameters:
        ///   - self: A pointer to the first big integer.
        ///   - rhs: A pointer to the second big integer.
        ///   - c: A constant choice indicating which big integer to select.
        ///
        /// Returns:
        ///   - The selected big integer.
        pub fn select(self: *const Self, rhs: *const Self, c: ConstChoice) Self {
            return if (c.eql(&ConstChoice.TRUE)) rhs.* else self.*;
        }

        /// Computes division with remainder for two big integers.
        ///
        /// This function computes division with remainder for two big integers using a variant of long division algorithm. It returns a tuple containing the quotient and the remainder.
        ///
        /// Parameters:
        ///   - self: A pointer to the dividend big integer.
        ///   - rhs: A pointer to the divisor big integer.
        ///
        /// Returns:
        ///   - A tuple containing the quotient and the remainder.
        ///
        /// Remarks:
        ///   - The function assumes that the divisor big integer is non-zero.
        ///   - The division algorithm used is a variant of long division.
        pub fn divRem(self: *const Self, rhs: *const Self) std.meta.Tuple(&.{ Self, Self }) {
            // Ensure that the divisor is not zero
            std.debug.assert(!rhs.isZero());

            // Calculate the number of bits in the divisor
            const mb = rhs.numBitsLe();

            // Initialize the remainder as the dividend
            var rm = self.*;

            // Initialize the quotient as zero
            var qt: Self = .{};

            // Calculate the number of bits to shift the divisor
            var bd: u32 = @intCast(N * @bitSizeOf(u64) - mb);

            // Shift the divisor to align with the most significant bit of the remainder
            var c = rhs.shl(bd);

            // Perform long division algorithm
            while (true) {
                // Compute the difference between the remainder and the shifted divisor
                const rb = rm.subWithBorrow(&c);

                // Determine whether to subtract or not based on the borrow
                const choice = ConstChoice.initFromBool(rb[1]);

                // Update the remainder based on the choice
                rm = rb[0].select(&rm, choice);

                // Update the quotient based on the choice
                qt = qt.bitOr(&comptime Self.one()).select(&qt, choice);

                // Check if the division process is complete
                if (bd == 0) break;

                // Update the shift count and the shifted divisor
                bd -= 1;
                c.shrAssign(1);
                qt.shlAssign(1);
            }

            // Return the computed quotient and remainder as a tuple
            return .{ qt, rm };
        }

        /// Computes the remainder of dividing `self` by `rhs`, returning the remainder in variable-time with respect to `rhs`.
        ///
        /// When used with a fixed `rhs`, this function is constant-time with respect to `self`.
        ///
        /// Parameters:
        ///   - self: A pointer to the dividend big integer.
        ///   - rhs: A pointer to the divisor big integer.
        ///
        /// Returns:
        ///   - The remainder of dividing `self` by `rhs`.
        ///
        /// Remarks:
        ///   - This function is equivalent to obtaining the second element of the tuple returned by `divRem`.
        pub fn rem(self: *const Self, rhs: *const Self) Self {
            // Ensure that the divisor is not zero
            std.debug.assert(!rhs.isZero());

            // Calculate the number of bits in the divisor
            const mb = rhs.numBitsLe();

            // Initialize the remainder as the dividend
            var rm = self.*;

            // Calculate the number of bits to shift the divisor
            var bd: u32 = @intCast(N * @bitSizeOf(u64) - mb);

            // Shift the divisor to align with the most significant bit of the remainder
            var c = rhs.shl(bd);

            // Perform long division algorithm
            while (true) {
                // Compute the difference between the remainder and the shifted divisor
                const rb = rm.subWithBorrow(&c);

                // Update the remainder based on the choice
                rm = rb[0].select(&rm, ConstChoice.initFromBool(rb[1]));

                // Check if the division process is complete
                if (bd == 0) break;

                // Update the shift count and the shifted divisor
                bd -= 1;
                c.shrAssign(1);
            }

            // Return the computed remainder
            return rm;
        }

        /// Performs the modular multiplication operation of two big integers within the Montgomery field modulo `p`.
        ///
        /// This function computes the product of `self` and `rhs` modulo `p` using the Montgomery reduction technique.
        /// It ensures that the modulus `p` is odd, as even moduli are currently unsupported and will panic.
        ///
        /// Parameters:
        ///   - self: A pointer to the multiplicand big integer.
        ///   - rhs: A pointer to the multiplier big integer.
        ///   - p: A pointer to the modulus big integer.
        ///
        /// Returns:
        ///   - The result of the modular multiplication operation (`self * rhs % p`) within the Montgomery field.
        ///
        /// Remarks:
        ///   - This function leverages the Montgomery reduction technique for efficient modular multiplication.
        ///   - It requires `p` to be an odd modulus; otherwise, it will panic.
        ///   - Montgomery multiplication is efficient for repeated modular multiplications with the same modulus.
        pub fn mulMod(self: *const Self, rhs: *const Self, comptime p: *const Self) Self {
            // Ensure that the modulus is odd
            if (p.isOdd()) {
                // Initialize the Montgomery field with modulus `p`
                const field = Field(N, comptime p.toU256());

                // Perform Montgomery multiplication
                return field.fromMontgomery(field.fromBytesLe(self.toBytesLe())
                    .mul(&field.fromBytesLe(rhs.toBytesLe())));
            }
            // Panics if the modulus is even (unsupported)
            // TODO: support for even `p`?
            @panic("even moduli are currently unsupported");
        }
    };
}

test "bigInt: div2 function should divide by 2" {
    // Test case: Divide a big integer by 2
    // Initialize a big integer with a value
    var a = bigInt(4).init(.{ 8446744, 0, 0, 0 });
    // Perform division by 2 in place
    a.div2Assign();
    // Assert that the result matches the expected value
    try expectEqual([_]u64{ 4223372, 0, 0, 0 }, a.limbs);

    // Test case: Divide zero by 2
    // Initialize a big integer with zero value
    var b = bigInt(4).init(.{ 0, 0, 0, 0 });
    // Perform division by 2 in place
    b.div2Assign();
    // Assert that the result is still zero
    try expectEqual([_]u64{ 0, 0, 0, 0 }, b.limbs);
}

test "bigInt: constants" {
    // Test case: Verify initialization of zero constant
    // Assert that the zero constant matches the expected value
    try expectEqual(bigInt(4).init(.{ 0, 0, 0, 0 }), comptime bigInt(4){});

    // Test case: Verify initialization of one constant
    // Assert that the one constant matches the expected value
    try expectEqual(bigInt(4).init(.{ 1, 0, 0, 0 }), comptime bigInt(4).one());
}

test "bigInt: fuzzing test for comparison" {
    // Test case: Fuzzing test for equality
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Test case: Verify equality of randomly generated big integers
        // Generate random unsigned integers of different sizes.
        var a = bigInt(4).rand(random);
        var b = bigInt(4).rand(random);
        var c = bigInt(4).rand(random);
        // Obtain constant big integers for comparison
        var one = comptime bigInt(4).one();
        var zero = comptime bigInt(4){};

        // Assert that each big integer is equal to itself
        try expect(a.eql(a));
        try expect(b.eql(b));
        try expect(c.eql(c));

        // Assert that each big integer is equal to itself
        try expect(!a.ne(a));
        try expect(!b.ne(b));
        try expect(!c.ne(c));

        // Assert non equality
        if (!a.eql(b)) try expect(a.ne(b));
        if (!a.eql(c)) try expect(a.ne(c));
        if (!b.eql(c)) try expect(b.ne(c));

        // Assert isZero method for each big integer
        try expect(!a.isZero());
        try expect(!b.isZero());
        try expect(!c.isZero());
        try expect(!one.isZero());
        try expect(zero.isZero());

        // Assert that each big integer is equal to itself using the cmp function
        try expect(a.cmp(&a) == .eq);
        try expect(b.cmp(&b) == .eq);
        try expect(c.cmp(&c) == .eq);

        // Assert that each big integer is less than or equal to itself
        try expect(a.lte(&a));
        try expect(b.lte(&b));
        try expect(c.lte(&c));

        // Assert that each big integer is not less than itself
        try expect(!a.lt(&a));
        try expect(!b.lt(&b));
        try expect(!c.lt(&c));

        // Assert that each big integer is not greater than itself
        try expect(!a.gt(&a));
        try expect(!b.gt(&b));
        try expect(!c.gt(&c));

        // Assert that each big integer is greater than or equal to itself
        try expect(a.gte(&a));
        try expect(b.gte(&b));
        try expect(c.gte(&c));

        // Assert that constant big integers are equal to themselves
        try expect(one.eql(one));
        try expect(zero.eql(zero));

        // Assert that one is greater than zero and greater than or equal to zero
        try expect(one.gt(&zero));
        try expect(one.gte(&zero));
        // Assert that one is not less than zero and not less than or equal to zero
        try expect(!one.lt(&zero));
        try expect(!one.lte(&zero));

        // Assert that zero is not greater than one and not greater than or equal to one
        try expect(!zero.gt(&one));
        try expect(!zero.gte(&one));
        // Assert that zero is less than one and less than or equal to one
        try expect(zero.lt(&one));
        try expect(zero.lte(&one));
    }
}

test "bigInt: fuzzing test for add and sub operations" {
    // Test case: Fuzzing test for addition and subtraction operations
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Test case: Verify addition and subtraction operations with random big integers
        // Generate random unsigned integers of different sizes.
        const a = bigInt(4).rand(random);
        const b = bigInt(4).rand(random);
        const c = bigInt(4).rand(random);

        // Constant zero big integer
        const zero = comptime bigInt(4){};

        // Test addition with zero
        // Assert that adding zero to a big integer results in the same big integer
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ a, false }),
            a.addWithCarry(&zero),
        );
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ b, false }),
            b.addWithCarry(&zero),
        );
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ c, false }),
            c.addWithCarry(&zero),
        );

        // Test subtraction with zero
        // Assert that subtracting zero from a big integer results in the same big integer
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ a, false }),
            a.subWithBorrow(&zero),
        );
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ b, false }),
            b.subWithBorrow(&zero),
        );
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ c, false }),
            c.subWithBorrow(&zero),
        );

        // Test subtraction resulting in zero
        // Assert that subtracting a big integer from itself results in zero
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ zero, false }),
            a.subWithBorrow(&a),
        );
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ zero, false }),
            b.subWithBorrow(&b),
        );
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bool }), .{ zero, false }),
            c.subWithBorrow(&c),
        );
    }
}

test "bigInt: fuzzing test for mul and div operations" {
    // Test case: Fuzzing test for multiplication and division operations
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {

        // Test case: Verify multiplication and division operations with random big integers
        // Generate random unsigned integers of different sizes.
        const a = bigInt(4).rand(random);
        const b = bigInt(4).rand(random);
        const c = bigInt(4).rand(random);

        // Constant zero big integer
        const zero = comptime bigInt(4){};

        // Constant one big integer
        const one = comptime bigInt(4).one();

        // Test addition with carry operation
        // Verify that adding a big integer with carry yields the same result as multiplying by two
        try expectEqual(zero.addWithCarry(&zero), zero.mul2());
        try expectEqual(one.addWithCarry(&one), one.mul2());
        try expectEqual(a.addWithCarry(&a), a.mul2());
        try expectEqual(b.addWithCarry(&b), b.mul2());
        try expectEqual(c.addWithCarry(&c), c.mul2());

        // Multiplication by zero
        try expect(a.mul(&zero)[0].eql(zero));
        try expect(zero.mul(&a)[0].eql(zero));
        try expect(zero.mul(&zero)[0].eql(zero));

        try expect(a.mulLow(&zero).eql(zero));
        try expect(zero.mulLow(&a).eql(zero));
        try expect(zero.mulLow(&zero).eql(zero));

        try expect(a.mulHigh(&zero).eql(zero));
        try expect(zero.mulHigh(&a).eql(zero));
        try expect(zero.mulHigh(&zero).eql(zero));

        // Associativity
        try expect(a.mul(&b)[0].mul(&c)[0].eql(
            a.mul(&b.mul(&c)[0])[0],
        ));
        try expect(a.mul(&b)[0].mul(&c)[0].eql(
            a.mulLow(&b.mulLow(&c)),
        ));

        // Commutativity
        try expect(a.mul(&b)[0].eql(b.mul(&a)[0]));
        try expect(a.mul(&c)[0].eql(c.mul(&a)[0]));
        try expect(b.mul(&c)[0].eql(c.mul(&b)[0]));

        try expect(b.mulLow(&a).eql(a.mulLow(&b)));
        try expect(c.mulLow(&a).eql(a.mulLow(&c)));
        try expect(c.mulLow(&b).eql(b.mulLow(&c)));

        //  Associativity and commutativity simultaneously
        try expect(a.mul(&b)[0].mul(&c)[0].eql(a.mul(&c)[0].mul(&b)[0]));
        try expect(a.mul(&c)[0].mul(&b)[0].eql(b.mul(&c)[0].mul(&a)[0]));

        try expect(a.mulLow(&b).mulLow(&c).eql(a.mulLow(&c).mulLow(&b)));
        try expect(a.mulLow(&c).mulLow(&b).eql(b.mulLow(&c).mulLow(&a)));
    }
}

test "bigInt: division with remainder" {
    // Test case: Fuzzing test for division operations
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {

        // Test case: Verify multiplication and division operations with random big integers
        // Generate random unsigned integers of different sizes.
        const a = bigInt(4).rand(random);
        const b = bigInt(4).rand(random);

        // Verify that the division with remainder operation works correctly.
        try expectEqual(
            @as(
                std.meta.Tuple(&.{ bigInt(4), bigInt(4) }),
                .{ a.shr(128), .{} },
            ),
            a.shr(128).mulLow(&b.shr(128)).divRem(&b.shr(128)),
        );
    }

    // Iterate over predefined test cases.
    for (
        [_]std.meta.Tuple(&.{ u256, u256, u256, u256 }){
            .{ 200, 2, 100, 0 },
            .{ 100, 25, 4, 0 },
            .{ 100, 10, 10, 0 },
            .{ 1024, 8, 128, 0 },
            .{ 27, 13, 2, 1 },
            .{ 26, 13, 2, 0 },
            .{ 14, 13, 1, 1 },
            .{ 13, 13, 1, 0 },
            .{ 12, 13, 0, 12 },
            .{ 1, 13, 0, 1 },
            .{ 10, 1, 10, 0 },
            .{ 8, 3, 2, 2 },
            .{ 500721, 5, 100144, 1 },
            .{ 4758402376589578934275873583589345, 43950384634609, 108267593472721187331, 12368508650766 },
        },
    ) |r| {
        // Create big integers from the test case values.
        const a = bigInt(4).fromInt(u256, r[0]);
        const b = bigInt(4).fromInt(u256, r[1]);
        const c = bigInt(4).fromInt(u256, r[2]);
        const d = bigInt(4).fromInt(u256, r[3]);

        // Verify that the division with remainder operation works correctly for predefined test cases.
        try expectEqual(
            @as(std.meta.Tuple(&.{ bigInt(4), bigInt(4) }), .{ c, d }),
            a.divRem(&b),
        );

        // Verify the remainder.
        try expectEqual(d, a.rem(&b));
    }

    // Test case: Verify division with remainder operation for large integers.
    const a = bigInt(4).fromInt(u256, 12678920202929299999999999282828);
    const b = bigInt(4).fromInt(u256, 9000000000000);

    // Verify that the division with remainder operation works correctly for large integers.
    try expectEqual(
        @as(
            std.meta.Tuple(&.{ bigInt(4), bigInt(4) }),
            .{ a, .{} },
        ),
        a.mulLow(&b).divRem(&b),
    );
}

test "bigInt: fuzzing test for shift operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Define a constant zero big integer.
    const zero = comptime bigInt(4){};

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate random big integers of different sizes.
        const a = bigInt(4).rand(random);
        const b = bigInt(4).rand(random);
        const c = bigInt(4).rand(random);

        // Initialize variables to hold the expected results after shifting.
        var a_mul_expected = a;
        var b_mul_expected = b;
        var c_mul_expected = c;

        var a_div_expected = a;
        var b_div_expected = b;
        var c_div_expected = c;

        // Perform multiple left shifts and right shifts on each big integer to compute the expected results.
        inline for (0..5) |_| {
            _ = a_mul_expected.mul2Assign();
            _ = b_mul_expected.mul2Assign();
            _ = c_mul_expected.mul2Assign();

            _ = a_div_expected.div2Assign();
            _ = b_div_expected.div2Assign();
            _ = c_div_expected.div2Assign();
        }

        // Assert that the result of shifting each big integer by 5 bits to the left is equal to the expected result after multiple left shifts.
        try expect(a.shl(5).eql(a_mul_expected));
        try expect(b.shl(5).eql(b_mul_expected));
        try expect(c.shl(5).eql(c_mul_expected));
        // Assert that shifting a big integer by an excessive number of bits results in zero.
        try expect(a.shl(6 * 64).eql(zero));

        // Assert that the result of shifting each big integer by 5 bits to the right is equal to the expected result after multiple right shifts.
        try expect(a.shr(5).eql(a_div_expected));
        try expect(b.shr(5).eql(b_div_expected));
        try expect(c.shr(5).eql(c_div_expected));
        // Assert that shifting a big integer by an excessive number of bits results in zero.
        try expect(c.shr(6 * 64).eql(zero));
    }
}

test "bigInt: fuzzing test for bits operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        // Generate random big integers of different sizes.
        const a = bigInt(4).rand(random);
        // Compute a new big integer by performing a logical right shift operation on `a` by 3 bits and assign it to `b`.
        const b = a.shr(3);

        // Test null bits of `b` to ensure the correctness of the logical right shift operation.
        try expect(!b.getBit(4 * 64 - 1));
        try expect(!b.getBit(4 * 64 - 2));
        try expect(!b.getBit(4 * 64 - 3));

        // Bitwise OR operation
        try expect(a.bitOr(&a).eql(a));
        try expect(a.bitOr(&b).bitOr(&b).eql(a.bitOr(&b)));

        // Bitwise XOR operation
        const xor = a.bitXor(&b);
        inline for (0..4) |i| try expect(xor.limbs[i] == a.limbs[i] ^ b.limbs[i]);

        // Bitwise AND operation
        try expect(a.bitAnd(&a).eql(a));
        try expect(a.bitAnd(&b).bitAnd(&b).eql(a.bitAnd(&b)));

        // From/to bits operations
        try expect(bigInt(4).fromBitsLe(a.toBitsLe()).eql(a));
        try expect(bigInt(4).fromBitsBe(a.toBitsBe()).eql(a));
    }

    // Define a constant `one` representing a big integer with the value 1.
    const one = comptime bigInt(4).one();
    // Test the bits of `one` to verify the bit representation of the value 1.
    // - The 0th bit of BigInteger representing 1 is 1
    try expect(one.getBit(0));
    // - The 1st bit of BigInteger representing 1 is not 1
    try expect(!one.getBit(1));

    // Define a constant `thirty_two` representing a big integer with the value 32, obtained by shifting `one` by 5 bits to the left.
    const thirty_two = one.shl(5);
    // Test the bits of `thirty_two` to verify the bit representation of the value 32.
    // - The 0th bit of BigInteger representing 32 is not 1
    try expect(!thirty_two.getBit(0));
    // - The 1st bit of BigInteger representing 32 is not 1
    try expect(!thirty_two.getBit(1));
    // - The 2nd bit of BigInteger representing 32 is not 1
    try expect(!thirty_two.getBit(2));
    // - The 3rd bit of BigInteger representing 32 is not 1
    try expect(!thirty_two.getBit(3));
    // - The 4th bit of BigInteger representing 32 is not 1
    try expect(!thirty_two.getBit(4));
    // - The 5th bit of BigInteger representing 32 is 1
    try expect(thirty_two.getBit(5));

    // Define a constant `zero` representing a big integer with the value 0.
    const zero = comptime bigInt(4){};

    // Test the number of bits needed to represent some big integers
    try expectEqual(@as(usize, 0), zero.numBitsLe());
    try expectEqual(@as(usize, 65), bigInt(4).init(.{ 0b0, 0b1, 0, 0 }).numBitsLe());
    try expectEqual(@as(usize, 64 + 3), bigInt(4).init(.{ 0b0, 0b111, 0, 0 }).numBitsLe());
    try expectEqual(
        @as(usize, 128),
        bigInt(4).init(.{ std.math.maxInt(u64), std.math.maxInt(u64), 0, 0 }).numBitsLe(),
    );
    try expectEqual(@bitSizeOf(u256), bigInt(4).max().numBitsLe());

    // Test to obtain big integer from bit array in little endian order
    var bits_array_one_le = [_]bool{false} ** (@bitSizeOf(u256));
    bits_array_one_le[0] = true;
    try expect(bigInt(4).fromBitsLe(bits_array_one_le).eql(one));
    try expect(bigInt(4).fromBitsLe([_]bool{true} ** (@bitSizeOf(u256))).eql(bigInt(4).max()));
    try expect(bigInt(4).fromBitsLe([_]bool{false} ** (@bitSizeOf(u256))).eql(zero));

    // Test to obtain big integer from bit array in big endian order
    var bits_array_one_be = [_]bool{false} ** (@bitSizeOf(u256));
    bits_array_one_be[@bitSizeOf(u256) - 1] = true;
    try expect(bigInt(4).fromBitsBe(bits_array_one_be).eql(one));
    var bits_array_max = [_]bool{false} ** (@bitSizeOf(u256));
    bits_array_max[0] = true;
    try expect(bigInt(4).fromBitsBe(bits_array_max).mul2()[0].eql(zero));
    try expect(bigInt(4).fromBitsBe([_]bool{true} ** (@bitSizeOf(u256))).eql(bigInt(4).max()));
    try expect(bigInt(4).fromBitsBe([_]bool{false} ** (@bitSizeOf(u256))).eql(zero));
}

test "bigInt: mulMod operations" {
    // Initialize a pseudo-random number generator (PRNG) with a seed of 0.
    var prng = std.Random.DefaultPrng.init(0);
    // Generate a random number using the PRNG.
    const random = prng.random();

    const p: u256 = 0x61daf9a1ad4fd3345c3816c1d45c7eb10556c81331ad3d612bdd8fb9d8d8dd79;
    const p_big_int = comptime bigInt(4).fromInt(u256, p);

    // Iterate over the test iterations.
    for (0..TEST_ITERATIONS) |_| {
        const a = random.int(u256);
        const b = random.int(u256);

        const a_big_int = bigInt(4).fromInt(u256, a);
        const b_big_int = bigInt(4).fromInt(u256, b);

        try expectEqual(
            @mod(@as(u512, a) * @as(u512, b), p),
            a_big_int.mulMod(&b_big_int, &p_big_int).toU256(),
        );
    }
}
