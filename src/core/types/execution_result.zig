const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const expectError = std.testing.expectError;

const TransactionExecutionStatus = enum { Succeeded, Reverted };

pub const ExecutionResult = union(TransactionExecutionStatus) {
    const Self = @This();

    Succeeded,
    Reverted: struct { reason: []const u8 },

    pub fn status(self: *Self) TransactionExecutionStatus {
        return switch (self.*) {
            .Succeeded => TransactionExecutionStatus.Succeeded,
            .Reverted => TransactionExecutionStatus.Reverted,
        };
    }

    pub fn revertReason(self: *Self) ?[]const u8 {
        return switch (self.*) {
            .Succeeded => null,
            .Reverted => |rev| rev.reason,
        };
    }
};
