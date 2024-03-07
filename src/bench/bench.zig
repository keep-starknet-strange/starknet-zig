const std = @import("std");
const Decl = std.builtin.Type.Declaration;

// Inspired by the following work: https://github.com/Hejsil/zig-bench

pub fn benchmark(comptime B: type) !void {
    const args = if (@hasDecl(B, "args")) B.args else [_]void{{}};
    const arg_names = if (@hasDecl(B, "arg_names")) B.arg_names else [_]u8{};
    const iterations = if (@hasDecl(B, "iterations")) B.iterations else 100000;

    const functions = comptime blk: {
        var res: []const Decl = &[_]Decl{};
        for (std.meta.declarations(B)) |decl| {
            if (@typeInfo(@TypeOf(@field(B, decl.name))) == .Fn)
                res = res ++ [_]Decl{decl};
        }

        break :blk res;
    };
    if (functions.len == 0)
        @compileError("No benchmarks to run.");

    const min_width = blk: {
        const writer = std.io.null_writer;
        var res = [_]u64{ 0, 0, 0, 0, 0, 0 };
        res = try printBenchmark(
            writer,
            res,
            "Benchmark",
            formatter("{s}", ""),
            formatter("{s}", "Iterations"),
            formatter("{s}", "Min(ns)"),
            formatter("{s}", "Max(ns)"),
            formatter("{s}", "Variance"),
            formatter("{s}", "Mean(ns)"),
        );
        inline for (functions) |f| {
            var i: usize = 0;
            while (i < args.len) : (i += 1) {
                res = if (i < arg_names.len)
                    try printBenchmark(
                        writer,
                        res,
                        f.name,
                        formatter("{s}", arg_names[i]),
                        std.math.maxInt(u32),
                        std.math.maxInt(u32),
                        std.math.maxInt(u32),
                        std.math.maxInt(u32),
                        std.math.maxInt(u32),
                    )
                else
                    try printBenchmark(
                        writer,
                        res,
                        f.name,
                        i,
                        std.math.maxInt(u32),
                        std.math.maxInt(u32),
                        std.math.maxInt(u32),
                        std.math.maxInt(u32),
                        std.math.maxInt(u32),
                    );
            }
        }
        break :blk res;
    };

    var _stderr = std.io.bufferedWriter(std.io.getStdErr().writer());
    const stderr = _stderr.writer();
    try stderr.writeAll("\n");
    _ = try printBenchmark(
        stderr,
        min_width,
        "Benchmark",
        formatter("{s}", ""),
        formatter("{s}", "Iterations"),
        formatter("{s}", "Min(ns)"),
        formatter("{s}", "Max(ns)"),
        formatter("{s}", "Variance"),
        formatter("{s}", "Mean(ns)"),
    );
    try stderr.writeAll("\n");
    for (min_width) |w|
        try stderr.writeByteNTimes('-', w);
    try stderr.writeByteNTimes('-', min_width.len - 1);
    try stderr.writeAll("\n");
    try stderr.context.flush();

    var timer = try std.time.Timer.start();
    inline for (functions) |def| {
        inline for (args, 0..) |arg, index| {
            timer.reset();

            for (0..iterations) |_| {
                _ = switch (@TypeOf(arg)) {
                    void => @field(B, def.name)(),
                    else => @field(B, def.name)(arg),
                };
            }

            const runtime_mean: f64 = @as(f64, @floatFromInt(timer.read())) / @as(f64, @floatFromInt(iterations));
            const variance = 0;

            if (index < arg_names.len) {
                const arg_name = formatter("{s}", arg_names[index]);
                _ = try printBenchmark(stderr, min_width, def.name, arg_name, iterations, 0, 0, variance, runtime_mean);
            } else {
                _ = try printBenchmark(stderr, min_width, def.name, index, iterations, 0, 0, variance, runtime_mean);
            }
            try stderr.writeAll("\n");
            try stderr.context.flush();
        }
    }
}

fn printBenchmark(
    writer: anytype,
    min_widths: [6]u64,
    func_name: []const u8,
    arg_name: anytype,
    iterations: anytype,
    min_runtime: anytype,
    max_runtime: anytype,
    variance: anytype,
    mean_runtime: anytype,
) ![6]u64 {
    const arg_len = std.fmt.count("{}", .{arg_name});
    const name_len = try alignedPrint(
        writer,
        .left,
        min_widths[0],
        "{s}{s}{}{s}",
        .{
            func_name,
            "("[0..@intFromBool(arg_len != 0)],
            arg_name,
            ")"[0..@intFromBool(arg_len != 0)],
        },
    );
    try writer.writeAll(" ");
    const it_len = try alignedPrint(writer, .right, min_widths[1], "{}", .{iterations});
    try writer.writeAll(" ");
    const min_runtime_len = try alignedPrint(writer, .right, min_widths[2], "{}", .{min_runtime});
    try writer.writeAll(" ");
    const max_runtime_len = try alignedPrint(writer, .right, min_widths[3], "{}", .{max_runtime});
    try writer.writeAll(" ");
    const variance_len = try alignedPrint(writer, .right, min_widths[4], "{}", .{variance});
    try writer.writeAll(" ");
    const mean_runtime_len = try alignedPrint(writer, .right, min_widths[5], "{}", .{mean_runtime});

    return [_]u64{
        name_len,
        it_len,
        min_runtime_len,
        max_runtime_len,
        variance_len,
        mean_runtime_len,
    };
}

fn formatter(comptime fmt_str: []const u8, value: anytype) Formatter(fmt_str, @TypeOf(value)) {
    return .{ .value = value };
}

fn Formatter(comptime fmt_str: []const u8, comptime T: type) type {
    return struct {
        value: T,

        pub fn format(
            self: @This(),
            comptime fmt: []const u8,
            options: std.fmt.FormatOptions,
            writer: anytype,
        ) !void {
            _ = fmt;
            _ = options;
            try std.fmt.format(writer, fmt_str, .{self.value});
        }
    };
}

fn alignedPrint(writer: anytype, dir: enum { left, right }, width: u64, comptime fmt: []const u8, args: anytype) !u64 {
    const value_len = std.fmt.count(fmt, args);

    var cow = std.io.countingWriter(writer);
    if (dir == .right)
        try cow.writer().writeByteNTimes(' ', std.math.sub(u64, width, value_len) catch 0);
    try cow.writer().print(fmt, args);
    if (dir == .left)
        try cow.writer().writeByteNTimes(' ', std.math.sub(u64, width, value_len) catch 0);
    return cow.bytes_written;
}
