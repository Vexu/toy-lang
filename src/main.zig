const std = @import("std");
const process = std.process;
const mem = std.mem;
const bog = @import("bog");
const repl = bog.repl;

const is_debug = @import("builtin").mode == .Debug;
var state = std.heap.GeneralPurposeAllocator(.{}){};

pub fn main() !void {
    const gpa = state.allocator();

    const args = try process.argsAlloc(gpa);
    defer process.argsFree(gpa, args);

    if (args.len > 1) {
        if (mem.eql(u8, args[1], "fmt")) {
            return fmt(gpa, args[2..]);
        }
        if (mem.eql(u8, args[1], "help") or mem.eql(u8, args[1], "--help")) {
            return help();
        }
        if (is_debug) {
            if (mem.eql(u8, args[1], "debug:dump")) {
                return debugDump(gpa, args[2..]);
            }
            if (mem.eql(u8, args[1], "debug:tokens")) {
                return debugTokens(gpa, args[2..]);
            }
        }
        if (!mem.startsWith(u8, "-", args[1])) {
            return run(gpa, args[1..]);
        }
    }

    try repl.run(gpa, std.io.getStdIn(), std.io.getStdOut());
}

const usage =
    \\usage: bog [command] [options] [-- [args]]
    \\
    \\Commands:
    \\
    \\  fmt        [source]      Parse file and render it
    \\  run        [source]      Run file
    \\
    \\
;

fn help() !void {
    try std.io.getStdOut().writer().writeAll(usage);
    process.exit(0);
}

fn run(gpa: std.mem.Allocator, args: []const []const u8) !void {
    std.debug.assert(args.len > 0);
    const file_name = args[0];

    var vm = bog.Vm.init(gpa, .{ .import_files = true });
    defer vm.deinit();
    try vm.addStd();
    const S = struct {
        var _args: []const []const u8 = undefined;

        fn argsToBog(ctx: bog.Vm.Context) bog.Vm.Error!*bog.Value {
            const ret = try ctx.vm.gc.alloc(.list);
            ret.* = .{ .list = .{} };
            try ret.list.inner.ensureTotalCapacity(ctx.vm.gc.gpa, _args.len);

            for (_args) |arg| {
                const str = try ctx.vm.gc.alloc(.str);
                str.* = bog.Value.string(arg);
                ret.list.inner.appendAssumeCapacity(str);
            }
            return ret;
        }
    };
    S._args = args[0..];
    try vm.imports.putNoClobber(vm.gc.gpa, "args", S.argsToBog);

    const res = vm.compileAndRun(file_name) catch |e| switch (e) {
        error.FatalError, error.TokenizeError, error.ParseError, error.CompileError => {
            vm.errors.render(std.io.getStdErr().writer()) catch {};
            process.exit(1);
        },
        error.OutOfMemory => return error.OutOfMemory,
        else => {
            fatal("cannot run '{s}': {s}", .{ file_name, @errorName(e) });
        },
    };

    switch (res.*) {
        .int => |int| {
            if (int >= 0 and int < std.math.maxInt(u8)) {
                process.exit(@intCast(int));
            } else {
                fatal("invalid exit code: {}", .{int});
            }
        },
        .err => |err| {
            const stderr = std.io.getStdErr().writer();
            try stderr.writeAll("script exited with error: ");
            try err.dump(stderr, 4);
            try stderr.writeAll("\n");
            process.exit(1);
        },
        .null => {},
        else => fatal("invalid return type '{s}'", .{res.typeName()}),
    }
}

const usage_fmt =
    \\usage: bog fmt [file]...
    \\
    \\   Formats the input files.
    \\
;

fn fmt(gpa: std.mem.Allocator, args: []const []const u8) !void {
    if (args.len == 0) fatal("expected at least one file", .{});

    var any_err = false;
    for (args) |arg| {
        any_err = (try fmtFile(gpa, arg)) or any_err;
    }
    if (any_err) process.exit(1);
}

const FmtError = std.mem.Allocator.Error || std.fs.File.OpenError || std.fs.File.Writer.Error ||
    std.fs.Dir.OpenError || std.fs.File.GetSeekPosError || std.fs.Dir.Iterator.Error ||
    std.fs.File.Reader.Error || error{EndOfStream};

fn fmtFile(gpa: std.mem.Allocator, name: []const u8) FmtError!bool {
    const source = std.fs.cwd().readFileAlloc(gpa, name, 1024 * 1024) catch |e| switch (e) {
        error.OutOfMemory => return error.OutOfMemory,
        error.IsDir => {
            var dir = std.fs.cwd().openDir(name, .{ .iterate = true }) catch |e2| {
                try std.io.getStdErr().writer().print("unable to open '{s}': {}\n", .{ name, e2 });
                return e2;
            };
            var any_err = false;
            defer dir.close();
            var it = dir.iterate();
            while (try it.next()) |entry| if (entry.kind == .directory or std.mem.endsWith(u8, entry.name, bog.extension)) {
                const full_path = try std.fs.path.join(gpa, &[_][]const u8{ name, entry.name });
                defer gpa.free(full_path);
                any_err = (try fmtFile(gpa, full_path)) or any_err;
            };
            return any_err;
        },
        else => |err| {
            try std.io.getStdErr().writer().print("unable to open '{s}': {}\n", .{ name, err });
            return err;
        },
    };
    defer gpa.free(source);

    var errors = bog.Errors.init(gpa);
    defer errors.deinit();

    var tree = bog.parse(gpa, source, name, &errors) catch |e| switch (e) {
        error.NeedInput => unreachable,
        error.TokenizeError, error.ParseError => {
            try errors.render(std.io.getStdErr().writer());
            return true;
        },
        error.OutOfMemory => return error.OutOfMemory,
    };
    defer tree.deinit(gpa);

    var buf = std.ArrayList(u8).init(gpa);
    defer buf.deinit();

    // TODO add check mode
    _ = try tree.render(buf.writer());

    const file = try std.fs.cwd().createFile(name, .{});
    defer file.close();

    try file.writeAll(buf.items);
    return false;
}

fn fatal(comptime msg: []const u8, args: anytype) noreturn {
    std.io.getStdErr().writer().print(msg ++ "\n", args) catch {};
    process.exit(1);
}

fn getFileName(usage_arg: []const u8, args: []const []const u8) []const u8 {
    if (args.len != 1) {
        fatal("{s}", .{usage_arg});
    }
    return args[0];
}

const usage_debug =
    \\usage: bog debug:[command] [file]
    \\
;

fn debugDump(gpa: std.mem.Allocator, args: []const []const u8) !void {
    const file_name = getFileName(usage_debug, args);

    var errors = bog.Errors.init(gpa);
    defer errors.deinit();
    var mod = mod: {
        const source = std.fs.cwd().readFileAlloc(gpa, file_name, 1024 * 1024) catch |e| switch (e) {
            error.OutOfMemory => return error.OutOfMemory,
            else => |err| {
                fatal("unable to open '{s}': {}", .{ file_name, err });
            },
        };
        errdefer gpa.free(source);

        break :mod bog.compile(gpa, source, file_name, &errors) catch |e| switch (e) {
            error.OutOfMemory => return error.OutOfMemory,
            error.TokenizeError, error.ParseError, error.CompileError => {
                try errors.render(std.io.getStdErr().writer());
                process.exit(1);
            },
        };
    };
    defer mod.deinit(gpa);

    mod.dump(mod.main, 0);
}

fn debugTokens(gpa: std.mem.Allocator, args: []const []const u8) !void {
    const file_name = getFileName(usage_debug, args);

    const source = std.fs.cwd().readFileAlloc(gpa, file_name, 1024 * 1024) catch |e| switch (e) {
        error.OutOfMemory => return error.OutOfMemory,
        else => |err| {
            fatal("unable to open '{s}': {}", .{ file_name, err });
        },
    };
    defer gpa.free(source);

    var errors = bog.Errors.init(gpa);
    defer errors.deinit();

    var tokens = bog.tokenize(gpa, source, file_name, &errors) catch |e| switch (e) {
        error.OutOfMemory => return error.OutOfMemory,
        error.TokenizeError => {
            try errors.render(std.io.getStdErr().writer());
            process.exit(1);
        },
    };
    defer tokens.deinit(gpa);

    const stream = std.io.getStdOut().writer();
    const starts = tokens.items(.start);
    const ends = tokens.items(.end);
    for (tokens.items(.id), 0..) |id, i| {
        switch (id) {
            .nl,
            .eof,
            // zig fmt: off
            .indent_1, .indent_2, .indent_3, .indent_4, .indent_5,
            .indent_6, .indent_7, .indent_8, .indent_9, .indent_10,
            .indent_11, .indent_12, .indent_13, .indent_14, .indent_15,
            .indent_16, .indent_17, .indent_18, .indent_19, .indent_20,
            .indent_21, .indent_22, .indent_23, .indent_24, .indent_25,
            .indent_26, .indent_27, .indent_28, .indent_29, .indent_30,
            .indent_31, .indent_32,
            // zig fmt: on
            => try stream.print("{s}\n", .{@tagName(id)}),
            else => try stream.print("{s} |{s}|\n", .{ @tagName(id), source[starts[i]..ends[i]] }),
        }
    }
}

comptime {
    _ = main;
}
