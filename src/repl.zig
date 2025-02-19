const std = @import("std");
const File = std.fs.File;
const ArrayList = std.ArrayList;
const Allocator = std.mem.Allocator;
const bog = @import("bog.zig");
const Vm = bog.Vm;
const Errors = bog.Errors;
const linenoise = @import("linenoise");
const builtin = @import("builtin");

pub fn run(gpa: Allocator, in: File, out: File) !void {
    var repl: Repl = undefined;
    try repl.init(gpa);
    defer repl.deinit();

    const writer = out.writer();

    repl.vm.gc.stack_protect_start = @frameAddress();

    const frame_val = try repl.vm.gc.alloc(.frame);
    frame_val.* = .{ .frame = &repl.frame };
    defer frame_val.* = .{ .int = 0 }; // clear frame

    while (true) {
        defer {
            repl.arena.deinit();
            repl.arena = std.heap.ArenaAllocator.init(gpa);
        }
        repl.handleLine(in, out) catch |err| switch (err) {
            error.EndOfStream => return,
            error.TokenizeError, error.ParseError, error.CompileError => try repl.vm.errors.render(writer),
            error.FatalError => {
                repl.frame.stack.items[0] = bog.Value.Null;
                try repl.vm.errors.render(writer);
            },
            else => |e| return e,
        };
    }
}

pub const Repl = struct {
    buffer: ArrayList(u8),
    ln: linenoise.Linenoise,
    tokenizer: bog.Tokenizer,
    parser: bog.Parser,
    tree: bog.Tree,
    compiler: bog.Compiler,
    bytecode: bog.Bytecode,
    code: bog.Compiler.Code,
    arena: std.heap.ArenaAllocator,
    vm: Vm,
    frame: Vm.Frame,

    const tokenize = @import("tokenizer.zig").tokenizeRepl;
    const parse = @import("parser.zig").parseRepl;
    const compile = @import("Compiler.zig").compileRepl;

    fn init(repl: *Repl, gpa: Allocator) !void {
        repl.buffer = try ArrayList(u8).initCapacity(gpa, std.heap.pageSize());
        errdefer repl.buffer.deinit();

        if (builtin.os.tag != .windows) {
            repl.ln = linenoise.Linenoise.init(gpa);
        }

        repl.tokenizer = .{
            .errors = &repl.vm.errors,
            .path = "<stdin>",
            .it = .{
                .i = 0,
                .bytes = "",
            },
            .repl = true,
        };

        repl.parser = .{
            .errors = &repl.vm.errors,
            .source = "",
            .path = "<stdin>",
            .tok_ids = &.{},
            .tok_starts = &.{},
            .extra = std.ArrayList(bog.Node.Index).init(gpa),
            .node_buf = std.ArrayList(bog.Node.Index).init(gpa),
            .repl = true,
        };

        repl.compiler = bog.Compiler{
            .tree = &repl.tree,
            .errors = &repl.vm.errors,
            .gpa = gpa,
            .arena = repl.arena.allocator(),
            .code = &repl.code,
            .params = 1, // ans
        };
        errdefer repl.compiler.deinit();

        try repl.compiler.scopes.append(gpa, .{
            .symbol = .{
                .name = "ans",
                .ref = @enumFromInt(0),
                .mut = false,
                .val = undefined,
            },
        });
        try repl.compiler.globals.append(gpa, .{
            .name = "ans",
            .ref = @enumFromInt(0),
            .mut = false,
            .val = undefined,
        });
        repl.code = .{};
        // repl.bytecode is initialized by compileRepl

        repl.arena = std.heap.ArenaAllocator.init(gpa);
        errdefer repl.arena.deinit();

        repl.vm = Vm.init(gpa, .{ .repl = true, .import_files = true });
        errdefer repl.vm.deinit();
        try repl.vm.addStd();

        repl.frame = .{
            .this = bog.Value.Null,
            .mod = &repl.bytecode,
            .body = &.{},
            .caller_frame = null,
            .module_frame = undefined,
            .captures = &.{},
            .params = 1,
        };
        errdefer repl.frame.deinit(&repl.vm);
        repl.frame.module_frame = &repl.frame;

        try repl.frame.stack.append(gpa, bog.Value.Null);
    }

    fn deinit(repl: *Repl) void {
        const gpa = repl.vm.gc.gpa;
        repl.buffer.deinit();
        repl.ln.deinit();
        repl.tokenizer.tokens.deinit(gpa);
        repl.parser.node_buf.deinit();
        repl.parser.extra.deinit();
        repl.parser.nodes.deinit(gpa);
        repl.compiler.deinit();
        repl.code.deinit(gpa);
        repl.arena.deinit();
        repl.frame.deinit(&repl.vm);
        repl.vm.deinit();
        repl.* = undefined;
    }

    fn handleLine(repl: *Repl, in: File, out: File) !void {
        const buffer_start = repl.buffer.items.len;
        errdefer |e| if (e == error.CompileError) {
            repl.buffer.shrinkAndFree(buffer_start);
        };

        try repl.readLine(in, out, ">>> ");
        const node = while (true) {
            if (try repl.tokenize()) {
                if (repl.parse()) |some| {
                    break some orelse return;
                } else |err| switch (err) {
                    error.NeedInput => {},
                    else => |e| return @as(@TypeOf(e)!void, e),
                }
            }

            try repl.readLine(in, out, "... ");
        } else unreachable;
        try repl.compile(node);

        const res = try repl.vm.run(&repl.frame);
        repl.frame.stack.items[0] = res;
        if (res == bog.Value.Null) return;

        const writer = out.writer();
        try res.dump(writer, 2);
        try writer.writeByte('\n');
    }

    fn readLine(repl: *Repl, in: File, out: File, prompt: []const u8) !void {
        _ = in;
        _ = out;
        if (repl.ln.linenoise(prompt)) |maybe_line| {
            const line = maybe_line orelse return error.EndOfStream;
            defer repl.ln.allocator.free(line);

            try repl.buffer.appendSlice(line);
            try repl.buffer.append('\n');

            try repl.ln.history.add(line);
        } else |err| {
            switch (err) {
                error.CtrlC => return error.EndOfStream,
                else => |e| return e,
            }
        }
    }
};
