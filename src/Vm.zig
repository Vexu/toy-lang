const std = @import("std");
const mem = std.mem;
const Allocator = mem.Allocator;
const bog = @import("bog.zig");
const Bytecode = bog.Bytecode;
const Value = bog.Value;
const Type = bog.Type;
const Ref = Bytecode.Ref;
const Gc = bog.Gc;
const Errors = bog.Errors;

const Vm = @This();

const max_params = @import("Compiler.zig").max_params;

gc: Gc,

errors: Errors,

/// Functions that act like modules, called by `import`ing a package by the name.
imports: std.StringHashMapUnmanaged(*const fn (Context) Value.NativeError!*Value) = .{},

/// All currently loaded packages and files.
imported_modules: std.StringHashMapUnmanaged(*Bytecode) = .{},

options: Options = .{},
/// Current call stack depth, used to prevent stack overflow.
call_depth: u32 = 0,

frame_cache: std.ArrayListUnmanaged(struct { s: Stack, e: ErrHandlers }) = .{},

const max_depth = 512;

pub const Options = struct {
    /// can files be imported
    import_files: bool = false,

    /// run vm in repl mode
    repl: bool = false,

    /// maximum size of imported files
    max_import_size: u32 = 5 * 1024 * 1024,

    /// maximum amount of pages gc may allocate.
    /// 1 page == 1 MiB.
    /// default 2 GiB.
    page_limit: u32 = 2048,
};

/// NOTE: should be ?*Value, but that makes stage1 shit its pants.
pub const Stack = std.ArrayListUnmanaged(*Value);

pub const Frame = struct {
    /// List of instructions part of this function.
    body: []const u32,
    /// Index into `body`.
    ip: u32 = 0,
    /// Number of parameters current function has. Needed to calculate
    /// a reference to instructions.
    params: u32,
    /// The module in which this function lives in.
    mod: *Bytecode,
    /// Values this function captures.
    captures: []*Value,

    /// Value of `this` as set by the caller.
    this: *Value, // = Value.Null,
    /// Frame of the function which called this, forms a call stack.
    caller_frame: ?*Frame,
    /// Frame of `mod.main`.
    module_frame: *Frame,
    /// This function frames stack.
    stack: Stack = .{},
    /// Stack of error handlers that have been set up.
    err_handlers: ErrHandlers = .{ .short = .{} },
    /// If not null then the frame has finished.
    result_val: ?*Value = null,

    pub fn deinit(f: *Frame, vm: *Vm) void {
        f.err_handlers.deinit(vm.gc.gpa);
        f.stack.deinit(vm.gc.gpa);
        f.* = undefined;
    }

    pub fn newVal(f: *Frame, vm: *Vm, ref: Ref, ty: Type) !*Value {
        const res = try f.newRef(vm, ref);
        if (res.*) |some| {
            // attempt to use old value for better performance in loops
            switch (some.*) {
                // simple values can be reused
                .int, .num, .range, .native => return some,
                // if string doesn't own it's contents it can be reused
                .str => |s| if (s.capacity == 0) return some,
                else => {},
            }
        }
        // allocate a new value if previous cannot be used or there isn't one
        res.* = try vm.gc.alloc(ty);
        return res.*.?;
    }

    pub fn newRef(f: *Frame, vm: *Vm, ref: Ref) !*?*Value {
        const ref_int = @intFromEnum(ref);
        if (ref_int < f.stack.items.len) {
            return @ptrCast(&f.stack.items[ref_int]);
        }
        try f.stack.ensureTotalCapacity(vm.gc.gpa, ref_int + 1);
        @memset(
            @as([]?*Value, @ptrCast(f.stack.items.ptr[f.stack.items.len .. ref_int + 1])),
            null,
        );
        f.stack.items.len = ref_int + 1;
        return @ptrCast(&f.stack.items[ref_int]);
    }

    pub inline fn refAssert(f: *Frame, ref: Ref) **Value {
        return &f.stack.items[@intFromEnum(ref)];
    }

    pub fn val(f: *Frame, ref: Ref) *Value {
        return f.stack.items[@intFromEnum(ref)];
    }

    pub inline fn valDupeSimple(f: *Frame, vm: *Vm, ref: Ref) !*Value {
        const old = f.val(ref);
        // do the opposite of newVal in case the value is added to an aggregate
        switch (old.*) {
            .int, .num, .range, .native => {},
            .str => |s| if (s.capacity != 0) return old,
            else => return old,
        }
        return vm.gc.dupe(old);
    }

    pub fn int(f: *Frame, vm: *Vm, ref: Ref) !?i64 {
        const res = f.val(ref);
        if (res.* != .int) {
            try f.throw(vm, "expected an integer");
            return null;
        }
        return res.int;
    }

    pub fn num(f: *Frame, vm: *Vm, ref: Ref) !?*Value {
        const res = f.val(ref);
        switch (res.*) {
            .int, .num => return res,
            else => {
                try f.throw(vm, "expected a number");
                return null;
            },
        }
    }

    pub fn @"bool"(f: *Frame, vm: *Vm, ref: Ref) !?bool {
        const res = f.val(ref);
        if (res.* != .bool) {
            try f.throw(vm, "expected a bool");
            return null;
        }
        return res.bool;
    }

    pub fn ctx(f: *Frame, vm: *Vm) Context {
        return .{ .this = Value.Null, .vm = vm, .frame = f };
    }

    pub fn ctxThis(f: *Frame, this: *Value, vm: *Vm) Context {
        return .{ .this = this, .vm = vm, .frame = f };
    }

    pub fn fatal(f: *Frame, vm: *Vm, msg: []const u8) Error {
        @branchHint(.cold);
        return f.fatalExtra(vm, .{ .data = msg }, .err);
    }

    pub fn fatalExtra(f: *Frame, vm: *Vm, msg: Value.String, kind: bog.Errors.Kind) Error {
        @branchHint(.cold);

        const byte_offset = f.mod.debug_info.lines.get(f.body[f.ip - 1]).?;
        try vm.errors.add(msg, f.mod.debug_info.source, f.mod.debug_info.path, byte_offset, kind);
        if (f.caller_frame) |some| return some.fatalExtra(vm, .{ .data = "called here" }, .trace);
        return error.FatalError;
    }

    pub fn throw(f: *Frame, vm: *Vm, err: []const u8) !void {
        if (f.err_handlers.get()) |handler| {
            const handler_operand = try f.newRef(vm, handler.operand);
            handler_operand.* = try vm.errorVal(err);
            f.ip = handler.offset;
        } else {
            return f.fatal(vm, err);
        }
    }

    pub fn throwFmt(f: *Frame, vm: *Vm, comptime err: []const u8, args: anytype) !void {
        if (f.err_handlers.get()) |handler| {
            const handler_operand = try f.newRef(vm, handler.operand);
            handler_operand.* = try vm.errorFmt(err, args);
            f.ip = handler.offset;
        } else {
            const str = try Value.String.init(vm.gc.gpa, err, args);
            return f.fatalExtra(vm, str, .err);
        }
    }
};

pub const Context = struct {
    this: *Value, // = Value.Null,
    vm: *Vm,
    frame: *Vm.Frame,

    pub fn throw(ctx: Context, err: []const u8) Value.NativeError {
        try ctx.frame.throw(ctx.vm, err);
        return error.Throw;
    }

    pub fn throwFmt(ctx: Context, comptime err: []const u8, args: anytype) Value.NativeError {
        try ctx.frame.throwFmt(ctx.vm, err, args);
        return error.Throw;
    }
};

pub const Error = error{FatalError} || Allocator.Error;

pub fn init(allocator: Allocator, options: Options) Vm {
    return .{
        .gc = Gc.init(allocator, options.page_limit),
        .errors = Errors.init(allocator),
        .options = options,
    };
}

pub fn deinit(vm: *Vm) void {
    vm.errors.deinit();
    vm.gc.deinit();
    vm.imports.deinit(vm.gc.gpa);
    var it = vm.imported_modules.iterator();
    while (it.next()) |mod| {
        mod.value_ptr.*.deinit(vm.gc.gpa);
    }
    vm.imported_modules.deinit(vm.gc.gpa);
    for (vm.frame_cache.items) |*c| {
        c.s.deinit(vm.gc.gpa);
        c.e.deinit(vm.gc.gpa);
    }
    vm.frame_cache.deinit(vm.gc.gpa);
    vm.* = undefined;
}

// TODO we might not want to require `importable` to be comptime
pub fn addPackage(vm: *Vm, name: []const u8, comptime importable: anytype) Allocator.Error!void {
    try vm.imports.putNoClobber(vm.gc.gpa, name, struct {
        fn func(ctx: Context) Vm.Error!*bog.Value {
            if (@typeInfo(@TypeOf(importable)) == .@"fn") {
                return bog.Value.zigFnToBog(ctx.vm, importable);
            }
            return bog.Value.zigToBog(ctx.vm, importable);
        }
    }.func);
}

pub fn addStd(vm: *Vm) Allocator.Error!void {
    try vm.addStdNoIo();
    try vm.addPackage("std.io", bog.std.io);
    try vm.addPackage("std.fs", bog.std.fs);
    try vm.addPackage("std.os", bog.std.os);
}

pub fn addStdNoIo(vm: *Vm) Allocator.Error!void {
    try vm.addPackage("std.math", bog.std.math);
    try vm.addPackage("std.map", bog.std.map);
    try vm.addPackage("std.debug", bog.std.debug);
    try vm.addPackage("std.json", bog.std.json);
    try vm.addPackage("std.gc", bog.std.gc);
}

/// Compiles and executes the file given by `file_path`.
pub fn compileAndRun(vm: *Vm, file_path: []const u8) !*Value {
    const mod = vm.importFile(file_path) catch |err| switch (err) {
        error.ImportingDisabled => unreachable,
        else => |e| return e,
    };

    var frame = Frame{
        .this = Value.Null,
        .mod = mod,
        .body = mod.main,
        .caller_frame = null,
        .module_frame = undefined,
        .captures = &.{},
        .params = 0,
    };
    defer frame.deinit(vm);
    frame.module_frame = &frame;

    vm.gc.stack_protect_start = @frameAddress();

    const frame_val = try vm.gc.alloc(.frame);
    frame_val.* = .{ .frame = &frame };
    defer frame_val.* = .{ .int = 0 }; // clear frame

    return vm.run(&frame) catch |err| switch (err) {
        error.Suspended => return frame.fatal(vm, "TODO main function suspended"),
        else => |e| return e,
    };
}

/// Continues execution from current instruction pointer.
pub fn run(vm: *Vm, f: *Frame) (Error || error{Suspended})!*Value {
    const mod = f.mod;
    const body = f.body;
    const ops = mod.code.items(.op);
    const data = mod.code.items(.data);

    while (true) {
        const inst = body[f.ip];
        const ref = Bytecode.indexToRef(f.ip, f.params);
        f.ip += 1;
        switch (ops[inst]) {
            .nop => continue,
            .primitive => {
                const res = try f.newRef(vm, ref);
                res.* = switch (data[inst].primitive) {
                    .null => Value.Null,
                    .true => Value.True,
                    .false => Value.False,
                };
            },
            .int => {
                const res = try f.newVal(vm, ref, .int);

                res.* = .{ .int = data[inst].int };
            },
            .num => {
                const res = try f.newVal(vm, ref, .num);

                res.* = .{ .num = data[inst].num };
            },
            .str => {
                const res = try f.newVal(vm, ref, .str);

                const str = mod.strings[data[inst].str.offset..][0..data[inst].str.len];
                res.* = Value.string(str);
            },
            .build_tuple => {
                const items = mod.extra[data[inst].extra.extra..][0..data[inst].extra.len];

                var len: usize = 0;
                for (items) |item_ref| {
                    switch (f.val(item_ref).*) {
                        .spread => |spread| len += spread.len(),
                        else => len += 1,
                    }
                }
                const res = try f.newVal(vm, ref, .tuple);
                res.* = .{ .tuple = try vm.gc.gpa.alloc(*Value, len) };

                var i: usize = 0;
                for (items) |item_ref| {
                    const val = try f.valDupeSimple(vm, item_ref);
                    switch (val.*) {
                        .spread => |spread| {
                            const spread_items = spread.items();
                            for (spread_items) |item| {
                                res.tuple[i] = item;
                                i += 1;
                            }
                        },
                        else => {
                            res.tuple[i] = val;
                            i += 1;
                        },
                    }
                }
            },
            .build_list => {
                const items = mod.extra[data[inst].extra.extra..][0..data[inst].extra.len];

                var len: usize = 0;
                for (items) |item_ref| {
                    switch (f.val(item_ref).*) {
                        .spread => |spread| len += spread.len(),
                        else => len += 1,
                    }
                }

                const res = try f.newVal(vm, ref, .list);
                res.* = .{ .list = .{} };
                try res.list.inner.ensureUnusedCapacity(vm.gc.gpa, len);

                for (items) |item_ref| {
                    const val = try f.valDupeSimple(vm, item_ref);
                    switch (val.*) {
                        .spread => |spread| res.list.inner.appendSliceAssumeCapacity(spread.items()),
                        else => res.list.inner.appendAssumeCapacity(val),
                    }
                }
            },
            .build_map => {
                const items = mod.extra[data[inst].extra.extra..][0..data[inst].extra.len];

                const res = try f.newVal(vm, ref, .map);
                res.* = .{ .map = .{} };

                try res.map.ensureUnusedCapacity(vm.gc.gpa, @intCast(items.len));

                var map_i: u32 = 0;
                while (map_i < items.len) : (map_i += 2) {
                    const key = try f.valDupeSimple(vm, items[map_i]);
                    const val = try f.valDupeSimple(vm, items[map_i + 1]);
                    res.map.putAssumeCapacity(key, val);
                }
            },
            .build_error => {
                const res = try f.newVal(vm, ref, .err);
                const arg = try f.valDupeSimple(vm, data[inst].un);

                res.* = .{ .err = try vm.gc.dupe(arg) };
            },
            .build_error_null => {
                const res = try f.newVal(vm, ref, .err);
                res.* = .{ .err = Value.Null };
            },
            .build_tagged => {
                const res = try f.newVal(vm, ref, .tagged);
                const arg = try f.valDupeSimple(vm, mod.extra[data[inst].extra.extra]);
                const str_offset = @intFromEnum(mod.extra[data[inst].extra.extra + 1]);

                const name = mod.strings[str_offset..][0..data[inst].extra.len];
                res.* = .{ .tagged = .{
                    .name = name,
                    .value = try vm.gc.dupe(arg),
                } };
            },
            .build_tagged_null => {
                const res = try f.newVal(vm, ref, .tagged);

                const name = mod.strings[data[inst].str.offset..][0..data[inst].str.len];
                res.* = .{ .tagged = .{ .name = name, .value = Value.Null } };
            },
            .build_func => {
                const res = try f.newVal(vm, ref, .func);
                const extra = mod.extra[data[inst].extra.extra..][0..data[inst].extra.len];
                const captures_len = @intFromEnum(extra[1]);
                const fn_captures = extra[2..][0..captures_len];
                const fn_body = extra[captures_len + 2 ..];

                const captures = try vm.gc.gpa.alloc(*Value, captures_len);
                for (fn_captures, 0..) |capture_ref, i| {
                    // TODO should this use valDupeSimple
                    captures[i] = f.val(capture_ref);
                }

                res.* = .{
                    .func = .{
                        .module = mod,
                        .captures_ptr = captures.ptr,
                        .extra_index = data[inst].extra.extra,
                        .body_len = @intCast(fn_body.len),
                    },
                };
            },
            .build_range => {
                const start = (try f.int(vm, data[inst].bin.lhs)) orelse continue;
                const end = (try f.int(vm, data[inst].bin.rhs)) orelse continue;

                const res = try f.newVal(vm, ref, .range);
                res.* = .{
                    .range = .{
                        .start = start,
                        .end = end,
                    },
                };
            },
            .build_range_step => {
                const start = (try f.int(vm, data[inst].range.start)) orelse continue;
                const end = (try f.int(vm, mod.extra[data[inst].range.extra])) orelse continue;
                const step = (try f.int(vm, mod.extra[data[inst].range.extra + 1])) orelse continue;

                const res = try f.newVal(vm, ref, .range);
                res.* = .{
                    .range = .{
                        .start = start,
                        .end = end,
                        .step = step,
                    },
                };
            },
            .import => {
                const val = f.val(data[inst].un);
                if (val.* != .str) {
                    try f.throw(vm, "expected a string");
                    continue;
                }
                const res_val = try vm.import(f, val.str.data);

                const res = try f.newRef(vm, ref);
                res.* = res_val;
            },
            .discard => {
                const arg = f.val(data[inst].un);

                if (arg.* == .err) {
                    return f.fatal(vm, "error discarded");
                }
            },
            .copy_un => {
                const val = try f.valDupeSimple(vm, data[inst].un);

                const res = try f.newRef(vm, ref);
                res.* = val;
            },
            .copy => {
                const val = f.val(data[inst].bin.rhs);

                const duped = try vm.gc.dupe(val);

                const res = try f.newRef(vm, data[inst].bin.lhs);
                res.* = duped;
            },
            .move => {
                const val = f.val(data[inst].bin.rhs);
                const res = try f.newRef(vm, data[inst].bin.lhs);

                res.* = val;
            },
            .load_global => {
                const res = try f.newRef(vm, ref);
                const ref_int = @intFromEnum(data[inst].un);
                if (ref_int > f.module_frame.stack.items.len)
                    return f.fatal(vm, "use of undefined variable");
                res.* = f.module_frame.stack.items[ref_int];
            },
            .store_global => {
                const val = try f.valDupeSimple(vm, data[inst].bin.rhs);
                const load_inst = body[Bytecode.refToIndex(data[inst].bin.lhs, f.params)];
                const res = try f.module_frame.newRef(vm, data[load_inst].un);
                res.* = val;
            },
            .load_capture => {
                const index = @intFromEnum(data[inst].un);
                const res = try f.newRef(vm, ref);
                res.* = f.captures[index];
            },
            .load_this => {
                const res = try f.newRef(vm, ref);
                res.* = f.this;
            },
            .div_floor => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;
                if (checkZero(rhs)) {
                    try f.throw(vm, "division by zero");
                    continue;
                }

                const copy: Value = if (needNum(lhs, rhs)) .{
                    .int = std.math.lossyCast(i64, @divFloor(asNum(lhs), asNum(rhs))),
                } else .{
                    .int = std.math.divFloor(i64, lhs.int, rhs.int) catch {
                        try f.throw(vm, "operation overflowed");
                        continue;
                    },
                };
                const res = try f.newVal(vm, ref, .int);
                res.* = copy;
            },
            .div => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;
                if (checkZero(rhs)) {
                    try f.throw(vm, "division by zero");
                    continue;
                }

                const copy = Value{ .num = asNum(lhs) / asNum(rhs) };
                const res = try f.newVal(vm, ref, .num);
                res.* = copy;
            },
            .rem => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;
                if (checkZero(rhs)) {
                    try f.throw(vm, "division by zero");
                    continue;
                }
                if (isNegative(rhs)) {
                    try f.throw(vm, "remainder division by negative denominator");
                    continue;
                }

                const copy: Value = if (needNum(lhs, rhs)) .{
                    .num = @rem(asNum(lhs), asNum(rhs)),
                } else .{
                    .int = @rem(lhs.int, rhs.int),
                };
                const res = try f.newVal(vm, ref, .num);
                res.* = copy;
            },
            .mul => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;

                const copy: Value = if (needNum(lhs, rhs)) .{
                    .num = asNum(lhs) * asNum(rhs),
                } else .{
                    .int = std.math.mul(i64, lhs.int, rhs.int) catch {
                        try f.throw(vm, "operation overflowed");
                        continue;
                    },
                };
                const res = try f.newVal(vm, ref, .num);
                res.* = copy;
            },
            .pow => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;

                const copy: Value = if (needNum(lhs, rhs)) .{
                    .num = std.math.pow(f64, asNum(lhs), asNum(rhs)),
                } else .{
                    .int = std.math.powi(i64, lhs.int, rhs.int) catch {
                        try f.throw(vm, "operation overflowed");
                        continue;
                    },
                };
                const res = try f.newVal(vm, ref, .num);
                res.* = copy;
            },
            .add => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;

                const copy: Value = if (needNum(lhs, rhs)) .{
                    .num = asNum(lhs) + asNum(rhs),
                } else .{
                    .int = std.math.add(i64, lhs.int, rhs.int) catch {
                        try f.throw(vm, "operation overflowed");
                        continue;
                    },
                };
                const res = try f.newVal(vm, ref, .num);
                res.* = copy;
            },
            .sub => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;

                const copy: Value = if (needNum(lhs, rhs)) .{
                    .num = asNum(lhs) - asNum(rhs),
                } else .{
                    .int = std.math.sub(i64, lhs.int, rhs.int) catch {
                        try f.throw(vm, "operation overflowed");
                        continue;
                    },
                };
                const res = try f.newVal(vm, ref, .num);
                res.* = copy;
            },
            .l_shift => {
                const lhs = (try f.int(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.int(vm, data[inst].bin.rhs)) orelse continue;
                if (rhs < 0) {
                    try f.throw(vm, "shift by negative amount");
                    continue;
                }

                const val = if (rhs > std.math.maxInt(u6))
                    0
                else
                    lhs << @intCast(rhs);

                const res = try f.newVal(vm, ref, .int);
                res.* = .{ .int = val };
            },
            .r_shift => {
                const lhs = (try f.int(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.int(vm, data[inst].bin.rhs)) orelse continue;
                if (rhs < 0) {
                    try f.throw(vm, "shift by negative amount");
                    continue;
                }

                const val = if (rhs > std.math.maxInt(u6))
                    if (lhs < 0) std.math.maxInt(i64) else @as(i64, 0)
                else
                    lhs << @intCast(rhs);

                const res = try f.newVal(vm, ref, .int);
                res.* = .{ .int = val };
            },
            .bit_and => {
                const lhs = (try f.int(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.int(vm, data[inst].bin.rhs)) orelse continue;

                const res = try f.newVal(vm, ref, .int);
                res.* = .{ .int = lhs & rhs };
            },
            .bit_or => {
                const lhs = (try f.int(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.int(vm, data[inst].bin.rhs)) orelse continue;

                const res = try f.newVal(vm, ref, .int);
                res.* = .{ .int = lhs | rhs };
            },
            .bit_xor => {
                const lhs = (try f.int(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.int(vm, data[inst].bin.rhs)) orelse continue;

                const res = try f.newVal(vm, ref, .int);
                res.* = .{ .int = lhs ^ rhs };
            },
            .equal => {
                const res = try f.newRef(vm, ref);
                const lhs = f.val(data[inst].bin.lhs);
                const rhs = f.val(data[inst].bin.rhs);

                res.* = if (lhs.eql(rhs)) Value.True else Value.False;
            },
            .not_equal => {
                const res = try f.newRef(vm, ref);
                const lhs = f.val(data[inst].bin.lhs);
                const rhs = f.val(data[inst].bin.rhs);

                res.* = if (!lhs.eql(rhs)) Value.True else Value.False;
            },
            .less_than => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;
                const res = try f.newRef(vm, ref);

                const bool_val = if (needNum(lhs, rhs))
                    asNum(lhs) < asNum(rhs)
                else
                    lhs.int < rhs.int;

                res.* = if (bool_val) Value.True else Value.False;
            },
            .less_than_equal => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;
                const res = try f.newRef(vm, ref);

                const bool_val = if (needNum(lhs, rhs))
                    asNum(lhs) <= asNum(rhs)
                else
                    lhs.int <= rhs.int;

                res.* = if (bool_val) Value.True else Value.False;
            },
            .greater_than => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;
                const res = try f.newRef(vm, ref);

                const bool_val = if (needNum(lhs, rhs))
                    asNum(lhs) > asNum(rhs)
                else
                    lhs.int > rhs.int;

                res.* = if (bool_val) Value.True else Value.False;
            },
            .greater_than_equal => {
                const lhs = (try f.num(vm, data[inst].bin.lhs)) orelse continue;
                const rhs = (try f.num(vm, data[inst].bin.rhs)) orelse continue;
                const res = try f.newRef(vm, ref);

                const bool_val = if (needNum(lhs, rhs))
                    asNum(lhs) >= asNum(rhs)
                else
                    lhs.int >= rhs.int;

                res.* = if (bool_val) Value.True else Value.False;
            },
            .in => {
                const lhs = f.val(data[inst].bin.lhs);
                const rhs = f.val(data[inst].bin.rhs);

                switch (rhs.*) {
                    .str, .tuple, .list, .map, .range => {},
                    else => {
                        try f.throwFmt(vm, "'in' not allowed with type {s}", .{rhs.typeName()});
                        continue;
                    },
                }

                const res = try f.newRef(vm, ref);
                res.* = if (lhs.in(rhs)) Value.True else Value.False;
            },
            .append => {
                const container = f.val(data[inst].bin.lhs);
                const operand = f.val(data[inst].bin.rhs);

                try container.list.inner.append(vm.gc.gpa, try vm.gc.dupe(operand));
            },
            .as => {
                const arg = f.val(data[inst].bin_ty.operand);

                // type is validated by the compiler
                const casted = arg.as(f.ctx(vm), data[inst].bin_ty.ty) catch |err| switch (err) {
                    error.Throw => continue,
                    else => |e| return e,
                };
                const res = try f.newRef(vm, ref);
                res.* = casted;
            },
            .is => {
                const res = try f.newRef(vm, ref);
                const arg = f.val(data[inst].bin_ty.operand);

                // type is validated by the compiler
                res.* = if (arg.is(data[inst].bin_ty.ty)) Value.True else Value.False;
            },
            .negate => {
                const operand = (try f.num(vm, data[inst].un)) orelse continue;

                const copy: Value = if (operand.* == .num) .{
                    .num = -operand.num,
                } else .{
                    .int = -operand.int,
                };
                const res = try f.newVal(vm, ref, .num);
                res.* = copy;
            },
            .bool_not => {
                const operand = (try f.bool(vm, data[inst].un)) orelse continue;
                const res = try f.newRef(vm, ref);

                res.* = if (operand) Value.False else Value.True;
            },
            .bit_not => {
                const operand = (try f.int(vm, data[inst].un)) orelse continue;

                const res = try f.newVal(vm, ref, .int);
                res.* = .{ .int = ~operand };
            },
            .spread => {
                var iterable = f.val(data[inst].un);

                switch (iterable.*) {
                    .str => {
                        return f.fatal(vm, "TODO spread str");
                    },
                    .range => |r| {
                        const res = try f.newVal(vm, ref, .list);
                        res.* = .{ .list = .{} };
                        try res.list.inner.ensureUnusedCapacity(vm.gc.gpa, @intCast(r.count()));

                        var it = r.iterator();
                        while (it.next()) |some| {
                            const int = try vm.gc.alloc(.int);
                            int.* = .{ .int = some };
                            res.list.inner.appendAssumeCapacity(int);
                        }
                        iterable = res;
                    },
                    .tuple, .list => {},
                    .iterator => unreachable,
                    else => {
                        try f.throwFmt(vm, "cannot iterate {s}", .{iterable.typeName()});
                        continue;
                    },
                }

                const res = try f.newVal(vm, ref, .spread);
                res.* = .{ .spread = .{ .iterable = iterable } };
            },
            .unwrap_error => {
                const arg = f.val(data[inst].un);

                if (arg.* != .err) {
                    try f.throw(vm, "expected an error");
                    continue;
                }

                const res = try f.newRef(vm, ref);
                res.* = try vm.gc.dupe(arg.err);
            },
            .unwrap_tagged => {
                const operand = f.val(mod.extra[data[inst].extra.extra]);
                const str_offset = @intFromEnum(mod.extra[data[inst].extra.extra + 1]);
                const name = mod.strings[str_offset..][0..data[inst].extra.len];

                if (operand.* != .tagged) {
                    try f.throw(vm, "expected a tagged value");
                    continue;
                }
                if (!mem.eql(u8, operand.tagged.name, name)) {
                    try f.throw(vm, "invalid tag");
                    continue;
                }

                const res = try f.newRef(vm, ref);
                res.* = operand.tagged.value;
            },
            .unwrap_tagged_or_null => {
                const res = try f.newRef(vm, ref);
                const operand = f.val(mod.extra[data[inst].extra.extra]);
                const str_offset = @intFromEnum(mod.extra[data[inst].extra.extra + 1]);
                const name = mod.strings[str_offset..][0..data[inst].extra.len];

                if (operand.* == .tagged and mem.eql(u8, operand.tagged.name, name)) {
                    res.* = operand.tagged.value;
                } else {
                    res.* = Value.Null;
                }
            },
            .check_len => {
                const container = f.val(data[inst].bin.lhs);
                const len = @intFromEnum(data[inst].bin.rhs);

                const ok = switch (container.*) {
                    .list => |list| list.inner.items.len == len,
                    .tuple => |tuple| tuple.len == len,
                    else => false,
                };
                const res = try f.newRef(vm, ref);
                if (ok) {
                    res.* = Value.True;
                } else {
                    res.* = Value.False;
                }
            },
            .assert_len => {
                const container = f.val(data[inst].bin.lhs);
                const len = @intFromEnum(data[inst].bin.rhs);

                const actual_len = switch (container.*) {
                    .list => |list| list.inner.items.len,
                    .tuple => |tuple| tuple.len,
                    else => {
                        try f.throwFmt(vm, "cannot destructure non list/tuple type {s}", .{container.typeName()});
                        continue;
                    },
                };
                if (len < actual_len) {
                    try f.throwFmt(
                        vm,
                        "not enough values to destructure (expected {d} args, got {d})",
                        .{ len, actual_len },
                    );
                } else if (len > actual_len) {
                    try f.throwFmt(
                        vm,
                        "too many values to destructure (expected {d} args, got {d})",
                        .{ len, actual_len },
                    );
                }
            },
            .spread_dest => {
                const container = f.val(data[inst].bin.lhs);
                const len = @intFromEnum(data[inst].bin.rhs);

                const items = switch (container.*) {
                    .list => |list| list.inner.items,
                    .tuple => |tuple| tuple,
                    else => {
                        try f.throwFmt(vm, "cannot destructure non list/tuple type {s}", .{container.typeName()});
                        continue;
                    },
                };
                if (items.len < len) {
                    try f.throwFmt(
                        vm,
                        "not enough values to destructure (expected at least {d} args, got {d})",
                        .{ len, items.len },
                    );
                    continue;
                }

                const res = try f.newVal(vm, ref, .list);
                res.* = .{ .list = .{} };
                try res.list.inner.ensureUnusedCapacity(vm.gc.gpa, items.len - len);

                for (items[len..]) |item| {
                    res.list.inner.appendAssumeCapacity(item);
                }
            },
            .get => {
                const res = try f.newRef(vm, ref);
                const container = f.val(data[inst].bin.lhs);
                const index = f.val(data[inst].bin.rhs);

                container.get(f.ctx(vm), index, res) catch |err| switch (err) {
                    error.Throw => continue,
                    else => |e| return e,
                };
            },
            .get_int => {
                const res = try f.newRef(vm, ref);
                const container = f.val(data[inst].bin.lhs);
                const index = Value{ .int = @intFromEnum(data[inst].bin.rhs) };

                container.get(f.ctx(vm), &index, res) catch |err| switch (err) {
                    error.Throw => continue,
                    else => |e| return e,
                };
            },
            .get_or_null => {
                const res = try f.newRef(vm, ref);
                const container = f.val(data[inst].bin.lhs);
                const index = f.val(data[inst].bin.rhs);

                if (container.* != .map) {
                    res.* = Value.Null;
                } else {
                    res.* = container.map.get(index) orelse Value.Null;
                }
            },
            .set => {
                const container = f.val(data[inst].range.start);
                const index = f.val(mod.extra[data[inst].range.extra]);
                const val = try f.valDupeSimple(vm, mod.extra[data[inst].range.extra + 1]);

                container.set(f.ctx(vm), index, val) catch |err| switch (err) {
                    error.Throw => continue,
                    else => |e| return e,
                };
            },
            .push_err_handler => {
                const err_val_ref = data[inst].jump_condition.operand;
                const offset = data[inst].jump_condition.offset;

                // Clear the error value ref in case we're in a loop
                const res_ref = try f.newRef(vm, err_val_ref);
                res_ref.* = null;

                try f.err_handlers.push(vm.gc.gpa, .{
                    .operand = err_val_ref,
                    .offset = offset,
                });
            },
            .pop_err_handler => {
                const handler = f.err_handlers.pop();

                // Jump past error handlers in case nothing was thrown
                const res_ref = f.newRef(vm, handler.operand) catch unreachable;
                if (res_ref.* == null) {
                    f.ip = data[inst].jump;
                }
            },
            .jump => {
                f.ip = data[inst].jump;
            },
            .jump_if_true => {
                const arg = (try f.bool(vm, data[inst].jump_condition.operand)) orelse continue;

                if (arg) {
                    f.ip = data[inst].jump_condition.offset;
                }
            },
            .jump_if_false => {
                const arg = (try f.bool(vm, data[inst].jump_condition.operand)) orelse continue;

                if (!arg) {
                    f.ip = data[inst].jump_condition.offset;
                }
            },
            .jump_if_null => {
                const arg = f.val(data[inst].jump_condition.operand);

                if (arg == Value.Null) {
                    f.ip = data[inst].jump_condition.offset;
                }
                continue;
            },
            .unwrap_error_or_jump => {
                const res = try f.newRef(vm, ref);
                const arg = f.val(data[inst].jump_condition.operand);

                if (arg.* == .err) {
                    res.* = arg.err;
                } else {
                    f.ip = data[inst].jump_condition.offset;
                }
            },
            .iter_init => {
                const arg = f.val(data[inst].un);

                const it = Value.iterate(arg, f.ctx(vm)) catch |err| switch (err) {
                    error.Throw => continue,
                    else => |e| return e,
                };
                const res = try f.newRef(vm, ref);
                res.* = it;
            },
            .iter_next => {
                const res = try f.newRef(vm, ref);
                const arg = f.val(data[inst].jump_condition.operand);

                const end = arg.iterator.next(f.ctx(vm), res) catch |err| switch (err) {
                    error.Throw => continue,
                    else => |e| return e,
                };

                if (!end) {
                    f.ip = data[inst].jump_condition.offset;
                }
            },
            .@"await" => {
                const arg = f.val(data[inst].un);

                if (arg.* != .frame) {
                    try f.throw(vm, "expected a function frame");
                    continue;
                }
                if (arg.frame.result_val) |some| {
                    const res = try f.newRef(vm, ref);
                    res.* = some;
                    continue;
                }

                const returned = vm.run(arg.frame) catch |err| {
                    if (err == error.Suspended) {
                        // rerun this await instruction once this function is resumed
                        f.ip -= 1;
                    }
                    return err;
                };
                arg.frame.result_val = returned;

                if (returned.* == .err) {
                    if (f.err_handlers.get()) |handler| {
                        const handler_operand = try f.newRef(vm, handler.operand);
                        handler_operand.* = returned.err;
                        f.ip = handler.offset;
                    }
                }
                const res = try f.newRef(vm, ref);
                res.* = returned;
            },
            .@"suspend" => {
                return error.Suspended;
            },
            .@"resume" => {
                const arg = f.val(data[inst].un);

                if (arg.* != .frame) {
                    try f.throw(vm, "expected a function frame");
                    continue;
                }
                if (arg.frame.result_val != null) {
                    try f.throw(vm, "attempt to resume a finished function frame");
                    continue;
                }

                _ = vm.run(arg.frame) catch |err| {
                    if (err == error.Suspended) {
                        // not our problem
                        continue;
                    }
                    return err;
                };
            },
            .call,
            .call_one,
            .call_zero,
            .this_call,
            .this_call_zero,
            .async_call,
            .async_call_one,
            .async_call_zero,
            .async_this_call,
            .async_this_call_zero,
            => {
                var buf: [1]Ref = undefined;
                var args: []const Ref = &.{};
                var callee: *Value = undefined;
                var this: *Value = Value.Null;
                switch (ops[inst]) {
                    .call, .async_call => {
                        const extra = mod.extra[data[inst].extra.extra..][0..data[inst].extra.len];
                        callee = f.val(extra[0]);
                        args = extra[1..];
                    },
                    .call_one, .async_call_one => {
                        callee = f.val(data[inst].bin.lhs);
                        buf[0] = data[inst].bin.rhs;
                        args = &buf;
                    },
                    .call_zero, .async_call_zero => callee = f.val(data[inst].un),
                    .this_call, .async_this_call => {
                        const extra = mod.extra[data[inst].extra.extra..][0..data[inst].extra.len];
                        callee = f.val(extra[0]);
                        this = f.val(extra[1]);
                        args = extra[2..];
                    },
                    .this_call_zero, .async_this_call_zero => {
                        callee = f.val(data[inst].bin.lhs);
                        this = f.val(data[inst].bin.rhs);
                    },
                    else => unreachable,
                }
                const is_async = switch (ops[inst]) {
                    .async_call, .async_call_one, .async_call_zero, .async_this_call, .async_this_call_zero => true,
                    else => false,
                };
                switch (callee.*) {
                    .native, .func => {},
                    else => {
                        try f.throwFmt(vm, "cannot call '{s}'", .{callee.typeName()});
                        continue;
                    },
                }

                var args_len: usize = 0;
                for (args) |item_ref| {
                    switch (f.val(item_ref).*) {
                        .spread => |spread| args_len += spread.len(),
                        else => args_len += 1,
                    }
                }

                if (callee.* == .native) {
                    if (callee.native.variadic) {
                        if (args_len < callee.native.arg_count) {
                            try f.throwFmt(
                                vm,
                                "expected at least {} args, got {}",
                                .{ callee.native.arg_count, args_len },
                            );
                            continue;
                        }
                    } else if (callee.native.arg_count != args_len) {
                        try f.throwFmt(
                            vm,
                            "expected {} args, got {}",
                            .{ callee.native.arg_count, args_len },
                        );
                        continue;
                    }

                    const args_tuple = try vm.gc.gpa.alloc(*Value, args_len);
                    defer vm.gc.gpa.free(args_tuple);

                    var i: u32 = 0;
                    for (args) |arg_ref| {
                        const arg = try f.valDupeSimple(vm, arg_ref);
                        switch (arg.*) {
                            .spread => |spread| {
                                const spread_items = spread.items();
                                for (spread_items) |item| {
                                    args_tuple[i] = item;
                                    i += 1;
                                }
                            },
                            else => {
                                args_tuple[i] = arg;
                                i += 1;
                            },
                        }
                    }

                    if (is_async) {
                        return f.fatal(vm, "TODO async call native function");
                    }

                    const res = callee.native.func(f.ctxThis(this, vm), args_tuple) catch |err| switch (err) {
                        error.Throw => continue,
                        else => |e| return e,
                    };

                    // function may mutate the stack
                    const returned = try f.newRef(vm, ref);
                    returned.* = res;
                } else if (callee.* == .func) {
                    const callee_args = callee.func.args();
                    const variadic = callee.func.variadic();
                    if (variadic) {
                        if (args_len < callee_args - 1) {
                            try f.throwFmt(
                                vm,
                                "expected at least {} args, got {}",
                                .{ callee_args, args_len },
                            );
                            continue;
                        }
                    } else if (callee_args != args_len) {
                        try f.throwFmt(
                            vm,
                            "expected {} args, got {}",
                            .{ callee_args, args_len },
                        );
                        continue;
                    }

                    if (vm.call_depth > max_depth) {
                        return f.fatal(vm, "maximum recursion depth exceeded");
                    }
                    vm.call_depth += 1;
                    defer vm.call_depth -= 1;

                    var new_frame = Frame{
                        .mod = callee.func.module,
                        .body = callee.func.body(),
                        .caller_frame = f,
                        .module_frame = f.module_frame,
                        .this = this,
                        .params = callee_args,
                        .captures = callee.func.captures(),
                    };
                    errdefer new_frame.deinit(vm);
                    vm.getFrame(&new_frame);

                    try new_frame.stack.ensureUnusedCapacity(vm.gc.gpa, callee_args);

                    {
                        const non_variadic_args = callee_args - @intFromBool(variadic);
                        var var_args: *Value = undefined;
                        if (variadic) {
                            var_args = try vm.gc.alloc(.list);
                            var_args.* = .{ .list = .{} };
                            try var_args.list.inner.ensureUnusedCapacity(vm.gc.gpa, args_len - non_variadic_args);
                        }

                        var i: u32 = 0;
                        var arg_list = &new_frame.stack;
                        for (args) |arg_ref| {
                            const arg = f.val(arg_ref);
                            switch (arg.*) {
                                .spread => |spread| {
                                    const spread_items = spread.items();
                                    for (spread_items) |item| {
                                        if (i == non_variadic_args) arg_list = &var_args.list.inner;
                                        arg_list.appendAssumeCapacity(item);
                                        i += 1;
                                    }
                                },
                                else => {
                                    if (i == non_variadic_args) arg_list = &var_args.list.inner;
                                    arg_list.appendAssumeCapacity(arg);
                                    i += 1;
                                },
                            }
                        }
                        if (variadic) new_frame.stack.appendAssumeCapacity(var_args);
                    }

                    var frame_val = try vm.gc.alloc(.frame);
                    frame_val.* = .{ .frame = &new_frame };
                    defer if (!is_async) {
                        frame_val.* = .{ .int = 0 }; // clear frame
                    };

                    const returned = vm.run(&new_frame) catch |err| {
                        if (err == error.Suspended) {
                            const duped_frame = try vm.gc.gpa.create(Frame);
                            errdefer vm.gc.gpa.destroy(duped_frame);
                            duped_frame.* = new_frame;
                            frame_val.frame = duped_frame;
                            new_frame.stack = .{};
                            new_frame.err_handlers = .{ .short = .{} };

                            const res = try f.newRef(vm, ref);
                            res.* = frame_val;
                            if (is_async) continue;
                        }
                        return err;
                    };
                    if (returned.* == .err) {
                        if (f.err_handlers.get()) |handler| {
                            const handler_operand = try f.newRef(vm, handler.operand);
                            handler_operand.* = returned.err;
                            f.ip = handler.offset;
                        }
                    }
                    const res = try f.newRef(vm, ref);
                    res.* = returned;
                    try vm.storeFrame(&new_frame);
                }
            },
            .ret => {
                const val = f.val(data[inst].un);
                f.result_val = val;
                return val;
            },
            .ret_null => {
                f.result_val = Value.Null;
                return Value.Null;
            },
            .throw => {
                const val = f.val(data[inst].un);
                if (f.err_handlers.get()) |handler| {
                    const handler_operand = try f.newRef(vm, handler.operand);
                    handler_operand.* = val;
                    f.ip = handler.offset;
                    continue;
                }
                const res = try vm.gc.alloc(.err);
                res.* = .{ .err = val };
                f.result_val = res;
                return res;
            },
        }
    }
}

const ErrHandlers = extern union {
    const Handler = extern struct {
        operand: Ref,
        offset: u32,
    };

    short: extern struct {
        len: u32 = 0,
        capacity: u32 = 4,
        arr: [4]Handler = undefined,
    },
    long: extern struct {
        len: u32,
        capacity: u32,
        ptr: [*]Handler,
    },

    pub fn deinit(e: *ErrHandlers, gpa: Allocator) void {
        if (e.short.capacity != 4) {
            gpa.free(e.long.ptr[0..e.long.capacity]);
        }
    }

    fn push(e: *ErrHandlers, gpa: Allocator, new: Handler) !void {
        if (e.short.capacity != 4) {
            var arr_list = std.ArrayList(Handler){
                .items = e.long.ptr[0..e.long.len],
                .capacity = e.long.capacity,
                .allocator = gpa,
            };
            defer {
                e.long.capacity = @intCast(arr_list.capacity);
                e.long.len = @intCast(arr_list.items.len);
                e.long.ptr = arr_list.items.ptr;
            }
            try arr_list.append(new);
        } else if (e.short.len == 4) {
            var arr_list = std.ArrayList(Handler).init(gpa);
            {
                errdefer arr_list.deinit();
                try arr_list.appendSlice(&e.short.arr);
                try arr_list.append(new);
            }
            e.long.capacity = @intCast(arr_list.capacity);
            e.long.len = @intCast(arr_list.items.len);
            e.long.ptr = arr_list.items.ptr;
        } else {
            e.short.arr[e.short.len] = new;
            e.short.len += 1;
        }
    }

    fn pop(e: *ErrHandlers) Handler {
        const handler = e.get().?;
        e.short.len -= 1;
        return handler;
    }

    fn get(e: ErrHandlers) ?Handler {
        return if (e.short.len == 0)
            null
        else if (e.short.capacity == 4)
            e.short.arr[e.short.len - 1]
        else
            e.long.ptr[e.long.len - 1];
    }
};

inline fn needNum(a: *Value, b: *Value) bool {
    return a.* == .num or b.* == .num;
}

inline fn asNum(val: *Value) f64 {
    return switch (val.*) {
        .int => |v| @floatFromInt(v),
        .num => |v| v,
        else => unreachable,
    };
}

fn checkZero(val: *Value) bool {
    switch (val.*) {
        .int => |v| return v == 0,
        .num => |v| return v == 0,
        else => unreachable,
    }
}

fn isNegative(val: *Value) bool {
    switch (val.*) {
        .int => |v| return v < 0,
        .num => |v| return v < 0,
        else => unreachable,
    }
}

fn getFrame(vm: *Vm, f: *Frame) void {
    const cached = vm.frame_cache.pop() orelse return;
    f.stack = cached.s;
    f.err_handlers = cached.e;
}

fn storeFrame(vm: *Vm, f: *Frame) !void {
    f.stack.items.len = 0;
    f.err_handlers.short.len = 0;
    try vm.frame_cache.append(vm.gc.gpa, .{ .s = f.stack, .e = f.err_handlers });
}

fn importFile(vm: *Vm, path: []const u8) !*Bytecode {
    if (!vm.options.import_files) return error.ImportingDisabled;

    var mod = mod: {
        const source = try std.fs.cwd().readFileAlloc(vm.gc.gpa, path, vm.options.max_import_size);
        errdefer vm.gc.gpa.free(source);

        break :mod try bog.compile(vm.gc.gpa, source, path, &vm.errors);
    };
    errdefer mod.deinit(vm.gc.gpa);

    const duped = try vm.gc.gpa.create(Bytecode);
    errdefer vm.gc.gpa.destroy(duped);
    duped.* = mod;

    _ = try vm.imported_modules.put(vm.gc.gpa, duped.debug_info.path, duped);
    return duped;
}

fn import(vm: *Vm, caller_frame: *Frame, id: []const u8) Error!*Value {
    const mod = vm.imported_modules.get(id) orelse if (mem.endsWith(u8, id, bog.extension))
        vm.importFile(id) catch |err| switch (err) {
            error.ImportingDisabled => {
                try caller_frame.throwFmt(
                    vm,
                    "cannot import '{s}': importing disabled by host",
                    .{id},
                );
                return Value.Null;
            },
            else => |e| {
                try caller_frame.throwFmt(
                    vm,
                    "cannot import '{s}': {s}",
                    .{ id, @errorName(e) },
                );
                return Value.Null;
            },
        }
    else {
        if (vm.imports.get(id)) |some| {
            return some(caller_frame.ctx(vm)) catch |err| switch (err) {
                error.Throw => return Value.Null,
                else => |e| return e,
            };
        }
        try caller_frame.throw(vm, "no such package");
        return Value.Null;
    };

    var frame = Frame{
        .mod = mod,
        .body = mod.main,
        .caller_frame = caller_frame,
        .module_frame = undefined,
        .this = Value.Null,
        .captures = &.{},
        .params = 0,
    };
    errdefer frame.deinit(vm);
    vm.getFrame(&frame);
    frame.module_frame = &frame;

    const frame_val = try vm.gc.alloc(.frame);
    frame_val.* = .{ .frame = &frame };
    defer frame_val.* = .{ .int = 0 }; // clear frame

    const res = vm.run(&frame);
    try vm.storeFrame(&frame);
    return res catch |err| switch (err) {
        error.Suspended => return frame.fatal(vm, "TODO import suspended"),
        else => |e| return e,
    };
}

fn errorFmt(vm: *Vm, comptime fmt: []const u8, args: anytype) Vm.Error!*Value {
    const str = try vm.gc.alloc(.str);
    str.* = .{ .str = try Value.String.init(vm.gc.gpa, fmt, args) };

    const err = try vm.gc.alloc(.err);
    err.* = .{ .err = str };
    return err;
}

fn errorVal(vm: *Vm, msg: []const u8) !*Value {
    const str = try vm.gc.alloc(.str);
    str.* = Value.string(msg);

    const err = try vm.gc.alloc(.err);
    err.* = .{ .err = str };
    return err;
}
