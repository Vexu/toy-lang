const std = @import("std");
const Allocator = mem.Allocator;
const assert = std.debug.assert;
const mem = std.mem;
const bog = @import("bog.zig");
const Bytecode = bog.Bytecode;
const Errors = bog.Errors;
const Node = bog.Node;
const Ref = Bytecode.Ref;
const Tree = bog.Tree;
const TokenIndex = bog.Token.Index;

const Compiler = @This();

// inputs
tree: *const Tree,
errors: *Errors,
gpa: Allocator,

// outputs
instructions: Bytecode.Inst.List = .{},
extra: std.ArrayListUnmanaged(Ref) = .{},
strings: std.ArrayListUnmanaged(u8) = .{},
string_interner: std.StringHashMapUnmanaged(u32) = .{},

// intermediate
arena: Allocator,
scopes: std.ArrayListUnmanaged(Scope) = .{},
unresolved_globals: std.ArrayListUnmanaged(UnresolvedGlobal) = .{},
list_buf: std.ArrayListUnmanaged(Ref) = .{},
cur_loop: ?*Loop = null,
cur_try: ?*Try = null,
cur_fn: ?*Fn = null,

code: *Code,

pub fn compile(gpa: Allocator, source: []const u8, errors: *Errors) (Compiler.Error || bog.Parser.Error || bog.Tokenizer.Error)!Bytecode {
    var tree = try bog.parse(gpa, source, errors);
    defer tree.deinit(gpa);

    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();

    var code: Code = .{};
    defer code.deinit(gpa);

    var compiler = Compiler{
        .tree = &tree,
        .errors = errors,
        .gpa = gpa,
        .arena = arena_state.allocator(),
        .code = &code,
    };
    defer compiler.deinit();

    for (tree.root_nodes) |node| {
        // try compiler.addLineInfo(node);

        const val = try compiler.genNode(node, .discard);
        if (val.isRt()) {
            // discard unused runtime value
            _ = try compiler.addUn(.discard, val.getRt());
        }
    }
    _ = try compiler.addUn(.ret_null, undefined);

    return Bytecode{
        .name = "",
        .code = compiler.instructions.toOwnedSlice(),
        .extra = compiler.extra.toOwnedSlice(gpa),
        .strings = compiler.strings.toOwnedSlice(gpa),
        .main = code.toOwnedSlice(gpa),
        .debug_info = undefined, // TODO
    };
}

pub fn deinit(c: *Compiler) void {
    c.scopes.deinit(c.gpa);
    c.unresolved_globals.deinit(c.gpa);
    c.list_buf.deinit(c.gpa);
    c.instructions.deinit(c.gpa);
    c.extra.deinit(c.gpa);
    c.strings.deinit(c.gpa);
    c.string_interner.deinit(c.gpa);
    c.* = undefined;
}

const Code = std.ArrayListUnmanaged(Bytecode.Ref);

const Fn = struct {
    code: Code = .{},
    captures: std.ArrayListUnmanaged(Capture) = .{},

    const Capture = struct {
        name: []const u8,
        local_ref: Ref,
        parent_ref: Ref,
        mut: bool,
    };
};

const UnresolvedGlobal = struct {
    identifier: TokenIndex,
    ref: Ref,
};

const Symbol = struct {
    name: []const u8,
    val: Value,
    ref: Ref,
    mut: bool,
};

const Scope = union(enum) {
    func: *Fn,
    symbol: Symbol,
};

const Loop = struct {
    breaks: JumpList = .{},
    first_inst: u32,
};

const Try = struct {
    jumps: JumpList = .{},
    err_ref: Ref,
};

const JumpList = std.ArrayListUnmanaged(Ref);

const Value = union(enum) {
    /// result of continue, break, return and assignment; cannot exist at runtime
    empty,
    ref: Ref,

    /// reference to a mutable variable
    mut: Ref,

    @"null",
    int: i64,
    num: f64,
    Bool: bool,
    str: []const u8,

    fn isRt(val: Value) bool {
        return switch (val) {
            .ref, .mut => true,
            else => false,
        };
    }

    fn getRt(val: Value) Ref {
        switch (val) {
            .ref, .mut => |r| return r,
            else => unreachable,
        }
    }

    fn getBool(val: Value, c: *Compiler, node: Node.Index) !bool {
        if (val != .Bool) {
            return c.reportErr("expected a boolean", node);
        }
        return val.Bool;
    }

    fn getInt(val: Value, c: *Compiler, node: Node.Index) !i64 {
        if (val != .int) {
            return c.reportErr("expected an integer", node);
        }
        return val.int;
    }

    fn getNum(val: Value) f64 {
        return switch (val) {
            .int => |v| @intToFloat(f64, v),
            .num => |v| v,
            else => unreachable,
        };
    }

    fn getStr(val: Value, c: *Compiler, node: Node.Index) ![]const u8 {
        if (val != .str) {
            return c.reportErr("expected a string", node);
        }
        return val.str;
    }

    fn checkNum(val: Value, c: *Compiler, node: Node.Index) !void {
        if (val != .int and val != .num) {
            return c.reportErr("expected a number", node);
        }
    }
};

pub const Error = error{CompileError} || Allocator.Error;

fn addInst(c: *Compiler, op: Bytecode.Inst.Op, data: Bytecode.Inst.Data) !Ref {
    const new_index = c.instructions.len;
    const ref = Bytecode.indexToRef(new_index);
    try c.instructions.append(c.gpa, .{ .op = op, .data = data });
    try c.code.append(c.gpa, ref);
    return ref;
}

fn addUn(c: *Compiler, op: Bytecode.Inst.Op, arg: Ref) !Ref {
    return c.addInst(op, .{ .un = arg });
}

fn addBin(c: *Compiler, op: Bytecode.Inst.Op, lhs: Ref, rhs: Ref) !Ref {
    return c.addInst(op, .{ .bin = .{ .lhs = lhs, .rhs = rhs } });
}

fn addJump(c: *Compiler, op: Bytecode.Inst.Op, operand: Ref) !Ref {
    return c.addInst(op, .{
        .jump_condition = .{
            .operand = operand,
            .offset = undefined, // set later
        },
    });
}

fn addExtra(c: *Compiler, op: Bytecode.Inst.Op, items: []const Ref) !Ref {
    const extra = @intCast(u32, c.extra.items.len);
    try c.extra.appendSlice(c.gpa, items);
    return c.addInst(op, .{
        .extra = .{
            .extra = extra,
            .len = @intCast(u32, items.len),
        },
    });
}

fn finishJump(c: *Compiler, jump_ref: Ref) void {
    const offset = @intCast(u32, c.code.items.len);
    const data = c.instructions.items(.data);
    const ops = c.instructions.items(.op);
    const jump_index = Bytecode.refToIndex(jump_ref);
    if (ops[jump_index] == .jump) {
        data[jump_index] = .{ .jump = offset };
    } else {
        data[jump_index].jump_condition.offset = offset;
    }
}

fn makeRuntime(c: *Compiler, val: Value) Error!Ref {
    return switch (val) {
        .empty => unreachable,
        .mut, .ref => |ref| ref,
        .@"null" => try c.addInst(.primitive, .{ .primitive = .@"null" }),
        .int => |int| try c.addInst(.int, .{ .int = int }),
        .num => |num| try c.addInst(.num, .{ .num = num }),
        .Bool => |b| try c.addInst(.primitive, .{ .primitive = if (b) .@"true" else .@"false" }),
        .str => |str| try c.addInst(.str, .{ .str = .{
            .len = @intCast(u32, str.len),
            .offset = try c.putString(str),
        } }),
    };
}

fn putString(c: *Compiler, str: []const u8) !u32 {
    if (c.string_interner.get(str)) |some| return some;
    const offset = @intCast(u32, c.strings.items.len);
    try c.strings.appendSlice(c.gpa, str);

    _ = try c.string_interner.put(c.gpa, str, offset);
    return offset;
}

const FoundSymbol = struct {
    ref: Ref,
    mut: bool,
    global: bool = false,
};

fn findSymbol(c: *Compiler, tok: TokenIndex) !FoundSymbol {
    return c.findSymbolExtra(tok, c.scopes.items.len);
}

fn findSymbolExtra(c: *Compiler, tok: TokenIndex, start_index: usize) Error!FoundSymbol {
    const name = c.tree.tokenSlice(tok);
    var i = start_index;

    while (i > 0) {
        i -= 1;
        const item = c.scopes.items[i];
        switch (item) {
            .func => |f| {
                for (f.captures.items) |capture| {
                    if (mem.eql(u8, capture.name, name)) {
                        return FoundSymbol{
                            .ref = capture.local_ref,
                            .mut = capture.mut,
                        };
                    }
                }

                const sym = try c.findSymbolExtra(tok, i);
                const loaded_capture = Bytecode.indexToRef(c.instructions.len);
                try c.instructions.append(c.gpa, .{
                    .op = .load_capture,
                    .data = .{ .un = @intToEnum(Ref, f.captures.items.len) },
                });
                try f.code.append(c.gpa, loaded_capture);
                try f.captures.append(c.gpa, .{
                    .name = name,
                    .parent_ref = sym.ref,
                    .local_ref = loaded_capture,
                    .mut = sym.mut,
                });
                return FoundSymbol{ .ref = loaded_capture, .mut = sym.mut };
            },
            .symbol => |sym| if (mem.eql(u8, sym.name, name)) {
                return FoundSymbol{ .ref = sym.ref, .mut = sym.mut };
            },
        }
    }

    const ref = try c.addInst(.load_global, undefined);
    try c.unresolved_globals.append(c.gpa, .{ .identifier = tok, .ref = ref });
    return FoundSymbol{ .ref = ref, .mut = false, .global = true };
}

fn checkRedeclaration(c: *Compiler, tok: TokenIndex) !void {
    const name = c.tree.tokenSlice(tok);
    var i = c.scopes.items.len;
    while (i > 0) {
        i -= 1;
        const scope = c.scopes.items[i];
        switch (scope) {
            .symbol => |sym| if (std.mem.eql(u8, sym.name, name)) {
                const msg = try bog.Value.String.init(c.gpa, "redeclaration of '{s}'", .{name});
                const starts = c.tree.tokens.items(.start);
                try c.errors.add(msg, starts[tok], .err);
                return error.CompileError;
            },
            else => {},
        }
    }
}

fn getLastNode(c: *Compiler, node: Node.Index) Node.Index {
    const data = c.tree.nodes.items(.data);
    const ids = c.tree.nodes.items(.id);
    var cur = node;
    while (true)
        switch (ids[cur]) {
            .paren_expr => cur = data[cur].un,
            else => return cur,
        };
}

const Result = union(enum) {
    /// A runtime value is expected
    ref: Ref,

    /// A value, runtime or constant, is expected
    value,

    /// No value is expected if some is given it will be discarded
    discard,

    /// returns .empty if res != .rt
    fn toVal(res: Result) Value {
        return if (res == .ref) .{ .ref = res.ref } else .empty;
    }
};

fn wrapResult(c: *Compiler, node: Node.Index, val: Value, res: Result) Error!Value {
    if (val == .empty and res != .discard) {
        return c.reportErr("expected a value", node);
    }
    if (res == .discard and val.isRt()) {
        // discard unused runtime value
        _ = try c.addUn(.discard, val.getRt());
    }
    if (res == .ref) {
        const val_ref = try c.makeRuntime(val);
        if (val_ref == res.ref) return val;
        if (val == .mut) {
            _ = try c.addBin(.copy, res.ref, val_ref);
        } else {
            _ = try c.addBin(.move, res.ref, val_ref);
        }
        return Value{ .ref = res.ref };
    }
    return val;
}

fn genNode(c: *Compiler, node: Node.Index, res: Result) Error!Value {
    const ids = c.tree.nodes.items(.id);
    const tokens = c.tree.nodes.items(.token);
    switch (ids[node]) {
        .string_expr => {
            const val = Value{ .str = try c.parseStr(tokens[node]) };
            return c.wrapResult(node, val, res);
        },
        .int_expr => {
            const slice = c.tree.tokenSlice(tokens[node]);
            const val = Value{
                .int = std.fmt.parseInt(i64, slice, 0) catch
                    return c.reportErr("TODO big int", node),
            };
            return c.wrapResult(node, val, res);
        },
        .num_expr => {
            const slice = c.tree.tokenSlice(tokens[node]);
            const val = Value{
                .num = std.fmt.parseFloat(f64, slice) catch unreachable,
            };
            return c.wrapResult(node, val, res);
        },
        .true_expr => {
            const val = Value{ .Bool = true };
            return c.wrapResult(node, val, res);
        },
        .false_expr => {
            const val = Value{ .Bool = false };
            return c.wrapResult(node, val, res);
        },
        .null_expr => {
            const val = Value{ .@"null" = {} };
            return c.wrapResult(node, val, res);
        },
        .ident_expr => {
            const val = try c.genIdent(node);
            return c.wrapResult(node, val, res);
        },
        .discard_expr => {
            return c.reportErr("'_' cannot be used as a value", node);
        },
        .mut_ident_expr => {
            return c.reportErr("'mut' cannot be used as a value", node);
        },

        .decl => try c.genDecl(node),

        .return_expr => try c.genReturn(node),
        .break_expr => try c.genBreak(node),
        .continue_expr => try c.genContinue(node),
        .for_expr, .for_let_expr => return c.genFor(node, res),
        .while_expr, .while_let_expr => return c.genWhile(node, res),
        .if_expr,
        .if_else_expr,
        .if_let_expr,
        .if_let_else_expr,
        => return c.genIf(node, res),
        .match_expr,
        .match_expr_one,
        => return c.genMatch(node, res),
        .match_case_catch_all,
        .match_case_let,
        .match_case,
        .match_case_one,
        => unreachable, // handled in genMatch
        .block_stmt_two,
        .block_stmt,
        => {
            var buf: [2]Node.Index = undefined;
            const stmts = c.tree.nodeItems(node, &buf);
            return c.genBlock(stmts, res);
        },
        .paren_expr => {
            const data = c.tree.nodes.items(.data);
            return c.genNode(data[node].un, res);
        },
        .as_expr => {
            const val = try c.genAs(node);
            return c.wrapResult(node, val, res);
        },
        .is_expr => {
            const val = try c.genIs(node);
            return c.wrapResult(node, val, res);
        },
        .bool_not_expr => {
            const val = try c.genBoolNot(node);
            return c.wrapResult(node, val, res);
        },
        .bit_not_expr => {
            const val = try c.genBitNot(node);
            return c.wrapResult(node, val, res);
        },
        .negate_expr => {
            const val = try c.genNegate(node);
            return c.wrapResult(node, val, res);
        },
        .less_than_expr,
        .less_than_equal_expr,
        .greater_than_expr,
        .greater_than_equal_expr,
        .equal_expr,
        .not_equal_expr,
        .in_expr,
        => {
            const val = try c.genComparison(node);
            return c.wrapResult(node, val, res);
        },
        .bit_and_expr,
        .bit_or_expr,
        .bit_xor_expr,
        .l_shift_expr,
        .r_shift_expr,
        => {
            const val = try c.genIntArithmetic(node);
            return c.wrapResult(node, val, res);
        },
        .add_expr,
        .sub_expr,
        .mul_expr,
        .div_expr,
        .div_floor_expr,
        .mod_expr,
        .pow_expr,
        => {
            const val = try c.genArithmetic(node);
            return c.wrapResult(node, val, res);
        },
        .assign => return c.genAssign(node, res),
        .add_assign,
        .sub_assign,
        .mul_assign,
        .pow_assign,
        .div_assign,
        .div_floor_assign,
        .mod_assign,
        .l_shift_assign,
        .r_shift_assign,
        .bit_and_assign,
        .bit_or_assign,
        .bit_xor_assign,
        => return c.genAugAssign(node, res),
        .tuple_expr,
        .tuple_expr_two,
        => return c.genTupleList(node, res, .build_tuple),
        .list_expr,
        .list_expr_two,
        => return c.genTupleList(node, res, .build_list),
        .map_expr,
        .map_expr_two,
        => return c.genMap(node, res),
        .map_item_expr => unreachable, // handled in genMap
        .error_expr => {
            const val = try c.genError(node);
            return c.wrapResult(node, val, res);
        },
        .import_expr => {
            const val = try c.genImport(node);
            return c.wrapResult(node, val, res);
        },
        .fn_expr, .fn_expr_one => {
            const val = try c.genFn(node);
            return c.wrapResult(node, val, res);
        },
        .call_expr,
        .call_expr_one,
        => {
            const val = try c.genCall(node);
            return c.wrapResult(node, val, res);
        },
        .member_access_expr => {
            const val = try c.genMemberAccess(node);
            return c.wrapResult(node, val, res);
        },
        .array_access_expr => {
            const val = try c.genArrayAccess(node);
            return c.wrapResult(node, val, res);
        },

        .this_expr,
        .throw_expr,
        .bool_or_expr,
        .bool_and_expr,
        .enum_expr,
        .range_expr,
        .range_expr_start,
        .range_expr_end,
        .range_expr_step,
        .try_expr,
        .try_expr_one,
        .catch_let_expr,
        .catch_expr,
        .format_expr,
        => @panic("TODO"),
    }
    return c.wrapResult(node, .empty, res);
}

fn genIdent(c: *Compiler, node: Node.Index) Error!Value {
    const tokens = c.tree.nodes.items(.token);
    const sym = try c.findSymbol(tokens[node]);
    if (sym.mut) {
        return Value{ .mut = sym.ref };
    } else {
        return Value{ .ref = sym.ref };
    }
}

fn genDecl(c: *Compiler, node: Node.Index) !void {
    const data = c.tree.nodes.items(.data);
    const init_val = try c.genNode(data[node].bin.rhs, .value);
    const destructuring = data[node].bin.lhs;
    const ids = c.tree.nodes.items(.id);

    const last_node = c.getLastNode(destructuring);
    if (ids[last_node] == .discard_expr) {
        return c.reportErr(
            "'_' cannot be used directly in variable initialization",
            last_node,
        );
    }
    try c.genLval(destructuring, .{ .let = &init_val });
}

fn genReturn(c: *Compiler, node: Node.Index) !void {
    const data = c.tree.nodes.items(.data);
    if (data[node].un != 0) {
        const operand = try c.genNode(data[node].un, .value);
        _ = try c.addUn(.ret, try c.makeRuntime(operand));
    } else {
        _ = try c.addUn(.ret_null, undefined);
    }
}

fn genBreak(c: *Compiler, node: Node.Index) !void {
    const loop = c.cur_loop orelse
        return c.reportErr("break outside of loop", node);

    const jump = try c.addInst(.jump, undefined);
    try loop.breaks.append(c.gpa, jump);
}

fn genContinue(c: *Compiler, node: Node.Index) !void {
    const loop = c.cur_loop orelse
        return c.reportErr("continue outside of loop", node);

    _ = try c.addInst(.jump, .{ .jump = loop.first_inst });
}

fn createListComprehension(c: *Compiler, ref: ?Ref) !Result {
    const list = try c.addExtra(.build_list, &.{});
    if (ref) |some| {
        _ = try c.addBin(.move, some, list);
        return Result{ .ref = some };
    } else {
        return Result{ .ref = list };
    }
}

fn genFor(c: *Compiler, node: Node.Index, res: Result) Error!Value {
    const sub_res = switch (res) {
        .discard => res,
        .value => try c.createListComprehension(null),
        .ref => |ref| try c.createListComprehension(ref),
    };
    const for_expr = Tree.For.get(c.tree.*, node);

    const scope_count = c.scopes.items.len;
    defer c.scopes.items.len = scope_count;

    const cond_val = try c.genNode(for_expr.cond, .value);
    if (!cond_val.isRt() and cond_val != .str)
        return c.reportErr("expected iterable value", for_expr.cond);

    const cond_ref = try c.makeRuntime(cond_val);

    // create the iterator
    const iter_ref = try c.addUn(.iter_init, cond_ref);
    if (c.cur_try) |try_scope| {
        _ = try c.addBin(.move, try_scope.err_ref, iter_ref);
        try try_scope.jumps.append(c.gpa, try c.addJump(.jump_if_error, iter_ref));
    }

    var loop = Loop{
        .first_inst = @intCast(u32, c.code.items.len),
    };
    defer loop.breaks.deinit(c.gpa);

    const old_loop = c.cur_loop;
    defer c.cur_loop = old_loop;
    c.cur_loop = &loop;

    // iter next is fused with a jump_null, offset is set after body is generated
    const elem_ref = try c.addJump(.iter_next, iter_ref);

    if (for_expr.capture) |some| {
        try c.genLval(some, .{ .let = &.{ .ref = elem_ref } });
    }

    switch (sub_res) {
        .discard => _ = try c.genNode(for_expr.body, .discard),
        .ref => |list| {
            const body_val = try c.genNode(for_expr.body, .value);
            const body_ref = try c.makeRuntime(body_val);
            _ = try c.addBin(.append, list, body_ref);
        },
        else => unreachable,
    }

    // jump to the start of the loop
    _ = try c.addInst(.jump, .{ .jump = loop.first_inst });

    // exit loop when IterNext results in None
    c.finishJump(elem_ref);

    for (loop.breaks.items) |@"break"| {
        c.finishJump(@"break");
    }
    return sub_res.toVal();
}

fn genWhile(c: *Compiler, node: Node.Index, res: Result) Error!Value {
    const sub_res = switch (res) {
        .discard => res,
        .value => try c.createListComprehension(null),
        .ref => |ref| try c.createListComprehension(ref),
    };
    const while_expr = Tree.While.get(c.tree.*, node);

    const scope_count = c.scopes.items.len;
    defer c.scopes.items.len = scope_count;

    var loop = Loop{
        .first_inst = @intCast(u32, c.code.items.len),
    };
    defer loop.breaks.deinit(c.gpa);

    const old_loop = c.cur_loop;
    defer c.cur_loop = old_loop;
    c.cur_loop = &loop;

    // beginning of condition
    var cond_jump: ?Ref = null;

    const cond_val = try c.genNode(while_expr.cond, .value);
    if (while_expr.capture) |capture| {
        if (cond_val.isRt()) {
            // exit loop if cond == null
            cond_jump = try c.addJump(.jump_if_null, cond_val.getRt());
        } else if (cond_val == .@"null") {
            // never executed
            return sub_res.toVal();
        }
        const cond_ref = try c.makeRuntime(cond_val);

        try c.genLval(capture, .{ .let = &.{ .ref = cond_ref } });
    } else if (cond_val.isRt()) {
        cond_jump = try c.addJump(.jump_if_false, cond_val.getRt());
    } else {
        const bool_val = try cond_val.getBool(c, while_expr.cond);
        if (bool_val == false) {
            // never executed
            return sub_res.toVal();
        }
    }

    switch (sub_res) {
        .discard => _ = try c.genNode(while_expr.body, .discard),
        .ref => |list| {
            const body_val = try c.genNode(while_expr.body, .value);
            const body_ref = try c.makeRuntime(body_val);
            _ = try c.addBin(.append, list, body_ref);
        },
        else => unreachable,
    }

    // jump to the start of the loop
    _ = try c.addInst(.jump, .{ .jump = loop.first_inst });

    // exit loop if cond == false
    if (cond_jump) |some| {
        c.finishJump(some);
    }

    for (loop.breaks.items) |@"break"| {
        c.finishJump(@"break");
    }

    return sub_res.toVal();
}

fn genIf(c: *Compiler, node: Node.Index, res: Result) Error!Value {
    const if_expr = Tree.If.get(c.tree.*, node);

    const scope_count = c.scopes.items.len;
    defer c.scopes.items.len = scope_count;

    var if_skip: Ref = undefined;

    const cond_val = try c.genNode(if_expr.cond, .value);
    if (if_expr.capture) |capture| {
        if (cond_val.isRt()) {
            // jump past if_body if cond == .none
            if_skip = try c.addJump(.jump_if_null, cond_val.getRt());
        } else if (cond_val == .@"null") {
            if (if_expr.else_body) |some| {
                return c.genNode(some, res);
            }

            const res_val = Value{ .@"null" = {} };
            return c.wrapResult(node, res_val, res);
        }
        const cond_ref = try c.makeRuntime(cond_val);

        try c.genLval(capture, .{ .let = &.{ .ref = cond_ref } });
    } else if (!cond_val.isRt()) {
        const bool_val = try cond_val.getBool(c, if_expr.cond);

        if (bool_val) {
            return c.genNode(if_expr.then_body, res);
        } else if (if_expr.else_body) |some| {
            return c.genNode(some, res);
        }

        const res_val = Value{ .@"null" = {} };
        return c.wrapResult(node, res_val, res);
    } else {
        // jump past if_body if cond == false
        if_skip = try c.addJump(.jump_if_false, cond_val.getRt());
    }
    const sub_res = switch (res) {
        .ref, .discard => res,
        .value => val: {
            // add a dummy instruction we can store the value into
            const res_ref = Bytecode.indexToRef(c.instructions.len);
            try c.instructions.append(c.gpa, undefined);
            break :val Result{ .ref = res_ref };
        },
    };

    // sub_res is either ref or discard, either way wrapResult handles it
    _ = try c.genNode(if_expr.then_body, sub_res);

    // jump past else_body since if_body was executed
    const else_skip = if (if_expr.else_body != null or sub_res == .ref)
        try c.addUn(.jump, undefined)
    else
        null;

    c.finishJump(if_skip);
    // end capture scope
    c.scopes.items.len = scope_count;

    if (if_expr.else_body) |some| {
        // sub_res is either ref or discard, either way wrapResult handles it
        _ = try c.genNode(some, sub_res);
    } else {
        const res_val = Value{ .@"null" = {} };
        _ = try c.wrapResult(node, res_val, sub_res);
    }

    if (else_skip) |some| {
        c.finishJump(some);
    }
    return sub_res.toVal();
}

fn genMatch(c: *Compiler, node: Node.Index, res: Result) Error!Value {
    const sub_res = switch (res) {
        .ref, .discard => res,
        .value => val: {
            // add a dummy instruction we can store the value into
            const res_ref = Bytecode.indexToRef(c.instructions.len);
            try c.instructions.append(c.gpa, undefined);
            break :val Result{ .ref = res_ref };
        },
    };

    const ids = c.tree.nodes.items(.id);
    const data = c.tree.nodes.items(.data);
    var buf: [2]Node.Index = undefined;
    const cases = c.tree.nodeItems(node, &buf);

    const cond_val = try c.genNode(cases[0], .value);
    const cond_ref = try c.makeRuntime(cond_val);

    var jumps: JumpList = .{};
    defer jumps.deinit(c.gpa);

    var seen_catch_all = false;
    for (cases[1..]) |case, case_i| {
        if (seen_catch_all) {
            return c.reportErr("additional cases after catch-all case", case);
        }

        const scope_count = c.scopes.items.len;
        defer c.scopes.items.len = scope_count;

        var expr: Node.Index = undefined;
        var case_skip: ?Ref = null;

        switch (ids[case]) {
            .match_case_catch_all => {
                seen_catch_all = true;
                expr = data[case].un;
            },
            .match_case_let => {
                seen_catch_all = true;
                expr = data[case].bin.rhs;

                try c.genLval(case, .{ .let = &.{ .ref = cond_ref } });
            },
            .match_case,
            .match_case_one,
            => {
                var buf_2: [2]Node.Index = undefined;
                const items = c.tree.nodeItems(case, &buf_2);
                expr = items[items.len - 1];

                if (items.len == 2) {
                    const item_val = try c.genNode(items[0], .value);
                    const item_ref = try c.makeRuntime(item_val);
                    // if not equal to the error value jump over this handler
                    const eq_ref = try c.addBin(.equal, item_ref, cond_ref);
                    case_skip = try c.addJump(.jump_if_false, eq_ref);
                } else {
                    var success_jumps: JumpList = .{};
                    defer success_jumps.deinit(c.gpa);

                    for (items[0 .. items.len - 1]) |item| {
                        const item_val = try c.genNode(item, .value);
                        const item_ref = try c.makeRuntime(item_val);

                        const eq_ref = try c.addBin(.equal, item_ref, cond_ref);
                        try success_jumps.append(c.gpa, try c.addJump(.jump_if_true, eq_ref));
                    }
                    case_skip = try c.addUn(.jump, undefined);

                    for (success_jumps.items) |some| {
                        c.finishJump(some);
                    }
                }
            },
            else => unreachable,
        }

        // sub_res is either ref or discard, either way wrapResult handles it
        _ = try c.genNode(expr, sub_res);

        // exit match (unless it's this is the last case)
        if (case_i + 2 != cases.len) {
            try jumps.append(c.gpa, try c.addUn(.jump, undefined));
        }

        // jump over this case if the value doesn't match
        if (case_skip) |some| {
            c.finishJump(some);
        }
    }

    if (!seen_catch_all) {
        const res_val = Value{ .@"null" = {} };
        _ = try c.wrapResult(node, res_val, sub_res);
    }

    // exit match
    for (jumps.items) |jump| {
        c.finishJump(jump);
    }
    return sub_res.toVal();
}

fn genBlock(c: *Compiler, stmts: []const Node.Index, res: Result) Error!Value {
    const scope_count = c.scopes.items.len;
    defer c.scopes.items.len = scope_count;

    for (stmts) |stmt, i| {
        // return value of last instruction if it is not discarded
        if (i + 1 == stmts.len) {
            return c.genNode(stmt, res);
        }

        _ = try c.genNode(stmt, .discard);
    }
    return Value{ .@"null" = {} };
}

const type_id_map = std.ComptimeStringMap(bog.Type, .{
    .{ "null", .@"null" },
    .{ "int", .int },
    .{ "num", .num },
    .{ "bool", .bool },
    .{ "str", .str },
    .{ "tuple", .tuple },
    .{ "map", .map },
    .{ "list", .list },
    .{ "err", .err },
    .{ "range", .range },
    .{ "func", .func },
    .{ "tagged", .tagged },
});

fn genAs(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const lhs = try c.genNode(data[node].ty_bin.lhs, .value);

    const ty_tok = data[node].ty_bin.rhs;

    const type_str = c.tree.tokenSlice(ty_tok);
    const type_id = type_id_map.get(type_str) orelse
        return c.reportErr("expected a type name", ty_tok);

    if (lhs.isRt()) {
        const cast_ref = try c.addInst(.as, .{ .bin_ty = .{
            .operand = lhs.getRt(),
            .ty = type_id,
        } });

        // `as` can result in a type error
        if (c.cur_try) |try_scope| {
            _ = try c.addBin(.move, try_scope.err_ref, cast_ref);
            try try_scope.jumps.append(c.gpa, try c.addJump(.jump_if_error, cast_ref));
        }
        return Value{ .ref = cast_ref };
    }

    return switch (type_id) {
        .@"null" => Value{ .@"null" = {} },
        .int => Value{
            .int = switch (lhs) {
                .int => |val| val,
                .num => |val| std.math.lossyCast(i64, val),
                .Bool => |val| @boolToInt(val),
                .str => |str| std.fmt.parseInt(i64, str, 0) catch
                    return c.reportErr("invalid cast to int", ty_tok),
                else => return c.reportErr("invalid cast to int", ty_tok),
            },
        },
        .num => Value{
            .num = switch (lhs) {
                .num => |val| val,
                .int => |val| @intToFloat(f64, val),
                .Bool => |val| @intToFloat(f64, @boolToInt(val)),
                .str => |str| std.fmt.parseFloat(f64, str) catch
                    return c.reportErr("invalid cast to num", ty_tok),
                else => return c.reportErr("invalid cast to num", ty_tok),
            },
        },
        .bool => Value{
            .Bool = switch (lhs) {
                .int => |val| val != 0,
                .num => |val| val != 0,
                .Bool => |val| val,
                .str => |val| if (mem.eql(u8, val, "true"))
                    true
                else if (mem.eql(u8, val, "false"))
                    false
                else
                    return c.reportErr("cannot cast string to bool", ty_tok),
                else => return c.reportErr("invalid cast to bool", ty_tok),
            },
        },
        .str => Value{
            .str = switch (lhs) {
                .int => |val| try std.fmt.allocPrint(c.arena, "{}", .{val}),
                .num => |val| try std.fmt.allocPrint(c.arena, "{d}", .{val}),
                .Bool => |val| if (val) "true" else "false",
                .str => |val| val,
                else => return c.reportErr("invalid cast to string", ty_tok),
            },
        },
        .func => return c.reportErr("cannot cast to function", ty_tok),
        .err => return c.reportErr("cannot cast to error", ty_tok),
        .range => return c.reportErr("cannot cast to range", ty_tok),
        .tuple, .map, .list, .tagged => return c.reportErr("invalid cast", ty_tok),
        else => unreachable,
    };
}

fn genIs(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const lhs = try c.genNode(data[node].ty_bin.lhs, .value);

    const ty_tok = data[node].ty_bin.rhs;

    const type_str = c.tree.tokenSlice(ty_tok);
    const type_id = type_id_map.get(type_str) orelse
        return c.reportErr("expected a type name", ty_tok);

    if (lhs.isRt()) {
        const ref = try c.addInst(.is, .{ .bin_ty = .{
            .operand = lhs.getRt(),
            .ty = type_id,
        } });
        return Value{ .ref = ref };
    }

    return Value{
        .Bool = switch (type_id) {
            .@"null" => lhs == .@"null",
            .int => lhs == .int,
            .num => lhs == .num,
            .bool => lhs == .Bool,
            .str => lhs == .str,
            else => false,
        },
    };
}

fn genBoolNot(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const operand = try c.genNode(data[node].un, .value);

    if (operand.isRt()) {
        const ref = try c.addUn(.bool_not, operand.getRt());
        return Value{ .ref = ref };
    }
    return Value{ .Bool = !try operand.getBool(c, data[node].un) };
}

fn genBitNot(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const operand = try c.genNode(data[node].un, .value);

    if (operand.isRt()) {
        const ref = try c.addUn(.bit_not, operand.getRt());
        return Value{ .ref = ref };
    }
    return Value{ .int = ~try operand.getInt(c, data[node].un) };
}

fn genNegate(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const operand = try c.genNode(data[node].un, .value);

    if (operand.isRt()) {
        const ref = try c.addUn(.negate, operand.getRt());
        return Value{ .ref = ref };
    }

    try operand.checkNum(c, data[node].un);
    if (operand == .int) {
        return Value{
            .int = std.math.sub(i64, 0, operand.int) catch
                return c.reportErr("TODO integer overflow", node),
        };
    } else {
        return Value{ .num = -operand.num };
    }
}

fn needNum(a: Value, b: Value) bool {
    return a == .num or b == .num;
}

fn genComparison(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const lhs = data[node].bin.lhs;
    const rhs = data[node].bin.rhs;
    var lhs_val = try c.genNode(lhs, .value);
    var rhs_val = try c.genNode(rhs, .value);

    const op: Bytecode.Inst.Op = switch (c.tree.nodes.items(.id)[node]) {
        .less_than_expr => .less_than,
        .less_than_equal_expr => .less_than_equal,
        .greater_than_expr => .greater_than,
        .greater_than_equal_expr => .greater_than_equal,
        .equal_expr => .equal,
        .not_equal_expr => .not_equal,
        .in_expr => .in,
        else => unreachable,
    };

    if (rhs_val.isRt() or lhs_val.isRt()) {
        const rhs_ref = try c.makeRuntime(rhs_val);
        const lhs_ref = try c.makeRuntime(lhs_val);

        const ref = try c.addBin(op, lhs_ref, rhs_ref);
        return Value{ .ref = ref };
    }

    // order comparisons are only allowed on numbers
    switch (op) {
        .in, .equal, .not_equal => {},
        else => {
            try lhs_val.checkNum(c, lhs);
            try rhs_val.checkNum(c, rhs);
        },
    }

    switch (op) {
        .less_than => return Value{
            .Bool = if (needNum(lhs_val, rhs_val))
                lhs_val.getNum() < rhs_val.getNum()
            else
                lhs_val.int < rhs_val.int,
        },
        .less_than_equal => return Value{
            .Bool = if (needNum(lhs_val, rhs_val))
                lhs_val.getNum() <= rhs_val.getNum()
            else
                lhs_val.int <= rhs_val.int,
        },
        .greater_than => return Value{
            .Bool = if (needNum(lhs_val, rhs_val))
                lhs_val.getNum() > rhs_val.getNum()
            else
                lhs_val.int > rhs_val.int,
        },
        .greater_than_equal => return Value{
            .Bool = if (needNum(lhs_val, rhs_val))
                lhs_val.getNum() >= rhs_val.getNum()
            else
                lhs_val.int >= rhs_val.int,
        },
        .equal, .not_equal => {
            const eql = switch (lhs_val) {
                .@"null" => rhs_val == .@"null",
                .int => |a_val| switch (rhs_val) {
                    .int => |b_val| a_val == b_val,
                    .num => |b_val| @intToFloat(f64, a_val) == b_val,
                    else => false,
                },
                .num => |a_val| switch (rhs_val) {
                    .int => |b_val| a_val == @intToFloat(f64, b_val),
                    .num => |b_val| a_val == b_val,
                    else => false,
                },
                .Bool => |a_val| switch (rhs_val) {
                    .Bool => |b_val| a_val == b_val,
                    else => false,
                },
                .str => |a_val| switch (rhs_val) {
                    .str => |b_val| mem.eql(u8, a_val, b_val),
                    else => false,
                },
                .empty, .mut, .ref => unreachable,
            };
            return Value{ .Bool = if (op == .equal) eql else !eql };
        },
        .in => return Value{
            .Bool = switch (lhs_val) {
                .str => mem.indexOf(
                    u8,
                    try lhs_val.getStr(c, lhs),
                    try rhs_val.getStr(c, rhs),
                ) != null,
                else => return c.reportErr("TODO: range without strings", lhs),
            },
        },
        else => unreachable,
    }
}

fn genIntArithmetic(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const lhs = data[node].bin.lhs;
    const rhs = data[node].bin.rhs;
    var lhs_val = try c.genNode(lhs, .value);
    var rhs_val = try c.genNode(rhs, .value);

    const op: Bytecode.Inst.Op = switch (c.tree.nodes.items(.id)[node]) {
        .bit_and_expr => .bit_and,
        .bit_or_expr => .bit_or,
        .bit_xor_expr => .bit_xor,
        .l_shift_expr => .l_shift,
        .r_shift_expr => .r_shift,
        else => unreachable,
    };

    if (lhs_val.isRt() or rhs_val.isRt()) {
        const rhs_ref = try c.makeRuntime(rhs_val);
        const lhs_ref = try c.makeRuntime(lhs_val);

        const ref = try c.addBin(op, lhs_ref, rhs_ref);
        return Value{ .ref = ref };
    }
    const l_int = try lhs_val.getInt(c, lhs);
    const r_int = try rhs_val.getInt(c, rhs);

    switch (op) {
        .bit_and => return Value{ .int = l_int & r_int },
        .bit_or => return Value{ .int = l_int | r_int },
        .bit_xor => return Value{ .int = l_int ^ r_int },
        .l_shift => {
            if (r_int < 0)
                return c.reportErr("shift by negative amount", rhs);
            const val = if (r_int > std.math.maxInt(u6))
                0
            else
                l_int << @truncate(u6, @bitCast(u64, r_int));
            return Value{ .int = val };
        },
        .r_shift => {
            if (r_int < 0)
                return c.reportErr("shift by negative amount", rhs);
            const val = if (r_int > std.math.maxInt(u6))
                std.math.maxInt(i64)
            else
                l_int >> @truncate(u6, @bitCast(u64, r_int));
            return Value{ .int = val };
        },
        else => unreachable,
    }
}

fn genArithmetic(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const lhs = data[node].bin.lhs;
    const rhs = data[node].bin.rhs;
    var lhs_val = try c.genNode(lhs, .value);
    var rhs_val = try c.genNode(rhs, .value);

    const op: Bytecode.Inst.Op = switch (c.tree.nodes.items(.id)[node]) {
        .add_expr => .add,
        .sub_expr => .sub,
        .mul_expr => .mul,
        .div_expr => .div,
        .div_floor_expr => .div_floor,
        .mod_expr => .mod,
        .pow_expr => .pow,
        else => unreachable,
    };

    if (!rhs_val.isRt() and !lhs_val.isRt()) rt: {
        try lhs_val.checkNum(c, lhs);
        try rhs_val.checkNum(c, rhs);

        switch (op) {
            .add => {
                if (needNum(lhs_val, rhs_val)) {
                    return Value{ .num = lhs_val.getNum() + rhs_val.getNum() };
                }
                return Value{
                    .int = std.math.add(i64, lhs_val.int, rhs_val.int) catch break :rt,
                };
            },
            .sub => {
                if (needNum(lhs_val, rhs_val)) {
                    return Value{ .num = lhs_val.getNum() - rhs_val.getNum() };
                }
                return Value{
                    .int = std.math.sub(i64, lhs_val.int, rhs_val.int) catch break :rt,
                };
            },
            .mul => {
                if (needNum(lhs_val, rhs_val)) {
                    return Value{ .num = lhs_val.getNum() * rhs_val.getNum() };
                }
                return Value{
                    .int = std.math.mul(i64, lhs_val.int, rhs_val.int) catch break :rt,
                };
            },
            .div => return Value{ .num = lhs_val.getNum() / rhs_val.getNum() },
            .div_floor => {
                if (needNum(lhs_val, rhs_val)) {
                    return Value{ .int = @floatToInt(i64, @divFloor(lhs_val.getNum(), rhs_val.getNum())) };
                }
                return Value{
                    .int = std.math.divFloor(i64, lhs_val.int, rhs_val.int) catch break :rt,
                };
            },
            .mod => {
                if (needNum(lhs_val, rhs_val)) {
                    return Value{ .num = @rem(lhs_val.getNum(), rhs_val.getNum()) };
                }
                return Value{
                    .int = std.math.rem(i64, lhs_val.int, rhs_val.int) catch break :rt,
                };
            },
            .pow => {
                if (needNum(lhs_val, rhs_val)) {
                    return Value{ .num = std.math.pow(f64, lhs_val.getNum(), rhs_val.getNum()) };
                }
                return Value{
                    .int = std.math.powi(i64, lhs_val.int, rhs_val.int) catch break :rt,
                };
            },
            else => unreachable,
        }
    }

    const rhs_ref = try c.makeRuntime(rhs_val);
    const lhs_ref = try c.makeRuntime(lhs_val);

    const ref = try c.addBin(op, lhs_ref, rhs_ref);
    return Value{ .ref = ref };
}

fn genAssign(c: *Compiler, node: Node.Index, res: Result) Error!Value {
    if (res != .discard) {
        return c.reportErr("assignment produces no value", node);
    }
    const data = c.tree.nodes.items(.data);
    const lhs = data[node].bin.lhs;
    const rhs = data[node].bin.rhs;
    const rhs_val = try c.genNode(rhs, .value);

    try c.genLval(lhs, .{ .assign = &rhs_val });
    return .empty;
}

fn genAugAssign(c: *Compiler, node: Node.Index, res: Result) Error!Value {
    if (res != .discard) {
        return c.reportErr("assignment produces no value", node);
    }
    const data = c.tree.nodes.items(.data);
    const lhs = data[node].bin.lhs;
    const rhs = data[node].bin.rhs;
    const rhs_val = try c.genNode(rhs, .value);

    const op: Bytecode.Inst.Op = switch (c.tree.nodes.items(.id)[node]) {
        .add_assign => .add,
        .sub_assign => .sub,
        .mul_assign => .mul,
        .pow_assign => .pow,
        .div_assign => .div,
        .div_floor_assign => .div_floor,
        .mod_assign => .mod,
        .l_shift_assign => .l_shift,
        .r_shift_assign => .r_shift,
        .bit_and_assign => .bit_and,
        .bit_or_assign => .bit_or,
        .bit_xor_assign => .bit_xor,
        else => unreachable,
    };

    var lhs_ref: Ref = undefined;
    try c.genLval(lhs, .{ .aug_assign = &lhs_ref });
    if (!rhs_val.isRt()) switch (op) {
        // zig fmt: off
        .add, .sub, .mul, .pow, .div, .div_floor, .mod,
        => try rhs_val.checkNum(c, rhs),
        .l_shift, .r_shift, .bit_and, .bit_or, .bit_xor,
        => _ = try rhs_val.getInt(c, rhs),
        // zig fmt: on
        else => unreachable,
    };

    const rhs_ref = try c.makeRuntime(rhs_val);
    const res_ref = try c.addBin(op, lhs_ref, rhs_ref);
    _ = try c.addBin(.move, lhs_ref, res_ref);
    return Value.empty;
}

fn genTupleList(
    c: *Compiler,
    node: Node.Index,
    res: Result,
    op: Bytecode.Inst.Op,
) Error!Value {
    var buf: [2]Node.Index = undefined;
    const items = c.tree.nodeItems(node, &buf);

    const list_buf_top = c.list_buf.items.len;
    defer c.list_buf.items.len = list_buf_top;

    if (res == .discard) {
        for (items) |val| {
            _ = try c.genNode(val, .discard);
        }
        return Value{ .empty = {} };
    }

    for (items) |val| {
        const item_val = try c.genNode(val, .value);
        const item_ref = try c.makeRuntime(item_val);

        try c.list_buf.append(c.gpa, item_ref);
    }

    const ref = try c.addExtra(op, c.list_buf.items[list_buf_top..]);
    return c.wrapResult(node, Value{ .ref = ref }, res);
}

fn genMap(c: *Compiler, node: Node.Index, res: Result) Error!Value {
    const data = c.tree.nodes.items(.data);
    const tok_ids = c.tree.tokens.items(.id);
    var buf: [2]Node.Index = undefined;
    const items = c.tree.nodeItems(node, &buf);

    const list_buf_top = c.list_buf.items.len;
    defer c.list_buf.items.len = list_buf_top;

    if (res == .discard) {
        for (items) |item| {
            if (data[item].bin.lhs != 0) {
                const last_node = c.getLastNode(data[item].bin.lhs);
                if (tok_ids[last_node] != .identifier) {
                    _ = try c.genNode(data[item].bin.lhs, .discard);
                }
            }

            _ = try c.genNode(data[item].bin.lhs, .discard);
        }
        return Value{ .empty = {} };
    }

    for (items) |item| {
        var key: Ref = undefined;
        if (data[item].bin.lhs != 0) {
            const last_node = c.getLastNode(data[item].bin.lhs);
            if (tok_ids[last_node] == .identifier) {
                // `ident = value` is equal to `"ident" = value`
                const ident = c.tree.firstToken(last_node);
                const str = c.tree.tokenSlice(ident);
                key = try c.addInst(.str, .{ .str = .{
                    .len = @intCast(u32, str.len),
                    .offset = try c.putString(str),
                } });
            } else {
                var key_val = try c.genNode(data[item].bin.lhs, .value);
                key = try c.makeRuntime(key_val);
            }
        } else {
            const last_node = c.getLastNode(data[item].bin.rhs);
            if (tok_ids[last_node] == .identifier) {
                return c.reportErr("expected a key", item);
            }
            // `ident` is equal to `"ident" = ident`
            const ident = c.tree.firstToken(last_node);
            const str = c.tree.tokenSlice(ident);
            key = try c.addInst(.str, .{ .str = .{
                .len = @intCast(u32, str.len),
                .offset = try c.putString(str),
            } });
        }

        var value_val = try c.genNode(data[item].bin.lhs, .value);
        const value_ref = try c.makeRuntime(value_val);
        try c.list_buf.appendSlice(c.gpa, &.{ key, value_ref });
    }

    const ref = try c.addExtra(.build_map, c.list_buf.items[list_buf_top..]);
    return c.wrapResult(node, Value{ .ref = ref }, res);
}

fn genError(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    if (data[node].un == 0) {
        const ref = try c.addUn(.build_error_null, undefined);
        return Value{ .ref = ref };
    }
    const operand_val = try c.genNode(data[node].un, .value);
    const operand_ref = try c.makeRuntime(operand_val);

    const ref = try c.addUn(.build_error, operand_ref);
    return Value{ .ref = ref };
}

fn genImport(c: *Compiler, node: Node.Index) Error!Value {
    const tokens = c.tree.nodes.items(.token);
    const str = try c.parseStr(tokens[node]);

    const res_ref = try c.addInst(.import, .{ .str = .{
        .len = @intCast(u32, str.len),
        .offset = try c.putString(str),
    } });
    return Value{ .ref = res_ref };
}

fn genFn(c: *Compiler, node: Node.Index) Error!Value {
    var buf: [2]Node.Index = undefined;
    const items = c.tree.nodeItems(node, &buf);
    const params = items[@boolToInt(items[0] == 0) .. items.len - 1];
    const body = items[items.len - 1];

    if (params.len > Bytecode.max_params) {
        return c.reportErr("too many parameters", node);
    }

    var func = Fn{};
    defer func.code.deinit(c.gpa);
    defer func.captures.deinit(c.gpa);

    const old_code = c.code;
    const scope_count = c.scopes.items.len;
    const old_try = c.cur_try;
    const old_loop = c.cur_loop;
    const old_fn = c.cur_fn;
    defer {
        c.code = old_code;
        c.scopes.items.len = scope_count;
        c.cur_try = old_try;
        c.cur_loop = old_loop;
        c.cur_fn = old_fn;
    }
    c.code = &func.code;
    c.cur_try = null;
    c.cur_loop = null;
    c.cur_fn = &func;

    try c.scopes.append(c.gpa, .{ .func = &func });

    // destructure parameters
    for (params) |param, i| {
        try c.genLval(param, .{ .let = &.{ .ref = @intToEnum(Ref, i) } });
    }

    // for one liner functions return the value of the expression,
    // otherwise require an explicit return statement
    const last = c.getLastNode(body);
    const ids = c.tree.nodes.items(.id);
    const sub_res: Result = switch (ids[last]) {
        // zig fmt: off
        .block_stmt_two, .block_stmt, .assign, .add_assign, .sub_assign, .mul_assign,
        .pow_assign, .div_assign, .div_floor_assign, .mod_assign, .l_shift_assign,
        .r_shift_assign, .bit_and_assign, .bit_or_assign, .bit_xor_assign => .discard,
        // zig fmt: on
        else => .value,
    };

    const body_val = try c.genNode(body, sub_res);
    if (body_val == .empty or body_val == .@"null") {
        _ = try c.addUn(.ret_null, undefined);
    } else {
        const body_ref = try c.makeRuntime(body_val);
        _ = try c.addUn(.ret, body_ref);
    }

    // done generating the new function
    c.code = old_code;

    const fn_info = Bytecode.Inst.Data.FnInfo{
        .args = @intCast(u8, params.len),
        .captures = @intCast(u24, func.captures.items.len),
    };

    const extra = @intCast(u32, c.extra.items.len);
    try c.extra.append(c.gpa, @intToEnum(Ref, @bitCast(u32, fn_info)));
    try c.extra.appendSlice(c.gpa, func.code.items);
    const func_ref = try c.addInst(.build_func, .{
        .extra = .{
            .extra = extra,
            .len = @intCast(u32, func.code.items.len + 1),
        },
    });

    for (func.captures.items) |capture| {
        _ = try c.addBin(.store_capture, func_ref, capture.parent_ref);
    }
    return Value{ .ref = func_ref };
}

fn genCall(c: *Compiler, node: Node.Index) Error!Value {
    var buf: [2]Node.Index = undefined;
    const items = c.tree.nodeItems(node, &buf);

    const callee = items[0];
    const args = items[1..];

    const callee_val = try c.genNode(callee, .value);
    if (!callee_val.isRt()) {
        return c.reportErr("attempt to call non function value", callee);
    }

    if (args.len > Bytecode.max_params) {
        return c.reportErr("too many arguments", node);
    }

    const list_buf_top = c.list_buf.items.len;
    defer c.list_buf.items.len = list_buf_top;

    try c.list_buf.append(c.gpa, callee_val.getRt());

    for (args) |arg| {
        const arg_val = try c.genNode(arg, .value);
        const arg_ref = if (arg_val == .mut)
            try c.addUn(.copy_un, arg_val.mut)
        else
            try c.makeRuntime(arg_val);

        try c.list_buf.append(c.gpa, arg_ref);
    }

    const arg_refs = c.list_buf.items[list_buf_top..];
    const res_ref = switch (arg_refs.len) {
        0 => unreachable, // callee is always added
        1 => try c.addUn(.call_zero, arg_refs[0]),
        2 => try c.addBin(.call_one, arg_refs[0], arg_refs[1]),
        else => try c.addExtra(.call, arg_refs),
    };

    if (c.cur_try) |try_scope| {
        _ = try c.addBin(.move, try_scope.err_ref, res_ref);
        try try_scope.jumps.append(c.gpa, try c.addJump(.jump_if_error, res_ref));
    }

    return Value{ .ref = res_ref };
}

fn genMemberAccess(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const tokens = c.tree.nodes.items(.token);
    const operand = data[node].un;

    var operand_val = try c.genNode(operand, .value);
    if (operand_val != .str and !operand_val.isRt()) {
        return c.reportErr("invalid operand to member access", operand);
    }
    const operand_ref = try c.makeRuntime(operand_val);

    var name_val = Value{ .str = c.tree.tokenSlice(tokens[node]) };
    var name_ref = try c.makeRuntime(name_val);

    const res_ref = try c.addBin(.get, operand_ref, name_ref);
    return Value{ .ref = res_ref };
}

fn genArrayAccess(c: *Compiler, node: Node.Index) Error!Value {
    const data = c.tree.nodes.items(.data);
    const lhs = data[node].bin.lhs;
    const rhs = data[node].bin.rhs;

    var lhs_val = try c.genNode(lhs, .value);
    if (lhs_val != .str and !lhs_val.isRt()) {
        return c.reportErr("invalid operand to subscript", lhs);
    }
    const lhs_ref = try c.makeRuntime(lhs_val);

    var rhs_val = try c.genNode(rhs, .value);
    var rhs_ref = try c.makeRuntime(rhs_val);

    const res_ref = try c.addBin(.get, lhs_ref, rhs_ref);
    return Value{ .ref = res_ref };
}

const Lval = union(enum) {
    let: *const Value,
    assign: *const Value,
    aug_assign: *Ref,
};

fn genLval(c: *Compiler, node: Node.Index, lval: Lval) Error!void {
    const ids = c.tree.nodes.items(.id);
    switch (ids[node]) {
        .paren_expr => {
            const data = c.tree.nodes.items(.data);
            return c.genLval(data[node].un, lval);
        },
        .ident_expr => try c.genLValIdent(node, lval, false),
        .mut_ident_expr => try c.genLValIdent(node, lval, true),
        .discard_expr => {
            // no op
        },
        .error_expr => try c.genLValError(node, lval),
        .range_expr,
        .range_expr_start,
        .range_expr_end,
        .range_expr_step,
        .tuple_expr,
        .tuple_expr_two,
        .list_expr,
        .list_expr_two,
        .map_expr,
        .map_expr_two,
        => @panic("TODO"),
        else => switch (lval) {
            .let => return c.reportErr("invalid left-hand side to declaration", node),
            .assign, .aug_assign => return c.reportErr("invalid left-hand side to assignment", node),
        },
    }
}

fn genLValIdent(c: *Compiler, node: Node.Index, lval: Lval, mutable: bool) Error!void {
    const tokens = c.tree.nodes.items(.token);
    switch (lval) {
        .let => |val| {
            try c.checkRedeclaration(tokens[node]);

            var ref = try c.makeRuntime(val.*);
            if (val.* == .mut or (mutable and val.isRt())) {
                // copy on assign
                ref = try c.addUn(.copy_un, ref);
            }
            const sym = Symbol{
                .name = c.tree.tokenSlice(tokens[node]),
                .ref = ref,
                .mut = mutable,
                .val = val.*,
            };
            try c.scopes.append(c.gpa, .{ .symbol = sym });
        },
        .assign => |val| {
            const sym = try c.findSymbol(tokens[node]);
            if (!sym.mut) {
                return c.reportErr("assignment to constant", node);
            }
            if (val.* == .mut) {
                _ = try c.addBin(.copy, sym.ref, val.mut);
            } else {
                _ = try c.addBin(.move, sym.ref, try c.makeRuntime(val.*));
            }
        },
        .aug_assign => |val| {
            const sym = try c.findSymbol(tokens[node]);
            if (!sym.mut) {
                return c.reportErr("assignment to constant", node);
            }
            val.* = sym.ref;
        },
    }
}

fn genLValError(c: *Compiler, node: Node.Index, lval: Lval) Error!void {
    const val = switch (lval) {
        .let, .assign => |val| val,
        .aug_assign => return c.reportErr("invalid left hand side to augmented assignment", node),
    };
    if (!val.isRt()) {
        return c.reportErr("expected an error", node);
    }
    const data = c.tree.nodes.items(.data);
    if (data[node].un == 0) {
        return c.reportErr("expected a destructuring", node);
    }
    const unwrapped = try c.addUn(.unwrap_error, val.getRt());

    const rhs_val = Value{ .ref = unwrapped };
    try c.genLval(data[node].un, switch (lval) {
        .let => .{ .let = &rhs_val },
        .assign => .{ .assign = &rhs_val },
        else => unreachable,
    });
}

fn parseStr(c: *Compiler, tok: TokenIndex) ![]u8 {
    var slice = c.tree.tokenSlice(tok);
    slice = slice[1 .. slice.len - 1];
    var buf = try c.arena.alloc(u8, slice.len);
    return buf[0..try c.parseStrExtra(tok, slice, buf)];
}

fn parseStrExtra(c: *Compiler, tok: TokenIndex, slice: []const u8, buf: []u8) !usize {
    var slice_i: u32 = 0;
    var i: u32 = 0;
    while (slice_i < slice.len) : (slice_i += 1) {
        const char = slice[slice_i];
        switch (char) {
            '\\' => {
                slice_i += 1;
                buf[i] = switch (slice[slice_i]) {
                    '\\' => '\\',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    '\'' => '\'',
                    '"' => '"',
                    'x', 'u' => return c.reportErr("TODO: more escape sequences", tok),
                    else => unreachable,
                };
            },
            else => buf[i] = char,
        }
        i += 1;
    }
    return i;
}

fn reportErr(c: *Compiler, msg: []const u8, node: Node.Index) Error {
    @setCold(true);
    const starts = c.tree.tokens.items(.start);
    try c.errors.add(.{ .data = msg }, starts[c.tree.firstToken(node)], .err);
    return error.CompileError;
}
