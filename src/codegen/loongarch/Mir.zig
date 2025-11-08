const Mir = @This();
const Instruction = @import("encoding.zig").Instruction;
const Disassemble = @import("Disassemble.zig");

prologue: []const Instruction,
body: []const Instruction,
epilogue: []const Instruction,
literals: []const u32,
nav_relocs: []const Reloc.Nav,
uav_relocs: []const Reloc.Uav,
lazy_relocs: []const Reloc.Lazy,
global_relocs: []const Reloc.Global,
literal_relocs: []const Reloc.Literal,

pub const Reloc = struct {
    label: u32,
    addend: i64 align(@alignOf(u32)) = 0,

    pub const Nav = struct {
        nav: InternPool.Nav.Index,
        reloc: Reloc,
    };

    pub const Uav = struct {
        uav: InternPool.Key.Ptr.BaseAddr.Uav,
        reloc: Reloc,
    };

    pub const Lazy = struct {
        symbol: link.File.LazySymbol,
        reloc: Reloc,
    };

    pub const Global = struct {
        name: [*:0]const u8,
        reloc: Reloc,
    };

    pub const Literal = struct {
        label: u32,
    };
};

pub fn deinit(mir: *Mir, gpa: std.mem.Allocator) void {
    // assert(mir.body.ptr + mir.body.len == mir.prologue.ptr); TODO
    // assert(mir.prologue.ptr + mir.prologue.len == mir.epilogue.ptr);
    gpa.free(mir.body.ptr[0 .. mir.body.len + mir.prologue.len + mir.epilogue.len]);
    gpa.free(mir.literals);
    gpa.free(mir.nav_relocs);
    gpa.free(mir.uav_relocs);
    gpa.free(mir.lazy_relocs);
    gpa.free(mir.global_relocs);
    gpa.free(mir.literal_relocs);
    mir.* = undefined;
}

pub fn emit(
    mir: Mir,
    lf: *link.File,
    pt: Zcu.PerThread,
    src_loc: Zcu.LazySrcLoc,
    func_index: InternPool.Index,
    atom_index: u32,
    w: *std.Io.Writer,
    debug_output: link.File.DebugInfoOutput,
) !void {
    _ = debug_output;
    const zcu = pt.zcu;
    const ip = &zcu.intern_pool;
    const func = zcu.funcInfo(func_index);
    const nav = ip.getNav(func.owner_nav);
    const mod = zcu.navFileScope(func.owner_nav).mod.?;
    const target = &mod.resolved_target.result;
    mir_log.debug("{f}:", .{nav.fqn.fmt(ip)});

    const func_align = switch (nav.status.fully_resolved.alignment) {
        .none => switch (mod.optimize_mode) {
            .Debug, .ReleaseSafe, .ReleaseFast => target_util.defaultFunctionAlignment(target),
            .ReleaseSmall => target_util.minFunctionAlignment(target),
        },
        else => |a| a.maxStrict(target_util.minFunctionAlignment(target)),
    };
    const code_len = mir.prologue.len + mir.body.len + mir.epilogue.len;
    const literals_align_gap = -%code_len & (@divExact(
        @as(u5, @intCast(func_align.minStrict(.@"16").toByteUnits().?)),
        @sizeOf(Instruction),
    ) - 1);
    try w.rebase(w.end, @sizeOf(Instruction) * (code_len + literals_align_gap + mir.literals.len));
    emitInstructionsForward(w, mir.prologue) catch unreachable;
    emitInstructionsBackward(w, mir.body) catch unreachable;
    const body_end: u32 = @intCast(w.end);
    emitInstructionsBackward(w, mir.epilogue) catch unreachable;
    w.splatByteAll(0, @sizeOf(Instruction) * literals_align_gap) catch unreachable;
    w.writeAll(@ptrCast(mir.literals)) catch unreachable;
    mir_log.debug("", .{});

    for (mir.nav_relocs) |nav_reloc| emitReloc(
        lf,
        zcu,
        atom_index,
        switch (try @import("../../codegen.zig").genNavRef(
            lf,
            pt,
            src_loc,
            nav_reloc.nav,
            &mod.resolved_target.result,
        )) {
            .sym_index => |sym_index| sym_index,
            .fail => |em| return zcu.codegenFailMsg(func.owner_nav, em),
        },
        mir.body[nav_reloc.reloc.label],
        body_end - @sizeOf(Instruction) * (1 + nav_reloc.reloc.label),
        nav_reloc.reloc.addend,
    ) catch |err|
        return zcu.codegenFail(func.owner_nav, "emit reloc failed: {t}", .{err});
    for (mir.uav_relocs) |uav_reloc| emitReloc(
        lf,
        zcu,
        atom_index,
        switch (try lf.lowerUav(
            pt,
            uav_reloc.uav.val,
            ZigType.fromInterned(uav_reloc.uav.orig_ty).ptrAlignment(zcu),
            src_loc,
        )) {
            .sym_index => |sym_index| sym_index,
            .fail => |em| return zcu.codegenFailMsg(func.owner_nav, em),
        },
        mir.body[uav_reloc.reloc.label],
        body_end - @sizeOf(Instruction) * (1 + uav_reloc.reloc.label),
        uav_reloc.reloc.addend,
    ) catch |err|
        return zcu.codegenFail(func.owner_nav, "emit reloc failed: {t}", .{err});
    for (mir.lazy_relocs) |lazy_reloc| emitReloc(
        lf,
        zcu,
        atom_index,
        if (lf.cast(.elf)) |ef|
            ef.zigObjectPtr().?.getOrCreateMetadataForLazySymbol(ef, pt, lazy_reloc.symbol) catch |err|
                return zcu.codegenFail(func.owner_nav, "{s} creating lazy symbol", .{@errorName(err)})
        else if (lf.cast(.elf2)) |elf|
            @intFromEnum(elf.lazySymbol(lazy_reloc.symbol) catch |err|
                return zcu.codegenFail(func.owner_nav, "emit lazy symbol: {t}", .{err}))
        else
            return zcu.codegenFail(func.owner_nav, "external symbols unimplemented for {s}", .{@tagName(lf.tag)}),
        mir.body[lazy_reloc.reloc.label],
        body_end - @sizeOf(Instruction) * (1 + lazy_reloc.reloc.label),
        lazy_reloc.reloc.addend,
    ) catch |err|
        return zcu.codegenFail(func.owner_nav, "emit reloc failed: {t}", .{err});
    for (mir.global_relocs) |global_reloc| emitReloc(
        lf,
        zcu,
        atom_index,
        if (lf.cast(.elf)) |ef|
            try ef.getGlobalSymbol(std.mem.span(global_reloc.name), null)
        else if (lf.cast(.elf2)) |elf| @intFromEnum(elf.globalSymbol(.{
            .name = std.mem.span(global_reloc.name),
            .type = .FUNC,
        }) catch |err|
            return zcu.codegenFail(func.owner_nav, "emit global symbol failed: {t}", .{err})) else return zcu.codegenFail(func.owner_nav, "external symbols unimplemented for {s}", .{@tagName(lf.tag)}),
        mir.body[global_reloc.reloc.label],
        body_end - @sizeOf(Instruction) * (1 + global_reloc.reloc.label),
        global_reloc.reloc.addend,
    ) catch |err|
        return zcu.codegenFail(func.owner_nav, "emit reloc failed: {t}", .{err});
    const literal_reloc_offset: i19 = @intCast(mir.epilogue.len + literals_align_gap);
    for (mir.literal_relocs) |literal_reloc| {
        var instruction = mir.body[literal_reloc.label];
        // TODO
        _ = &instruction;
        _ = literal_reloc_offset;
    }
}

fn emitInstructionsForward(w: *std.Io.Writer, instructions: []const Instruction) !void {
    for (instructions) |instruction| try emitInstruction(w, instruction);
}
fn emitInstructionsBackward(w: *std.Io.Writer, instructions: []const Instruction) !void {
    var instruction_index = instructions.len;
    while (instruction_index > 0) {
        instruction_index -= 1;
        try emitInstruction(w, instructions[instruction_index]);
    }
}
fn emitInstruction(w: *std.Io.Writer, instruction: Instruction) !void {
    mir_log.debug("    {f}", .{(Disassemble{}).fmtInstruction(instruction)});
    try w.writeInt(@FieldType(Instruction, "word"), instruction.word, .little);
}

fn emitReloc(
    lf: *link.File,
    zcu: *Zcu,
    atom_index: u32,
    sym_index: u32,
    instruction: Instruction,
    offset: u32,
    addend: i64,
) !void {
    _ = zcu;
    const mnemonic = Disassemble.decodeMnemonic(instruction) orelse unreachable;
    switch (mnemonic) {
        else => {
            mir_log.debug("unimplemented reloc on {t}", .{mnemonic});
            unreachable;
        },
        .pcaddu18i => if (lf.cast(.elf2)) |ef| {
            try ef.addReloc(@enumFromInt(atom_index), offset, @enumFromInt(sym_index), addend, .{ .LARCH = .CALL36 });
        } else unreachable,
    }
}

const Air = @import("../../Air.zig");
const assert = std.debug.assert;
const mir_log = std.log.scoped(.mir);
const InternPool = @import("../../InternPool.zig");
const link = @import("../../link.zig");
const std = @import("std");
const target_util = @import("../../target.zig");
const Zcu = @import("../../Zcu.zig");
const ZigType = @import("../../Type.zig");
