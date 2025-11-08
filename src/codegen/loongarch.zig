const Mir = @import("loongarch/Mir.zig");
const Select = @import("loongarch/Select.zig");
const Disassemble = @import("loongarch/Disassemble.zig");

comptime {
    _ = Disassemble;
}

pub fn legalizeFeatures(_: *const std.Target) ?*const Air.Legalize.Features {
    return comptime &.initMany(&.{
        .expand_intcast_safe,
        .expand_int_from_float_safe,
        .expand_int_from_float_optimized_safe,
        .expand_add_safe,
        .expand_sub_safe,
        .expand_mul_safe,
        .expand_packed_load,
        .expand_packed_store,
        .expand_packed_struct_field_val,
        .expand_packed_aggregate_init,
    });
}

pub fn generate(
    _: *link.File,
    pt: Zcu.PerThread,
    _: Zcu.LazySrcLoc,
    func_index: InternPool.Index,
    air: *const Air,
    liveness: *const ?Air.Liveness,
) !Mir {
    const zcu = pt.zcu;
    const gpa = zcu.gpa;
    const ip = &zcu.intern_pool;
    const func = zcu.funcInfo(func_index);
    const func_zir = func.zir_body_inst.resolveFull(ip).?;
    const file = zcu.fileByIndex(func_zir.file);
    const named_params_len = file.zir.?.getParamBody(func_zir.inst).len;
    const func_type = ip.indexToKey(func.ty).func_type;
    assert(liveness.* == null);

    const mod = zcu.navFileScope(func.owner_nav).mod.?;
    var isel: Select = .{
        .pt = pt,
        .target = &mod.resolved_target.result,
        .air = air.*,
        .nav_index = zcu.funcInfo(func_index).owner_nav,
    };
    defer isel.deinit();

    const air_main_body = air.getMainBody();

    var cc_it: Select.CallAbiIterator = .{ .cc = &func_type.cc, .isel = &isel };

    ret: {
        const ret_vi = try cc_it.resolve(.fromInterned(func_type.return_type), true) orelse break :ret;
        tracking_log.debug("${d} <- %main", .{@intFromEnum(ret_vi)});
        try isel.live_values.putNoClobber(gpa, Select.Block.main, ret_vi);
    }

    for (air_main_body) |air_inst_index| {
        if (air.instructions.items(.tag)[@intFromEnum(air_inst_index)] != .arg) break;
        const arg = air.instructions.items(.data)[@intFromEnum(air_inst_index)].arg;
        const param_ty = arg.ty.toType();
        const param_vi = param_vi: {
            if (arg.zir_param_index >= named_params_len)
                assert(func_type.is_var_args);
            break :param_vi try cc_it.resolve(param_ty, false);
        } orelse unreachable;
        tracking_log.debug("${d} <- %{d}", .{ @intFromEnum(param_vi), @intFromEnum(air_inst_index) });
        try isel.live_values.putNoClobber(gpa, air_inst_index, param_vi);
    }

    assert(!(try isel.blocks.getOrPut(gpa, Select.Block.main)).found_existing);
    try isel.analyze(air_main_body);
    try isel.finishAnalysis();
    isel.verify(false);

    isel.blocks.values()[0] = .{
        .live_registers = isel.live_registers,
        .target_label = @intCast(isel.instructions.items.len),
    };
    try isel.body(air_main_body);
    if (isel.live_values.fetchRemove(Select.Block.main)) |ret_vi| {
        switch (ret_vi.value.parent(&isel)) {
            .unallocated, .stack_slot => {},
            .value, .constant => unreachable,
            .address => |address_vi| try address_vi.liveIn(
                &isel,
                address_vi.hint(&isel).?,
                comptime &.initFill(.free),
            ),
        }
        ret_vi.value.deref(&isel);
    }
    isel.verify(true);

    const prologue = isel.instructions.items.len;
    const epilogue = try isel.layout(cc_it, mod);

    const instructions = try isel.instructions.toOwnedSlice(gpa);
    var mir: Mir = .{
        .prologue = instructions[prologue..epilogue],
        .body = instructions[0..prologue],
        .epilogue = instructions[epilogue..],
        .literals = &.{},
        .nav_relocs = &.{},
        .uav_relocs = &.{},
        .lazy_relocs = &.{},
        .global_relocs = &.{},
        .literal_relocs = &.{},
    };
    errdefer mir.deinit(gpa);
    mir.literals = try isel.literals.toOwnedSlice(gpa);
    mir.nav_relocs = try isel.nav_relocs.toOwnedSlice(gpa);
    mir.uav_relocs = try isel.uav_relocs.toOwnedSlice(gpa);
    mir.lazy_relocs = try isel.lazy_relocs.toOwnedSlice(gpa);
    mir.global_relocs = try isel.global_relocs.toOwnedSlice(gpa);
    mir.literal_relocs = try isel.literal_relocs.toOwnedSlice(gpa);
    return mir;
}

const Air = @import("../Air.zig");
const assert = std.debug.assert;
const InternPool = @import("../InternPool.zig");
const link = @import("../link.zig");
const std = @import("std");
const tracking_log = std.log.scoped(.tracking);
const Zcu = @import("../Zcu.zig");
