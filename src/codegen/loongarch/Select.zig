const Register = @import("bits.zig").Register;
const encoding = @import("encoding.zig");
const Instruction = encoding.Instruction;
const Mir = @import("Mir.zig");
const Disassemble = @import("Disassemble.zig");

pt: Zcu.PerThread,
target: *const std.Target,
air: Air,
nav_index: InternPool.Nav.Index,

// Wip Mir
saved_registers: std.enums.EnumSet(Register) = .initEmpty(),
instructions: std.ArrayListUnmanaged(Instruction) = .empty,
literals: std.ArrayListUnmanaged(u32) = .empty,
nav_relocs: std.ArrayListUnmanaged(Mir.Reloc.Nav) = .empty,
uav_relocs: std.ArrayListUnmanaged(Mir.Reloc.Uav) = .empty,
lazy_relocs: std.ArrayListUnmanaged(Mir.Reloc.Lazy) = .empty,
global_relocs: std.ArrayListUnmanaged(Mir.Reloc.Global) = .empty,
literal_relocs: std.ArrayListUnmanaged(Mir.Reloc.Literal) = .empty,

// Stack Frame
returns: bool = false,
stack_size: u24 = 0,
stack_align: InternPool.Alignment = .@"16",

// Value Tracking
live_registers: LiveRegisters = .initFill(.free),
live_values: std.AutoHashMapUnmanaged(Air.Inst.Index, Value.Index) = .empty,
values: std.ArrayListUnmanaged(Value) = .empty,

// Blocks
def_order: std.AutoArrayHashMapUnmanaged(Air.Inst.Index, void) = .empty,
blocks: std.AutoArrayHashMapUnmanaged(Air.Inst.Index, Block) = .empty,

pub const LiveRegisters = std.enums.EnumArray(Register, Value.Index);

pub const Block = struct {
    live_registers: LiveRegisters,
    target_label: u32,

    pub const main: Air.Inst.Index = @enumFromInt(
        std.math.maxInt(@typeInfo(Air.Inst.Index).@"enum".tag_type),
    );

    fn branch(target_block: *const Block, isel: *Select) !void {
        if (isel.instructions.items.len > target_block.target_label) {
            const offset: i26 = @intCast((isel.instructions.items.len + 1 - target_block.target_label) << 2);
            try isel.emit(.b(@intCast(offset >> 16), @truncate(offset)));
        }
        try isel.merge(&target_block.live_registers, .{});
    }
};

pub fn deinit(isel: *Select) void {
    const gpa = isel.pt.zcu.gpa;

    isel.instructions.deinit(gpa);
    isel.literals.deinit(gpa);
    isel.nav_relocs.deinit(gpa);
    isel.uav_relocs.deinit(gpa);
    isel.lazy_relocs.deinit(gpa);
    isel.global_relocs.deinit(gpa);
    isel.literal_relocs.deinit(gpa);

    isel.live_values.deinit(gpa);
    isel.values.deinit(gpa);

    isel.def_order.deinit(gpa);
    isel.blocks.deinit(gpa);

    isel.* = undefined;
}

pub const Value = struct {
    refs: u32,
    flags: Flags,
    offset_from_parent: u64,
    parent_payload: Parent.Payload,
    location_payload: Location.Payload,
    parts: Value.Index,

    /// Must be at least 16 to compute call abi.
    /// Must be at least 16, the largest hardware alignment.
    pub const max_parts = 16;
    pub const PartsLen = std.math.IntFittingRange(0, Value.max_parts);

    comptime {
        if (!std.debug.runtime_safety) assert(@sizeOf(Value) == 32);
    }

    pub const Flags = packed struct(u32) {
        alignment: InternPool.Alignment,
        parent_tag: Parent.Tag,
        location_tag: Location.Tag,
        parts_len_minus_one: std.math.IntFittingRange(0, Value.max_parts - 1),
        unused: u18 = 0,
    };

    pub const Parent = union(enum(u3)) {
        unallocated: void,
        stack_slot: Indirect,
        address: Value.Index,
        value: Value.Index,
        constant: Constant,

        pub const Tag = @typeInfo(Parent).@"union".tag_type.?;
        pub const Payload = @Type(.{ .@"union" = .{
            .layout = .auto,
            .tag_type = null,
            .fields = @typeInfo(Parent).@"union".fields,
            .decls = &.{},
        } });
    };

    pub const Location = union(enum(u1)) {
        large: struct {
            size: u64,
        },
        small: struct {
            size: u5,
            signedness: std.builtin.Signedness,
            class: Register.Class,
            modifier: Register.Modifier,
            hint: Register,
            register: Register,
        },

        pub const Tag = @typeInfo(Location).@"union".tag_type.?;
        pub const Payload = @Type(.{ .@"union" = .{
            .layout = .auto,
            .tag_type = null,
            .fields = @typeInfo(Location).@"union".fields,
            .decls = &.{},
        } });
    };

    pub const Indirect = packed struct(u32) {
        base: Register,
        offset: i25,

        pub fn withOffset(ind: Indirect, offset: i25) Indirect {
            return .{
                .base = ind.base,
                .offset = ind.offset + offset,
            };
        }
    };

    pub const Index = enum(u32) {
        allocating = std.math.maxInt(u32) - 1,
        free = std.math.maxInt(u32) - 0,
        _,

        fn get(vi: Value.Index, isel: *Select) *Value {
            return &isel.values.items[@intFromEnum(vi)];
        }

        fn setAlignment(vi: Value.Index, isel: *Select, new_alignment: InternPool.Alignment) void {
            vi.get(isel).flags.alignment = new_alignment;
        }

        pub fn alignment(vi: Value.Index, isel: *Select) InternPool.Alignment {
            return vi.get(isel).flags.alignment;
        }

        pub fn setParent(vi: Value.Index, isel: *Select, new_parent: Parent) void {
            const value = vi.get(isel);
            assert(value.flags.parent_tag == .unallocated);
            value.flags.parent_tag = new_parent;
            value.parent_payload = switch (new_parent) {
                .unallocated => unreachable,
                inline else => |payload, tag| @unionInit(Parent.Payload, @tagName(tag), payload),
            };
            if (value.refs > 0) switch (new_parent) {
                .unallocated => unreachable,
                .stack_slot, .constant => {},
                .address, .value => |parent_vi| _ = parent_vi.ref(isel),
            };
        }

        pub fn changeStackSlot(vi: Value.Index, isel: *Select, new_stack_slot: Indirect) void {
            const value = vi.get(isel);
            assert(value.flags.parent_tag == .stack_slot);
            value.flags.parent_tag = .unallocated;
            vi.setParent(isel, .{ .stack_slot = new_stack_slot });
        }

        pub fn parent(vi: Value.Index, isel: *Select) Parent {
            const value = vi.get(isel);
            return switch (value.flags.parent_tag) {
                inline else => |tag| @unionInit(
                    Parent,
                    @tagName(tag),
                    @field(value.parent_payload, @tagName(tag)),
                ),
            };
        }

        pub fn valueParent(initial_vi: Value.Index, isel: *Select) struct { u64, Value.Index } {
            var offset: u64 = 0;
            var vi = initial_vi;
            parent: switch (vi.parent(isel)) {
                else => return .{ offset, vi },
                .value => |parent_vi| {
                    offset += vi.position(isel)[0];
                    vi = parent_vi;
                    continue :parent parent_vi.parent(isel);
                },
            }
        }

        pub fn location(vi: Value.Index, isel: *Select) Location {
            const value = vi.get(isel);
            return switch (value.flags.location_tag) {
                inline else => |tag| @unionInit(
                    Location,
                    @tagName(tag),
                    @field(value.location_payload, @tagName(tag)),
                ),
            };
        }

        pub fn position(vi: Value.Index, isel: *Select) struct { u64, u64 } {
            return .{ vi.get(isel).offset_from_parent, vi.size(isel) };
        }

        pub fn size(vi: Value.Index, isel: *Select) u64 {
            return switch (vi.location(isel)) {
                inline else => |loc| loc.size,
            };
        }

        fn setHint(vi: Value.Index, isel: *Select, new_hint: Register) void {
            vi.get(isel).location_payload.small.hint = new_hint;
        }

        pub fn hint(vi: Value.Index, isel: *Select) ?Register {
            return switch (vi.location(isel)) {
                .large => null,
                .small => |loc| switch (loc.hint) {
                    Register.zero => null,
                    else => |hint_reg| hint_reg,
                },
            };
        }

        fn setSignedness(vi: Value.Index, isel: *Select, new_signedness: std.builtin.Signedness) void {
            const value = vi.get(isel);
            assert(value.location_payload.small.size <= 2);
            value.location_payload.small.signedness = new_signedness;
        }

        pub fn signedness(vi: Value.Index, isel: *Select) std.builtin.Signedness {
            const value = vi.get(isel);
            return switch (value.flags.location_tag) {
                .large => .unsigned,
                .small => value.location_payload.small.signedness,
            };
        }

        fn setRegisterClass(vi: Value.Index, isel: *Select, new_class: Register.Class) void {
            vi.get(isel).location_payload.small.class = new_class;
        }

        pub fn registerClass(vi: Value.Index, isel: *Select) Register.Class {
            const value = vi.get(isel);
            return switch (value.flags.location_tag) {
                .large => .int,
                .small => value.location_payload.small.class,
            };
        }

        fn setModifier(vi: Value.Index, isel: *Select, new_modifier: Register.Modifier) void {
            vi.get(isel).location_payload.small.modifier = new_modifier;
        }

        pub fn modifier(vi: Value.Index, isel: *Select) Register.Modifier {
            const value = vi.get(isel);
            return switch (value.flags.location_tag) {
                .large => .general,
                .small => value.location_payload.small.modifier,
            };
        }

        pub fn register(vi: Value.Index, isel: *Select) ?Register {
            return switch (vi.location(isel)) {
                .large => null,
                .small => |loc| switch (loc.register) {
                    Register.zero => null,
                    else => |reg| reg,
                },
            };
        }

        pub fn isUsed(vi: Value.Index, isel: *Select) bool {
            return vi.valueParent(isel)[1].parent(isel) != .unallocated or vi.hasRegisterRecursive(isel);
        }

        fn hasRegisterRecursive(vi: Value.Index, isel: *Select) bool {
            if (vi.register(isel)) |_| return true;
            var part_it = vi.parts(isel);
            if (part_it.only() == null) while (part_it.next()) |part_vi| if (part_vi.hasRegisterRecursive(isel)) return true;
            return false;
        }

        fn setParts(vi: Value.Index, isel: *Select, parts_len: Value.PartsLen) void {
            assert(parts_len > 1);
            const value = vi.get(isel);
            assert(value.flags.parts_len_minus_one == 0);
            value.parts = @enumFromInt(isel.values.items.len);
            value.flags.parts_len_minus_one = @intCast(parts_len - 1);
        }

        fn addPart(vi: Value.Index, isel: *Select, part_offset: u64, part_size: u64) Value.Index {
            const part_vi = isel.initValueAdvanced(vi.alignment(isel), part_offset, part_size);
            tracking_log.debug("${d} <- ${d}[{d}]", .{
                @intFromEnum(part_vi),
                @intFromEnum(vi),
                part_offset,
            });
            part_vi.setParent(isel, .{ .value = vi });
            return part_vi;
        }

        pub fn parts(vi: Value.Index, isel: *Select) Value.PartIterator {
            const value = vi.get(isel);
            return switch (value.flags.parts_len_minus_one) {
                0 => .initOne(vi),
                else => |parts_len_minus_one| .{
                    .vi = value.parts,
                    .remaining = @as(Value.PartsLen, parts_len_minus_one) + 1,
                },
            };
        }

        fn partAtOffset(vi: Value.Index, isel: *Select, offset: u64) Value.Index {
            const SearchPartIndex = std.math.IntFittingRange(0, Value.max_parts * 2 - 1);
            const value = vi.get(isel);
            var last: SearchPartIndex = value.flags.parts_len_minus_one;
            if (last == 0) return vi;
            var first: SearchPartIndex = 0;
            last += 1;
            while (true) {
                const mid = (first + last) / 2;
                const mid_vi: Value.Index = @enumFromInt(@intFromEnum(value.parts) + mid);
                if (mid == first) return mid_vi;
                if (offset < mid_vi.get(isel).offset_from_parent) last = mid else first = mid;
            }
        }

        fn field(
            vi: Value.Index,
            ty: ZigType,
            field_offset: u64,
            field_size: u64,
        ) Value.FieldPartIterator {
            assert(field_size > 0);
            return .{
                .vi = vi,
                .ty = ty,
                .field_offset = field_offset,
                .field_size = field_size,
                .next_offset = 0,
            };
        }

        fn ref(initial_vi: Value.Index, isel: *Select) Value.Index {
            var vi = initial_vi;
            while (true) {
                const refs = &vi.get(isel).refs;
                refs.* += 1;
                if (refs.* > 1) return initial_vi;
                switch (vi.parent(isel)) {
                    .unallocated, .stack_slot, .constant => {},
                    .address, .value => |parent_vi| {
                        vi = parent_vi;
                        continue;
                    },
                }
                return initial_vi;
            }
        }

        pub fn deref(initial_vi: Value.Index, isel: *Select) void {
            var vi = initial_vi;
            while (true) {
                const refs = &vi.get(isel).refs;
                refs.* -= 1;
                if (refs.* > 0) return;
                switch (vi.parent(isel)) {
                    .unallocated, .constant => {},
                    .stack_slot => {
                        // reuse stack slot
                    },
                    .address, .value => |parent_vi| {
                        vi = parent_vi;
                        continue;
                    },
                }
                return;
            }
        }

        fn move(dst_vi: Value.Index, isel: *Select, src_ref: Air.Inst.Ref) !void {
            try dst_vi.copy(
                isel,
                isel.air.typeOf(src_ref, &isel.pt.zcu.intern_pool),
                try isel.use(src_ref),
            );
        }

        fn copy(dst_vi: Value.Index, isel: *Select, ty: ZigType, src_vi: Value.Index) !void {
            try dst_vi.copyAdvanced(isel, src_vi, .{
                .ty = ty,
                .dst_vi = dst_vi,
                .dst_offset = 0,
                .src_vi = src_vi,
                .src_offset = 0,
            });
        }

        fn copyAdvanced(dst_vi: Value.Index, isel: *Select, src_vi: Value.Index, root: struct {
            ty: ZigType,
            dst_vi: Value.Index,
            dst_offset: u64,
            src_vi: Value.Index,
            src_offset: u64,
        }) !void {
            if (dst_vi == src_vi) return;
            var dst_part_it = dst_vi.parts(isel);
            if (dst_part_it.only()) |dst_part_vi| {
                var src_part_it = src_vi.parts(isel);
                if (src_part_it.only()) |src_part_vi| only: {
                    const src_part_size = src_part_vi.size(isel);
                    if (src_part_size > @as(@TypeOf(src_part_size), 8)) {
                        var subpart_it = root.src_vi.field(root.ty, root.src_offset, src_part_size - 1);
                        _ = try subpart_it.next(isel);
                        src_part_it = src_vi.parts(isel);
                        assert(src_part_it.only() == null);
                        break :only;
                    }
                    return src_part_vi.liveOut(isel, try dst_part_vi.defReg(isel) orelse return);
                }
                while (src_part_it.next()) |src_part_vi| {
                    const src_part_offset, const src_part_size = src_part_vi.position(isel);
                    var dst_field_it = root.dst_vi.field(root.ty, root.dst_offset + src_part_offset, src_part_size);
                    const dst_field_vi = try dst_field_it.only(isel);
                    try dst_field_vi.?.copyAdvanced(isel, src_part_vi, .{
                        .ty = root.ty,
                        .dst_vi = root.dst_vi,
                        .dst_offset = root.dst_offset + src_part_offset,
                        .src_vi = root.src_vi,
                        .src_offset = root.src_offset + src_part_offset,
                    });
                }
            } else while (dst_part_it.next()) |dst_part_vi| {
                const dst_part_offset, const dst_part_size = dst_part_vi.position(isel);
                var src_field_it = root.src_vi.field(root.ty, root.src_offset + dst_part_offset, dst_part_size);
                const src_part_vi = try src_field_it.only(isel);
                try dst_part_vi.copyAdvanced(isel, src_part_vi.?, .{
                    .ty = root.ty,
                    .dst_vi = root.dst_vi,
                    .dst_offset = root.dst_offset + dst_part_offset,
                    .src_vi = root.src_vi,
                    .src_offset = root.src_offset + dst_part_offset,
                });
            }
        }

        pub fn liveIn(
            vi: Value.Index,
            isel: *Select,
            src: Register,
            expected_live_registers: *const LiveRegisters,
        ) !void {
            const src_live_vi = isel.live_registers.getPtr(src);
            if (vi.register(isel)) |dst| {
                const dst_live_vi = isel.live_registers.getPtr(dst);
                assert(dst_live_vi.* == vi);
                if (dst == src) {
                    src_live_vi.* = .allocating;
                    return;
                }
                dst_live_vi.* = .allocating;
                if (try isel.fill(src)) {
                    assert(src_live_vi.* == .free);
                    src_live_vi.* = .allocating;
                }
                assert(src_live_vi.* == .allocating);
                tracking_log.debug("live in: {t} <- {t}", .{ dst, src });
                try isel.emit(switch (vi.modifier(isel)) {
                    .general => switch (src.class()) {
                        .int => .ori(dst, src, 0),
                        .fp => .@"fmov.d"(dst, src),
                        .fcc => unreachable,
                    },
                    .lsx, .lasx => return isel.fail("TODO Value.Index.liveIn SIMD", .{}),
                });
                assert(dst_live_vi.* == .allocating);
                dst_live_vi.* = switch (expected_live_registers.get(dst)) {
                    _ => .allocating,
                    .allocating => .allocating,
                    .free => .free,
                };
            } else if (try isel.fill(src)) {
                assert(src_live_vi.* == .free);
                src_live_vi.* = .allocating;
            }
            assert(src_live_vi.* == .allocating);
            vi.get(isel).location_payload.small.register = src;
        }

        pub fn defLiveIn(
            vi: Value.Index,
            isel: *Select,
            src: Register,
            expected_live_registers: *const LiveRegisters,
        ) !void {
            try vi.liveIn(isel, src, expected_live_registers);
            const offset_from_parent, const parent_vi = vi.valueParent(isel);
            switch (parent_vi.parent(isel)) {
                .unallocated => {},
                .stack_slot => |stack_slot| if (stack_slot.base != Register.fp) try isel.storeReg(
                    src,
                    vi.size(isel),
                    stack_slot.base,
                    (std.math.cast(i64, offset_from_parent) orelse unreachable) + stack_slot.offset,
                ),
                else => unreachable,
            }
            try vi.spillReg(isel, src, 0, expected_live_registers);
        }

        fn spillReg(
            vi: Value.Index,
            isel: *Select,
            src_reg: Register,
            start_offset: u64,
            expected_live_registers: *const LiveRegisters,
        ) !void {
            assert(isel.live_registers.get(src_reg) == .allocating);
            var part_it = vi.parts(isel);
            if (part_it.only()) |part_vi| {
                const dst_reg = part_vi.register(isel) orelse return;
                if (dst_reg == src_reg) return;
                const part_size = part_vi.size(isel);

                // copy src_reg[8 * start_offset, 8 * end_offset] to dst_reg
                const msbw = std.math.cast(u6, 8 * (start_offset + part_size)) orelse unreachable;
                const lsbw = std.math.cast(u6, 8 * start_offset) orelse unreachable;
                try isel.emit(.@"bstrpick.d"(dst_reg, src_reg, msbw, lsbw));

                const value_ra = &part_vi.get(isel).location_payload.small.register;
                assert(value_ra.* == dst_reg);
                value_ra.* = .zero;
                const dst_live_vi = isel.live_registers.getPtr(dst_reg);
                assert(dst_live_vi.* == part_vi);
                dst_live_vi.* = switch (expected_live_registers.get(dst_reg)) {
                    _ => .allocating,
                    .allocating => unreachable,
                    .free => .free,
                };
            } else while (part_it.next()) |part_vi| try part_vi.spillReg(
                isel,
                src_reg,
                start_offset + part_vi.get(isel).offset_from_parent,
                expected_live_registers,
            );
        }

        fn liveOut(vi: Value.Index, isel: *Select, reg: Register) !void {
            assert(try isel.fill(reg));
            const live_vi = isel.live_registers.getPtr(reg);
            assert(live_vi.* == .free);
            live_vi.* = .allocating;
            try Value.Materialize.finish(.{ .vi = vi, .reg = reg }, isel);
        }

        const MemoryAccessOptions = struct {
            root_vi: Value.Index = .free,
            offset: u64 = 0,
            @"volatile": bool = false,
            split: bool = true,
            wrap: ?std.builtin.Type.Int = null,
            expected_live_registers: *const LiveRegisters = &.initFill(.free),
        };

        fn load(
            vi: Value.Index,
            isel: *Select,
            root_ty: ZigType,
            base_reg: Register,
            opts: MemoryAccessOptions,
        ) !bool {
            const root_vi = switch (opts.root_vi) {
                _ => |root_vi| root_vi,
                .allocating => unreachable,
                .free => vi,
            };
            var part_it = vi.parts(isel);
            if (part_it.only()) |part_vi| {
                const part_size = part_vi.size(isel);
                // const part_is_vector = part_vi.isVector(isel);
                // if (part_size > @as(@TypeOf(part_size), if (part_is_vector) 16 else 8)) {
                //     if (!opts.split) return false;
                //     var subpart_it = root_vi.field(root_ty, opts.offset, part_size - 1);
                //     _ = try subpart_it.next(isel);
                //     part_it = vi.parts(isel);
                //     assert(part_it.only() == null);
                //     break :only;
                // }
                const part_reg = if (try part_vi.defReg(isel)) |part_reg|
                    part_reg
                else if (opts.@"volatile")
                    Register.zero
                else
                    return false;
                if (part_reg != Register.zero) {
                    const live_vi = isel.live_registers.getPtr(part_reg);
                    assert(live_vi.* == .free);
                    live_vi.* = .allocating;
                }
                if (opts.wrap) |int_info| switch (int_info.bits) {
                    else => unreachable,
                    1...7, 9...15, 17...31 => |bits| try isel.emit(.@"bstrpick.w"(part_reg, part_reg, @intCast(bits - 1), 0)),
                    8, 16, 32 => {},
                    33...63 => |bits| try isel.emit(.@"bstrpick.d"(part_reg, part_reg, @intCast(bits - 1), 0)),
                    64 => {},
                };
                try isel.loadReg(part_reg, part_size, part_vi.signedness(isel), base_reg, @intCast(opts.offset));
                if (part_reg != Register.zero) {
                    const live_vi = isel.live_registers.getPtr(part_reg);
                    assert(live_vi.* == .allocating);
                    switch (opts.expected_live_registers.get(part_reg)) {
                        _ => {},
                        .allocating => unreachable,
                        .free => live_vi.* = .free,
                    }
                }
                return true;
            }
            var used = false;
            while (part_it.next()) |part_vi| used |= try part_vi.load(isel, root_ty, base_reg, .{
                .root_vi = root_vi,
                .offset = opts.offset + part_vi.get(isel).offset_from_parent,
                .@"volatile" = opts.@"volatile",
                .split = opts.split,
                .wrap = switch (part_it.remaining) {
                    else => null,
                    0 => if (opts.wrap) |wrap| .{
                        .signedness = wrap.signedness,
                        .bits = @intCast(wrap.bits - 8 * part_vi.position(isel)[0]),
                    } else null,
                },
                .expected_live_registers = opts.expected_live_registers,
            });
            return used;
        }

        fn store(
            vi: Value.Index,
            isel: *Select,
            root_ty: ZigType,
            base_reg: Register,
            opts: MemoryAccessOptions,
        ) !void {
            const root_vi = switch (opts.root_vi) {
                _ => |root_vi| root_vi,
                .allocating => unreachable,
                .free => vi,
            };
            var part_it = vi.parts(isel);
            if (part_it.only()) |part_vi| {
                const part_size = part_vi.size(isel);
                // const part_is_vector = part_vi.isVector(isel);
                // if (part_size > @as(@TypeOf(part_size), if (part_is_vector) 16 else 8)) {
                //     if (!opts.split) return;
                //     var subpart_it = root_vi.field(root_ty, opts.offset, part_size - 1);
                //     _ = try subpart_it.next(isel);
                //     part_it = vi.parts(isel);
                //     assert(part_it.only() == null);
                //     break :only;
                // }
                const part_mat = try part_vi.matReg(isel);
                try isel.storeReg(part_mat.reg, part_size, base_reg, @intCast(opts.offset));
                return part_mat.finish(isel);
            }
            while (part_it.next()) |part_vi| try part_vi.store(isel, root_ty, base_reg, .{
                .root_vi = root_vi,
                .offset = opts.offset + part_vi.get(isel).offset_from_parent,
                .@"volatile" = opts.@"volatile",
                .split = opts.split,
                .wrap = switch (part_it.remaining) {
                    else => null,
                    0 => if (opts.wrap) |wrap| .{
                        .signedness = wrap.signedness,
                        .bits = @intCast(wrap.bits - 8 * part_vi.position(isel)[0]),
                    } else null,
                },
                .expected_live_registers = opts.expected_live_registers,
            });
        }

        fn matReg(vi: Value.Index, isel: *Select) !Value.Materialize {
            const mat_reg = mat_reg: {
                if (vi.register(isel)) |mat_reg| {
                    vi.get(isel).location_payload.small.register = .zero;
                    const live_vi = isel.live_registers.getPtr(mat_reg);
                    assert(live_vi.* == vi);
                    live_vi.* = .allocating;
                    break :mat_reg mat_reg;
                }
                if (vi.hint(isel)) |hint_reg| {
                    const live_vi = isel.live_registers.getPtr(hint_reg);
                    if (live_vi.* == .free) {
                        live_vi.* = .allocating;
                        isel.saved_registers.insert(hint_reg);
                        break :mat_reg hint_reg;
                    }
                }
                break :mat_reg switch (vi.modifier(isel)) {
                    .general => try isel.allocReg(vi.registerClass(isel)),
                    else => |vi_mod| return isel.fail("unimplemented matReg {t}", .{vi_mod}),
                };
            };
            assert(isel.live_registers.get(mat_reg) == .allocating);
            return .{ .vi = vi, .reg = mat_reg };
        }

        fn defReg(def_vi: Value.Index, isel: *Select) !?Register {
            var vi = def_vi;
            var offset: i64 = 0;
            var def_reg: ?Register = null;
            while (true) {
                if (vi.register(isel)) |reg| {
                    vi.get(isel).location_payload.small.register = .zero;
                    const live_vi = isel.live_registers.getPtr(reg);
                    assert(live_vi.* == vi);
                    if (def_reg == null and vi != def_vi) {
                        var part_it = vi.parts(isel);
                        assert(part_it.only() == null);

                        const first_part_vi = part_it.next().?;
                        const first_part_value = first_part_vi.get(isel);
                        assert(first_part_value.offset_from_parent == 0);
                        first_part_value.location_payload.small.register = reg;
                        live_vi.* = first_part_vi;

                        const vi_size = vi.size(isel);
                        while (part_it.next()) |part_vi| {
                            const part_offset, const part_size = part_vi.position(isel);
                            const part_mat = try part_vi.matReg(isel);
                            switch (part_vi.registerClass(isel)) {
                                .int => {
                                    switch (vi_size) {
                                        else => unreachable,
                                        1...4 => try isel.emit(.@"bstrpick.w"(
                                            reg,
                                            part_mat.reg,
                                            @truncate(32 - 8 * part_offset),
                                            @intCast(8 * part_size - 1),
                                        )),
                                        5...8 => try isel.emit(.@"bstrpick.d"(
                                            reg,
                                            part_mat.reg,
                                            @truncate(64 - 8 * part_offset),
                                            @intCast(8 * part_size - 1),
                                        )),
                                    }
                                },
                                else => return isel.fail("unimplemented defReg vector", .{}),
                            }
                            try part_mat.finish(isel);
                        }
                        vi = def_vi;
                        offset = 0;
                        continue;
                    }
                    live_vi.* = .free;
                    def_reg = reg;
                }
                offset += @intCast(vi.get(isel).offset_from_parent);
                switch (vi.parent(isel)) {
                    else => unreachable,
                    .unallocated => return def_reg,
                    .stack_slot => |stack_slot| {
                        offset += stack_slot.offset;
                        const reg = def_reg orelse try isel.allocReg(vi.registerClass(isel));
                        defer if (def_reg == null) isel.freeReg(reg);
                        try isel.storeReg(reg, def_vi.size(isel), stack_slot.base, offset);
                        return reg;
                    },
                    .value => |parent_vi| vi = parent_vi,
                }
            }
        }

        /// Moves the address of `initial_vi` to `ptr_reg`, adding `initial_offset`.
        fn address(initial_vi: Value.Index, isel: *Select, initial_offset: u64, ptr_reg: Register) !void {
            var vi = initial_vi;
            var offset: i65 = vi.get(isel).offset_from_parent + initial_offset;
            parent: switch (vi.parent(isel)) {
                .unallocated => {
                    const stack_slot = vi.allocStackSlot(isel);
                    vi.setParent(isel, .{ .stack_slot = stack_slot });
                    continue :parent .{ .stack_slot = stack_slot };
                },
                .stack_slot => |stack_slot| {
                    offset += stack_slot.offset;
                    if (offset == 0)
                        return try isel.emit(.ori(ptr_reg, stack_slot.base, 0));
                    if (std.math.cast(i12, offset)) |off12|
                        return try isel.emit(.@"addi.d"(ptr_reg, stack_slot.base, off12));
                    if ((offset & 0xffff) == 0) if (std.math.cast(i32, offset)) |off32|
                        return try isel.emit(.@"addu16i.d"(ptr_reg, stack_slot.base, @intCast(off32 >> 16)));

                    const offset_reg = try isel.allocReg(.int);
                    defer isel.freeReg(offset_reg);
                    if (offset > 0) {
                        try isel.emit(.@"add.d"(ptr_reg, stack_slot.base, offset_reg));
                        try isel.moveImm(offset_reg, @intCast(offset));
                    } else {
                        try isel.emit(.@"sub.d"(ptr_reg, stack_slot.base, offset_reg));
                        try isel.moveImm(offset_reg, @intCast(-offset));
                    }
                },
                .address => |address_vi| try address_vi.liveOut(isel, ptr_reg),
                .value => |parent_vi| {
                    vi = parent_vi;
                    offset += vi.get(isel).offset_from_parent;
                    continue :parent vi.parent(isel);
                },
                .constant => |constant| {
                    const pt = isel.pt;
                    const zcu = pt.zcu;

                    try isel.uav_relocs.append(zcu.gpa, .{
                        .uav = .{
                            .val = constant.toIntern(),
                            .orig_ty = (try pt.singleConstPtrType(constant.typeOf(zcu))).toIntern(),
                        },
                        .reloc = .{
                            .label = @intCast(isel.instructions.items.len),
                            .addend = @intCast(offset),
                        },
                    });
                    try isel.emit(.@"addi.d"(ptr_reg, ptr_reg, 0));
                    try isel.uav_relocs.append(zcu.gpa, .{
                        .uav = .{
                            .val = constant.toIntern(),
                            .orig_ty = (try pt.singleConstPtrType(constant.typeOf(zcu))).toIntern(),
                        },
                        .reloc = .{
                            .label = @intCast(isel.instructions.items.len),
                            .addend = @intCast(offset),
                        },
                    });
                    try isel.emit(.pcaddu12i(ptr_reg, 0));
                },
            }
        }

        /// Allocates a stack slot with the size and alignment of this vi.
        fn allocStackSlot(vi: Value.Index, isel: *Select) Value.Indirect {
            const offset = vi.alignment(isel).forward(isel.stack_size);
            isel.stack_size = @intCast(offset + vi.size(isel));
            tracking_log.debug("${d} -> [sp, #0x{x}]", .{ @intFromEnum(vi), @abs(offset) });
            return .{
                .base = .sp,
                .offset = @intCast(offset),
            };
        }
    };

    pub const PartIterator = struct {
        vi: Value.Index,
        remaining: Value.PartsLen,

        fn initOne(vi: Value.Index) PartIterator {
            return .{ .vi = vi, .remaining = 1 };
        }

        pub fn next(it: *PartIterator) ?Value.Index {
            if (it.remaining == 0) return null;
            it.remaining -= 1;
            defer it.vi = @enumFromInt(@intFromEnum(it.vi) + 1);
            return it.vi;
        }

        pub fn peek(it: PartIterator) ?Value.Index {
            var it_mut = it;
            return it_mut.next();
        }

        pub fn only(it: PartIterator) ?Value.Index {
            return if (it.remaining == 1) it.vi else null;
        }
    };

    const FieldPartIterator = struct {
        vi: Value.Index,
        ty: ZigType,
        field_offset: u64,
        field_size: u64,
        next_offset: u64,

        fn next(it: *FieldPartIterator, isel: *Select) !?struct { offset: u64, vi: Value.Index } {
            const next_offset = it.next_offset;
            const next_part_size = it.field_size - next_offset;
            if (next_part_size == 0) return null;
            var next_part_offset = it.field_offset + next_offset;

            const zcu = isel.pt.zcu;
            const ip = &zcu.intern_pool;
            var vi = it.vi;
            var ty = it.ty;
            var ty_size = vi.size(isel);
            assert(ty_size == ty.abiSize(zcu));
            var offset: u64 = 0;
            var size = ty_size;
            assert(next_part_offset + next_part_size <= size);
            while (next_part_offset > 0 or next_part_size < size) {
                const part_vi = vi.partAtOffset(isel, next_part_offset);
                if (part_vi != vi) {
                    vi = part_vi;
                    const part_offset, size = part_vi.position(isel);
                    assert(part_offset <= next_part_offset and part_offset + size > next_part_offset);
                    offset += part_offset;
                    next_part_offset -= part_offset;
                    continue;
                }
                try isel.values.ensureUnusedCapacity(zcu.gpa, Value.max_parts);
                type_key: switch (ip.indexToKey(ty.toIntern())) {
                    else => return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)}),
                    .int_type => |int_type| switch (int_type.bits) {
                        0 => unreachable,
                        1...64 => unreachable,
                        65...256 => |bits| if (offset == 0 and size == ty_size) {
                            const parts_len = std.math.divCeil(u16, bits, 64) catch unreachable;
                            vi.setParts(isel, @intCast(parts_len));
                            for (0..parts_len) |part_index| _ = vi.addPart(isel, 8 * part_index, 8);
                        },
                        else => return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)}),
                    },
                    .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
                        .one, .many, .c => unreachable,
                        .slice => if (offset == 0 and size == ty_size) {
                            vi.setParts(isel, 2);
                            _ = vi.addPart(isel, 0, 8);
                            _ = vi.addPart(isel, 8, 8);
                        } else unreachable,
                    },
                    .opt_type => |child_type| if (ty.optionalReprIsPayload(zcu)) continue :type_key ip.indexToKey(child_type) else {
                        const child_ty: ZigType = .fromInterned(child_type);
                        const child_size = child_ty.abiSize(zcu);
                        if (offset == 0 and size == child_size) {
                            ty = child_ty;
                            ty_size = child_size;
                            continue :type_key ip.indexToKey(child_type);
                        }
                        switch (child_size) {
                            0...8, 16 => if (offset == 0 and size == ty_size) {
                                vi.setParts(isel, 2);
                                _ = vi.addPart(isel, 0, child_size);
                                _ = vi.addPart(isel, child_size, 1);
                            } else unreachable,
                            9...15 => if (offset == 0 and size == ty_size) {
                                vi.setParts(isel, 2);
                                _ = vi.addPart(isel, 0, 8);
                                _ = vi.addPart(isel, 8, ty_size - 8);
                            } else if (offset == 8 and size == ty_size - 8) {
                                vi.setParts(isel, 2);
                                _ = vi.addPart(isel, 0, child_size - 8);
                                _ = vi.addPart(isel, child_size - 8, 1);
                            } else unreachable,
                            else => return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)}),
                        }
                    },
                    .array_type => return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)}),
                    .anyframe_type => unreachable,
                    .error_union_type => return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)}),
                    .simple_type => |simple_type| switch (simple_type) {
                        .f16, .f32, .f64, .f128, .c_longdouble => return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)}),
                        .f80 => continue :type_key .{ .int_type = .{ .signedness = .unsigned, .bits = 80 } },
                        .usize,
                        .isize,
                        .c_char,
                        .c_short,
                        .c_ushort,
                        .c_int,
                        .c_uint,
                        .c_long,
                        .c_ulong,
                        .c_longlong,
                        .c_ulonglong,
                        => continue :type_key .{ .int_type = ty.intInfo(zcu) },
                        .anyopaque,
                        .void,
                        .type,
                        .comptime_int,
                        .comptime_float,
                        .noreturn,
                        .null,
                        .undefined,
                        .enum_literal,
                        .adhoc_inferred_error_set,
                        .generic_poison,
                        => unreachable,
                        .bool => continue :type_key .{ .int_type = .{ .signedness = .unsigned, .bits = 1 } },
                        .anyerror => continue :type_key .{ .int_type = .{
                            .signedness = .unsigned,
                            .bits = zcu.errorSetBits(),
                        } },
                    },
                    .struct_type => {
                        const loaded_struct = ip.loadStructType(ty.toIntern());
                        switch (loaded_struct.layout) {
                            .auto, .@"extern" => {},
                            .@"packed" => continue :type_key .{
                                .int_type = ip.indexToKey(loaded_struct.backingIntTypeUnordered(ip)).int_type,
                            },
                        }
                        const min_part_log2_stride: u5 = if (size > 16) 4 else if (size > 8) 3 else 0;
                        if (loaded_struct.field_types.len > Value.max_parts and
                            (std.math.divCeil(u64, size, @as(u64, 1) << min_part_log2_stride) catch unreachable) > Value.max_parts)
                            return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)});
                        const alignment = vi.alignment(isel);
                        const Part = struct { offset: u64, size: u64, signedness: ?std.builtin.Signedness };
                        var parts: [Value.max_parts]Part = undefined;
                        var parts_len: Value.PartsLen = 0;
                        var field_end: u64 = 0;
                        var field_it = loaded_struct.iterateRuntimeOrder(ip);
                        while (field_it.next()) |field_index| {
                            const field_ty: ZigType = .fromInterned(loaded_struct.field_types.get(ip)[field_index]);
                            const field_begin = switch (loaded_struct.fieldAlign(ip, field_index)) {
                                .none => field_ty.abiAlignment(zcu),
                                else => |field_align| field_align,
                            }.forward(field_end);
                            if (field_begin >= offset + size) break;
                            const field_size = field_ty.abiSize(zcu);
                            field_end = field_begin + field_size;
                            if (field_end <= offset) continue;
                            if (offset >= field_begin and offset + size <= field_begin + field_size) {
                                ty = field_ty;
                                ty_size = field_size;
                                offset -= field_begin;
                                continue :type_key ip.indexToKey(field_ty.toIntern());
                            }
                            const field_signedness = if (field_ty.isAbiInt(zcu)) field_signedness: {
                                const field_int_info = field_ty.intInfo(zcu);
                                break :field_signedness if (field_int_info.bits <= 16) field_int_info.signedness else null;
                            } else null;
                            if (parts_len > 0) combine: {
                                const prev_part = &parts[parts_len - 1];
                                const combined_size = field_end - prev_part.offset;
                                if (combined_size > @as(u64, 1) << @min(
                                    min_part_log2_stride,
                                    alignment.toLog2Units(),
                                    @ctz(prev_part.offset),
                                )) break :combine;
                                prev_part.size = combined_size;
                                prev_part.signedness = null;
                                continue;
                            }
                            parts[parts_len] = .{
                                .offset = field_begin,
                                .size = field_size,
                                .signedness = field_signedness,
                            };
                            parts_len += 1;
                        }
                        vi.setParts(isel, parts_len);
                        for (parts[0..parts_len]) |part| {
                            const subpart_vi = vi.addPart(isel, part.offset - offset, part.size);
                            if (part.signedness) |signedness| subpart_vi.setSignedness(isel, signedness);
                        }
                    },
                    .tuple_type => |tuple_type| {
                        const min_part_log2_stride: u5 = if (size > 16) 4 else if (size > 8) 3 else 0;
                        if (tuple_type.types.len > Value.max_parts and
                            (std.math.divCeil(u64, size, @as(u64, 1) << min_part_log2_stride) catch unreachable) > Value.max_parts)
                            return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)});
                        const alignment = vi.alignment(isel);
                        const Part = struct { offset: u64, size: u64 };
                        var parts: [Value.max_parts]Part = undefined;
                        var parts_len: Value.PartsLen = 0;
                        var field_end: u64 = 0;
                        for (tuple_type.types.get(ip), tuple_type.values.get(ip)) |field_type, field_value| {
                            if (field_value != .none) continue;
                            const field_ty: ZigType = .fromInterned(field_type);
                            const field_begin = field_ty.abiAlignment(zcu).forward(field_end);
                            if (field_begin >= offset + size) break;
                            const field_size = field_ty.abiSize(zcu);
                            if (field_size == 0) continue;
                            field_end = field_begin + field_size;
                            if (field_end <= offset) continue;
                            if (offset >= field_begin and offset + size <= field_begin + field_size) {
                                ty = field_ty;
                                ty_size = field_size;
                                offset -= field_begin;
                                continue :type_key ip.indexToKey(field_ty.toIntern());
                            }
                            if (parts_len > 0) combine: {
                                const prev_part = &parts[parts_len - 1];
                                const combined_size = field_end - prev_part.offset;
                                if (combined_size > @as(u64, 1) << @min(
                                    min_part_log2_stride,
                                    alignment.toLog2Units(),
                                    @ctz(prev_part.offset),
                                )) break :combine;
                                prev_part.size = combined_size;
                                continue;
                            }
                            parts[parts_len] = .{ .offset = field_begin, .size = field_size };
                            parts_len += 1;
                        }
                        vi.setParts(isel, parts_len);
                        for (parts[0..parts_len]) |part| {
                            const subpart_vi = vi.addPart(isel, part.offset - offset, part.size);
                            _ = subpart_vi;
                        }
                    },
                    .union_type => {
                        const loaded_union = ip.loadUnionType(ty.toIntern());
                        switch (loaded_union.flagsUnordered(ip).layout) {
                            .auto, .@"extern" => {},
                            .@"packed" => continue :type_key .{ .int_type = .{
                                .signedness = .unsigned,
                                .bits = @intCast(ty.bitSize(zcu)),
                            } },
                        }
                        const min_part_log2_stride: u5 = if (size > 16) 4 else if (size > 8) 3 else 0;
                        if ((std.math.divCeil(u64, size, @as(u64, 1) << min_part_log2_stride) catch unreachable) > Value.max_parts)
                            return isel.fail("Value.FieldPartIterator.next({f})", .{isel.fmtType(ty)});
                        const union_layout = ZigType.getUnionLayout(loaded_union, zcu);
                        const alignment = vi.alignment(isel);
                        const tag_offset = union_layout.tagOffset();
                        const payload_offset = union_layout.payloadOffset();
                        const Part = struct { offset: u64, size: u64, signedness: ?std.builtin.Signedness };
                        var parts: [2]Part = undefined;
                        var parts_len: Value.PartsLen = 0;
                        var field_end: u64 = 0;
                        for (0..2) |field_index| {
                            const field: enum { tag, payload } = switch (field_index) {
                                0 => if (tag_offset < payload_offset) .tag else .payload,
                                1 => if (tag_offset < payload_offset) .payload else .tag,
                                else => unreachable,
                            };
                            const field_size, const field_begin = switch (field) {
                                .tag => .{ union_layout.tag_size, tag_offset },
                                .payload => .{ union_layout.payload_size, payload_offset },
                            };
                            if (field_begin >= offset + size) break;
                            if (field_size == 0) continue;
                            field_end = field_begin + field_size;
                            if (field_end <= offset) continue;
                            const field_signedness = field_signedness: switch (field) {
                                .tag => {
                                    if (offset >= field_begin and offset + size <= field_begin + field_size) {
                                        ty = .fromInterned(loaded_union.enum_tag_ty);
                                        ty_size = field_size;
                                        offset -= field_begin;
                                        continue :type_key ip.indexToKey(loaded_union.enum_tag_ty);
                                    }
                                    break :field_signedness ip.indexToKey(loaded_union.loadTagType(ip).tag_ty).int_type.signedness;
                                },
                                .payload => null,
                            };
                            if (parts_len > 0) combine: {
                                const prev_part = &parts[parts_len - 1];
                                const combined_size = field_end - prev_part.offset;
                                if (combined_size > @as(u64, 1) << @min(
                                    min_part_log2_stride,
                                    alignment.toLog2Units(),
                                    @ctz(prev_part.offset),
                                )) break :combine;
                                prev_part.size = combined_size;
                                prev_part.signedness = null;
                                continue;
                            }
                            parts[parts_len] = .{
                                .offset = field_begin,
                                .size = field_size,
                                .signedness = field_signedness,
                            };
                            parts_len += 1;
                        }
                        vi.setParts(isel, parts_len);
                        for (parts[0..parts_len]) |part| {
                            const subpart_vi = vi.addPart(isel, part.offset - offset, part.size);
                            if (part.signedness) |signedness| subpart_vi.setSignedness(isel, signedness);
                        }
                    },
                    .opaque_type, .func_type => continue :type_key .{ .simple_type = .anyopaque },
                    .enum_type => continue :type_key ip.indexToKey(ip.loadEnumType(ty.toIntern()).tag_ty),
                    .error_set_type,
                    .inferred_error_set_type,
                    => continue :type_key .{ .simple_type = .anyerror },
                }
            }
            it.next_offset = next_offset + size;
            return .{ .offset = next_part_offset - next_offset, .vi = vi };
        }

        fn only(it: *FieldPartIterator, isel: *Select) !?Value.Index {
            const part = try it.next(isel);
            assert(part.?.offset == 0);
            return if (try it.next(isel)) |_| null else part.?.vi;
        }
    };

    const Materialize = struct {
        vi: Value.Index,
        reg: Register,

        fn finish(mat: Value.Materialize, isel: *Select) error{ OutOfMemory, CodegenFail }!void {
            const live_vi = isel.live_registers.getPtr(mat.reg);
            assert(live_vi.* == .allocating);
            var vi = mat.vi;
            var offset: u64 = 0;
            const size = mat.vi.size(isel);
            free: while (true) {
                if (vi.register(isel)) |reg| {
                    if (reg != mat.reg) {
                        if (vi == mat.vi) switch (vi.registerClass(isel)) {
                            .int => try isel.emit(.ori(reg, mat.reg, 0)),
                            else => return isel.fail("unimplemented finished mat non-int reg to reg copy", .{}),
                        } else {
                            const msbw = std.math.cast(u6, 8 * (offset + size)) orelse unreachable;
                            const lsbw = std.math.cast(u6, 8 * offset) orelse unreachable;
                            try isel.emit(.@"bstrpick.d"(reg, mat.reg, msbw, lsbw));
                        }
                        break :free;
                    }
                    mat.vi.get(isel).location_payload.small.register = mat.reg;
                    live_vi.* = mat.vi;
                    return;
                }
                offset += vi.get(isel).offset_from_parent;
                switch (vi.parent(isel)) {
                    .unallocated => {
                        mat.vi.get(isel).location_payload.small.register = mat.reg;
                        live_vi.* = mat.vi;
                        return;
                    },
                    .value => |parent_vi| vi = parent_vi,
                    .constant => |initial_constant| {
                        const zcu = isel.pt.zcu;
                        const ip = &zcu.intern_pool;
                        var constant = initial_constant.toIntern();
                        var constant_key = ip.indexToKey(constant);
                        while (true) {
                            constant_key: switch (constant_key) {
                                .int_type,
                                .ptr_type,
                                .array_type,
                                .vector_type,
                                .opt_type,
                                .anyframe_type,
                                .error_union_type,
                                .simple_type,
                                .struct_type,
                                .tuple_type,
                                .union_type,
                                .opaque_type,
                                .enum_type,
                                .func_type,
                                .error_set_type,
                                .inferred_error_set_type,

                                .enum_literal,
                                .empty_enum_value,
                                .memoized_call,
                                => unreachable, // not a runtime value
                                .undef => break :free switch (vi.registerClass(isel)) {
                                    .int => try isel.emit(.ori(mat.reg, .zero, 0xaaa)),
                                    .fp => switch (vi.modifier(isel)) {
                                        .general => switch (isel.target.cpu.arch) {
                                            .loongarch32 => {
                                                try isel.emit(.@"movgr2frh.w"(mat.reg, .zero));
                                                try isel.emit(.@"movgr2fr.w"(mat.reg, .zero));
                                            },
                                            .loongarch64 => try isel.emit(.@"movgr2fr.d"(mat.reg, .zero)),
                                            else => unreachable,
                                        },
                                        else => return isel.fail("vector unimplemented", .{}),
                                    },
                                    .fcc => try isel.emit(.@"fcmp.caf.d"(mat.reg, .f0, .f0)),
                                },
                                .simple_value => |simple_value| switch (simple_value) {
                                    .undefined, .void, .null, .empty_tuple, .@"unreachable" => unreachable,
                                    .true => continue :constant_key .{ .int = .{
                                        .ty = .bool_type,
                                        .storage = .{ .u64 = 1 },
                                    } },
                                    .false => continue :constant_key .{ .int = .{
                                        .ty = .bool_type,
                                        .storage = .{ .u64 = 0 },
                                    } },
                                },
                                .int => |int| break :free storage: switch (int.storage) {
                                    .u64 => |imm| try isel.moveImm(mat.reg, @bitCast(std.math.shr(u64, imm, 8 * offset))),
                                    .i64 => |imm| switch (size) {
                                        else => unreachable,
                                        1...4 => try isel.moveImm(mat.reg, @as(u32, @bitCast(@as(i32, @truncate(std.math.shr(i64, imm, 8 * offset)))))),
                                        5...8 => try isel.moveImm(mat.reg, @bitCast(std.math.shr(i64, imm, 8 * offset))),
                                    },
                                    .big_int => |big_int| {
                                        assert(size == 8);
                                        var imm: u64 = 0;
                                        const limb_bits = @bitSizeOf(std.math.big.Limb);
                                        const limbs = @divExact(64, limb_bits);
                                        var limb_index: usize = @intCast(@divExact(offset, @divExact(limb_bits, 8)) + limbs);
                                        for (0..limbs) |_| {
                                            limb_index -= 1;
                                            if (limb_index >= big_int.limbs.len) continue;
                                            if (limb_bits < 64) imm <<= limb_bits;
                                            imm |= big_int.limbs[limb_index];
                                        }
                                        if (!big_int.positive) {
                                            limb_index = @min(limb_index, big_int.limbs.len);
                                            imm = while (limb_index > 0) {
                                                limb_index -= 1;
                                                if (big_int.limbs[limb_index] != 0) break ~imm;
                                            } else -%imm;
                                        }
                                        try isel.moveImm(mat.reg, @bitCast(imm));
                                    },
                                    .lazy_align => |ty| continue :storage .{ .u64 = ZigType.fromInterned(ty).abiAlignment(zcu).toByteUnits().? },
                                    .lazy_size => |ty| continue :storage .{ .u64 = ZigType.fromInterned(ty).abiSize(zcu) },
                                },
                                .err => |err| continue :constant_key .{ .int = .{
                                    .ty = err.ty,
                                    .storage = .{ .u64 = ip.getErrorValueIfExists(err.name).? },
                                } },
                                .error_union => |error_union| {
                                    const error_union_type = ip.indexToKey(error_union.ty).error_union_type;
                                    const error_set_ty: ZigType = .fromInterned(error_union_type.error_set_type);
                                    const payload_ty: ZigType = .fromInterned(error_union_type.payload_type);
                                    const error_set_offset = codegen.errUnionErrorOffset(payload_ty, zcu);
                                    const error_set_size = error_set_ty.abiSize(zcu);
                                    if (offset >= error_set_offset and offset + size <= error_set_offset + error_set_size) {
                                        offset -= error_set_offset;
                                        continue :constant_key switch (error_union.val) {
                                            .err_name => |err_name| .{ .err = .{
                                                .ty = error_union_type.error_set_type,
                                                .name = err_name,
                                            } },
                                            .payload => .{ .int = .{
                                                .ty = error_union_type.error_set_type,
                                                .storage = .{ .u64 = 0 },
                                            } },
                                        };
                                    }
                                    const payload_offset = codegen.errUnionPayloadOffset(payload_ty, zcu);
                                    const payload_size = payload_ty.abiSize(zcu);
                                    if (offset >= payload_offset and offset + size <= payload_offset + payload_size) {
                                        offset -= payload_offset;
                                        switch (error_union.val) {
                                            .err_name => continue :constant_key .{ .undef = error_union_type.payload_type },
                                            .payload => |payload| {
                                                constant = payload;
                                                constant_key = ip.indexToKey(constant);
                                                continue :constant_key constant_key;
                                            },
                                        }
                                    }
                                },
                                .enum_tag => |enum_tag| continue :constant_key .{ .int = ip.indexToKey(enum_tag.int).int },
                                .float => return isel.fail("float unimplemented", .{}),
                                .ptr => |ptr| {
                                    assert(offset == 0 and size == 8);
                                    break :free switch (ptr.base_addr) {
                                        .nav => |nav| if (ZigType.fromInterned(ip.getNav(nav).typeOf(ip)).isFnOrHasRuntimeBits(zcu)) {
                                            try isel.nav_relocs.append(zcu.gpa, .{
                                                .nav = nav,
                                                .reloc = .{
                                                    .label = @intCast(isel.instructions.items.len),
                                                    .addend = @intCast(ptr.byte_offset),
                                                },
                                            });
                                            try isel.emit(.@"addi.d"(mat.reg, mat.reg, 0));
                                            try isel.nav_relocs.append(zcu.gpa, .{
                                                .nav = nav,
                                                .reloc = .{
                                                    .label = @intCast(isel.instructions.items.len),
                                                    .addend = @intCast(ptr.byte_offset),
                                                },
                                            });
                                            try isel.emit(.pcaddu12i(mat.reg, 0));
                                        } else continue :constant_key .{ .int = .{
                                            .ty = .usize_type,
                                            .storage = .{ .u64 = isel.pt.navAlignment(nav).forward(0xaaaaaaaaaaaaaaaa) },
                                        } },
                                        .uav => |uav| if (ZigType.fromInterned(ip.typeOf(uav.val)).isFnOrHasRuntimeBits(zcu)) {
                                            try isel.uav_relocs.append(zcu.gpa, .{
                                                .uav = uav,
                                                .reloc = .{
                                                    .label = @intCast(isel.instructions.items.len),
                                                    .addend = @intCast(ptr.byte_offset),
                                                },
                                            });
                                            try isel.emit(.@"addi.d"(mat.reg, mat.reg, 0));
                                            try isel.uav_relocs.append(zcu.gpa, .{
                                                .uav = uav,
                                                .reloc = .{
                                                    .label = @intCast(isel.instructions.items.len),
                                                    .addend = @intCast(ptr.byte_offset),
                                                },
                                            });
                                            try isel.emit(.pcaddu12i(mat.reg, 0));
                                        } else continue :constant_key .{ .int = .{
                                            .ty = .usize_type,
                                            .storage = .{ .u64 = ZigType.fromInterned(uav.orig_ty).ptrAlignment(zcu).forward(0xaaaaaaaaaaaaaaaa) },
                                        } },
                                        .int => continue :constant_key .{ .int = .{
                                            .ty = .usize_type,
                                            .storage = .{ .u64 = ptr.byte_offset },
                                        } },
                                        .eu_payload => |base| {
                                            var base_ptr = ip.indexToKey(base).ptr;
                                            const eu_ty = ip.indexToKey(base_ptr.ty).ptr_type.child;
                                            const payload_ty = ip.indexToKey(eu_ty).error_union_type.payload_type;
                                            base_ptr.byte_offset += codegen.errUnionPayloadOffset(.fromInterned(payload_ty), zcu) + ptr.byte_offset;
                                            continue :constant_key .{ .ptr = base_ptr };
                                        },
                                        .opt_payload => |base| {
                                            var base_ptr = ip.indexToKey(base).ptr;
                                            base_ptr.byte_offset += ptr.byte_offset;
                                            continue :constant_key .{ .ptr = base_ptr };
                                        },
                                        .field => |field| {
                                            var base_ptr = ip.indexToKey(field.base).ptr;
                                            const agg_ty: ZigType = .fromInterned(ip.indexToKey(base_ptr.ty).ptr_type.child);
                                            base_ptr.byte_offset += agg_ty.structFieldOffset(@intCast(field.index), zcu) + ptr.byte_offset;
                                            continue :constant_key .{ .ptr = base_ptr };
                                        },
                                        .comptime_alloc, .comptime_field, .arr_elem => unreachable,
                                    };
                                },
                                .slice => |slice| switch (offset) {
                                    0 => continue :constant_key switch (ip.indexToKey(slice.ptr)) {
                                        else => unreachable,
                                        .undef => |undef| .{ .undef = undef },
                                        .ptr => |ptr| .{ .ptr = ptr },
                                    },
                                    else => {
                                        assert(offset == @divExact(isel.target.ptrBitWidth(), 8));
                                        offset = 0;
                                        continue :constant_key .{ .int = ip.indexToKey(slice.len).int };
                                    },
                                },
                                .opt => |opt| {
                                    const child_ty = ip.indexToKey(opt.ty).opt_type;
                                    const child_size = ZigType.fromInterned(child_ty).abiSize(zcu);
                                    if (offset == child_size and size == 1) {
                                        offset = 0;
                                        continue :constant_key .{ .simple_value = switch (opt.val) {
                                            .none => .false,
                                            else => .true,
                                        } };
                                    }
                                    const opt_ty: ZigType = .fromInterned(opt.ty);
                                    if (offset + size <= child_size) continue :constant_key switch (opt.val) {
                                        .none => if (opt_ty.optionalReprIsPayload(zcu)) .{ .int = .{
                                            .ty = opt.ty,
                                            .storage = .{ .u64 = 0 },
                                        } } else .{ .undef = child_ty },
                                        else => |child| {
                                            constant = child;
                                            constant_key = ip.indexToKey(constant);
                                            continue :constant_key constant_key;
                                        },
                                    };
                                },
                                .aggregate => |aggregate| switch (ip.indexToKey(aggregate.ty)) {
                                    else => unreachable,
                                    .array_type => |array_type| {
                                        const elem_size = ZigType.fromInterned(array_type.child).abiSize(zcu);
                                        const elem_offset = @mod(offset, elem_size);
                                        if (size <= elem_size - elem_offset) {
                                            defer offset = elem_offset;
                                            continue :constant_key switch (aggregate.storage) {
                                                .bytes => |bytes| .{ .int = .{ .ty = .u8_type, .storage = .{
                                                    .u64 = bytes.toSlice(array_type.lenIncludingSentinel(), ip)[@intCast(@divFloor(offset, elem_size))],
                                                } } },
                                                .elems => |elems| {
                                                    constant = elems[@intCast(@divFloor(offset, elem_size))];
                                                    constant_key = ip.indexToKey(constant);
                                                    continue :constant_key constant_key;
                                                },
                                                .repeated_elem => |repeated_elem| {
                                                    constant = repeated_elem;
                                                    constant_key = ip.indexToKey(constant);
                                                    continue :constant_key constant_key;
                                                },
                                            };
                                        }
                                    },
                                    .vector_type => {},
                                    .struct_type => {
                                        const loaded_struct = ip.loadStructType(aggregate.ty);
                                        switch (loaded_struct.layout) {
                                            .auto => {
                                                var field_offset: u64 = 0;
                                                var field_it = loaded_struct.iterateRuntimeOrder(ip);
                                                while (field_it.next()) |field_index| {
                                                    if (loaded_struct.fieldIsComptime(ip, field_index)) continue;
                                                    const field_ty: ZigType = .fromInterned(loaded_struct.field_types.get(ip)[field_index]);
                                                    field_offset = field_ty.structFieldAlignment(
                                                        loaded_struct.fieldAlign(ip, field_index),
                                                        loaded_struct.layout,
                                                        zcu,
                                                    ).forward(field_offset);
                                                    const field_size = field_ty.abiSize(zcu);
                                                    if (offset >= field_offset and offset + size <= field_offset + field_size) {
                                                        offset -= field_offset;
                                                        constant = switch (aggregate.storage) {
                                                            .bytes => unreachable,
                                                            .elems => |elems| elems[field_index],
                                                            .repeated_elem => |repeated_elem| repeated_elem,
                                                        };
                                                        constant_key = ip.indexToKey(constant);
                                                        continue :constant_key constant_key;
                                                    }
                                                    field_offset += field_size;
                                                }
                                            },
                                            .@"extern", .@"packed" => {},
                                        }
                                    },
                                    .tuple_type => |tuple_type| {
                                        var field_offset: u64 = 0;
                                        for (tuple_type.types.get(ip), tuple_type.values.get(ip), 0..) |field_type, field_value, field_index| {
                                            if (field_value != .none) continue;
                                            const field_ty: ZigType = .fromInterned(field_type);
                                            field_offset = field_ty.abiAlignment(zcu).forward(field_offset);
                                            const field_size = field_ty.abiSize(zcu);
                                            if (offset >= field_offset and offset + size <= field_offset + field_size) {
                                                offset -= field_offset;
                                                constant = switch (aggregate.storage) {
                                                    .bytes => unreachable,
                                                    .elems => |elems| elems[field_index],
                                                    .repeated_elem => |repeated_elem| repeated_elem,
                                                };
                                                constant_key = ip.indexToKey(constant);
                                                continue :constant_key constant_key;
                                            }
                                            field_offset += field_size;
                                        }
                                    },
                                },
                                .un => |un| {
                                    const loaded_union = ip.loadUnionType(un.ty);
                                    const union_layout = ZigType.getUnionLayout(loaded_union, zcu);
                                    if (loaded_union.hasTag(ip)) {
                                        const tag_offset = union_layout.tagOffset();
                                        if (offset >= tag_offset and offset + size <= tag_offset + union_layout.tag_size) {
                                            offset -= tag_offset;
                                            continue :constant_key switch (ip.indexToKey(un.tag)) {
                                                else => unreachable,
                                                .int => |int| .{ .int = int },
                                                .enum_tag => |enum_tag| .{ .enum_tag = enum_tag },
                                            };
                                        }
                                    }
                                    const payload_offset = union_layout.payloadOffset();
                                    if (offset >= payload_offset and offset + size <= payload_offset + union_layout.payload_size) {
                                        offset -= payload_offset;
                                        constant = un.val;
                                        constant_key = ip.indexToKey(constant);
                                        continue :constant_key constant_key;
                                    }
                                },
                                else => {},
                            }
                            // var buffer: [16]u8 = @splat(0);
                            // if (ZigType.fromInterned(constant_key.typeOf()).abiSize(zcu) <= buffer.len and
                            //     try isel.writeToMemory(.fromInterned(constant), &buffer))
                            // {
                            //     constant_key = if (mat.ra.isVector()) .{ .float = switch (size) {
                            //         else => unreachable,
                            //         2 => .{ .ty = .f16_type, .storage = .{ .f16 = @bitCast(std.mem.readInt(
                            //             u16,
                            //             buffer[@intCast(offset)..][0..2],
                            //             isel.target.cpu.arch.endian(),
                            //         )) } },
                            //         4 => .{ .ty = .f32_type, .storage = .{ .f32 = @bitCast(std.mem.readInt(
                            //             u32,
                            //             buffer[@intCast(offset)..][0..4],
                            //             isel.target.cpu.arch.endian(),
                            //         )) } },
                            //         8 => .{ .ty = .f64_type, .storage = .{ .f64 = @bitCast(std.mem.readInt(
                            //             u64,
                            //             buffer[@intCast(offset)..][0..8],
                            //             isel.target.cpu.arch.endian(),
                            //         )) } },
                            //         16 => .{ .ty = .f128_type, .storage = .{ .f128 = @bitCast(std.mem.readInt(
                            //             u128,
                            //             buffer[@intCast(offset)..][0..16],
                            //             isel.target.cpu.arch.endian(),
                            //         )) } },
                            //     } } else .{ .int = .{
                            //         .ty = .u64_type,
                            //         .storage = .{ .u64 = switch (size) {
                            //             else => unreachable,
                            //             inline 1...8 => |ct_size| std.mem.readInt(
                            //                 @Type(.{ .int = .{ .signedness = .unsigned, .bits = 8 * ct_size } }),
                            //                 buffer[@intCast(offset)..][0..ct_size],
                            //                 isel.target.cpu.arch.endian(),
                            //             ),
                            //         } },
                            //     } };
                            //     offset = 0;
                            //     continue;
                            // }
                            return isel.fail("unsupported value <{f}, {f}>", .{
                                isel.fmtType(.fromInterned(constant_key.typeOf())),
                                isel.fmtConstant(.fromInterned(constant)),
                            });
                        }
                    },
                    else => |parent_tag| return isel.fail("unimplemented finish materialization {t}", .{parent_tag}),
                }
            }
            live_vi.* = .free;
        }
    };
};

fn fail(isel: *Select, comptime format: []const u8, args: anytype) error{ OutOfMemory, CodegenFail } {
    @branchHint(.cold);
    return isel.pt.zcu.codegenFail(isel.nav_index, format, args);
}

pub fn analyze(isel: *Select, air_body: []const Air.Inst.Index) !void {
    const zcu = isel.pt.zcu;
    const ip = &zcu.intern_pool;
    const gpa = zcu.gpa;
    const air_tags = isel.air.instructions.items(.tag);
    const air_data = isel.air.instructions.items(.data);
    const initial_def_order_len = isel.def_order.count();

    for (air_body, 0..) |air_inst_index, air_body_index| {
        _ = air_body_index;
        switch (air_tags[@intFromEnum(air_inst_index)]) {
            else => |air_tag| return isel.fail("unimplemented analyze for {t}", .{air_tag}),
            .arg,
            .ret_addr,
            .frame_addr,
            .err_return_trace,
            .save_err_return_trace_index,
            .runtime_nav_ptr,
            .c_va_start,
            => {
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .add,
            .add_safe,
            .add_optimized,
            .add_wrap,
            .add_sat,
            .sub,
            .sub_safe,
            .sub_optimized,
            .sub_wrap,
            .sub_sat,
            .mul,
            .mul_safe,
            .mul_optimized,
            .mul_wrap,
            .mul_sat,
            .div_float,
            .div_float_optimized,
            .div_trunc,
            .div_trunc_optimized,
            .div_floor,
            .div_floor_optimized,
            .div_exact,
            .div_exact_optimized,
            .rem,
            .rem_optimized,
            .mod,
            .mod_optimized,
            .max,
            .min,
            .bit_and,
            .bit_or,
            .shr,
            .shr_exact,
            .shl,
            .shl_exact,
            .shl_sat,
            .xor,
            .cmp_lt,
            .cmp_lt_optimized,
            .cmp_lte,
            .cmp_lte_optimized,
            .cmp_eq,
            .cmp_eq_optimized,
            .cmp_gte,
            .cmp_gte_optimized,
            .cmp_gt,
            .cmp_gt_optimized,
            .cmp_neq,
            .cmp_neq_optimized,
            .bool_and,
            .bool_or,
            .array_elem_val,
            .slice_elem_val,
            .ptr_elem_val,
            => {
                const bin_op = air_data[@intFromEnum(air_inst_index)].bin_op;

                try isel.analyzeUse(bin_op.lhs);
                try isel.analyzeUse(bin_op.rhs);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .ptr_add,
            .ptr_sub,
            .add_with_overflow,
            .sub_with_overflow,
            .mul_with_overflow,
            .shl_with_overflow,
            .slice,
            .slice_elem_ptr,
            .ptr_elem_ptr,
            => {
                const ty_pl = air_data[@intFromEnum(air_inst_index)].ty_pl;
                const bin_op = isel.air.extraData(Air.Bin, ty_pl.payload).data;

                try isel.analyzeUse(bin_op.lhs);
                try isel.analyzeUse(bin_op.rhs);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .alloc => {
                const ty = air_data[@intFromEnum(air_inst_index)].ty;

                isel.stack_align = isel.stack_align.maxStrict(ty.ptrAlignment(zcu));
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .inferred_alloc,
            .inferred_alloc_comptime,
            .wasm_memory_size,
            .wasm_memory_grow,
            .work_item_id,
            .work_group_size,
            .work_group_id,
            => unreachable,
            .ret, .ret_safe, .ret_load => {
                const un_op = air_data[@intFromEnum(air_inst_index)].un_op;
                isel.returns = true;

                const block_index = 0;
                assert(isel.blocks.keys()[block_index] == Block.main);

                try isel.analyzeUse(un_op);
            },
            .ret_ptr => {
                const ty = air_data[@intFromEnum(air_inst_index)].ty;

                if (isel.live_values.get(Block.main)) |ret_vi| switch (ret_vi.parent(isel)) {
                    .unallocated, .stack_slot => isel.stack_align = isel.stack_align.maxStrict(ty.ptrAlignment(zcu)),
                    .value, .constant => unreachable,
                    .address => |address_vi| try isel.live_values.putNoClobber(gpa, air_inst_index, address_vi.ref(isel)),
                };
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .assembly => {
                const ty_pl = air_data[@intFromEnum(air_inst_index)].ty_pl;
                const extra = isel.air.extraData(Air.Asm, ty_pl.payload);
                const operands: []const Air.Inst.Ref = @ptrCast(isel.air.extra.items[extra.end..][0 .. extra.data.flags.outputs_len + extra.data.inputs_len]);

                for (operands) |operand| if (operand != .none) try isel.analyzeUse(operand);
                if (ty_pl.ty != .void_type) try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .not,
            .clz,
            .ctz,
            .popcount,
            .byte_swap,
            .bit_reverse,
            .abs,
            .load,
            .fptrunc,
            .fpext,
            .intcast,
            .intcast_safe,
            .trunc,
            .optional_payload,
            .optional_payload_ptr,
            .optional_payload_ptr_set,
            .wrap_optional,
            .unwrap_errunion_payload,
            .unwrap_errunion_err,
            .unwrap_errunion_payload_ptr,
            .unwrap_errunion_err_ptr,
            .errunion_payload_ptr_set,
            .wrap_errunion_payload,
            .wrap_errunion_err,
            .struct_field_ptr_index_0,
            .struct_field_ptr_index_1,
            .struct_field_ptr_index_2,
            .struct_field_ptr_index_3,
            .get_union_tag,
            .ptr_slice_len_ptr,
            .ptr_slice_ptr_ptr,
            .array_to_slice,
            .int_from_float,
            .int_from_float_optimized,
            .int_from_float_safe,
            .int_from_float_optimized_safe,
            .float_from_int,
            .splat,
            .error_set_has_value,
            .addrspace_cast,
            .c_va_arg,
            .c_va_copy,
            => {
                const ty_op = air_data[@intFromEnum(air_inst_index)].ty_op;

                try isel.analyzeUse(ty_op.operand);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .repeat, .trap, .unreach => {},
            .br => {
                const br = air_data[@intFromEnum(air_inst_index)].br;
                try isel.analyzeUse(br.operand);
            },
            .breakpoint, .dbg_stmt, .dbg_empty_stmt, .dbg_var_ptr, .dbg_var_val, .dbg_arg_inline, .c_va_end => {},
            .sqrt,
            .sin,
            .cos,
            .tan,
            .exp,
            .exp2,
            .log,
            .log2,
            .log10,
            .floor,
            .ceil,
            .round,
            .trunc_float,
            .neg,
            .neg_optimized,
            .is_null,
            .is_non_null,
            .is_null_ptr,
            .is_non_null_ptr,
            .is_err,
            .is_non_err,
            .is_err_ptr,
            .is_non_err_ptr,
            .is_named_enum_value,
            .tag_name,
            .error_name,
            .cmp_lt_errors_len,
            => {
                const un_op = air_data[@intFromEnum(air_inst_index)].un_op;

                try isel.analyzeUse(un_op);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .cmp_vector, .cmp_vector_optimized => {
                const ty_pl = air_data[@intFromEnum(air_inst_index)].ty_pl;
                const extra = isel.air.extraData(Air.VectorCmp, ty_pl.payload).data;

                try isel.analyzeUse(extra.lhs);
                try isel.analyzeUse(extra.rhs);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .store,
            .store_safe,
            .set_union_tag,
            .memset,
            .memset_safe,
            .memcpy,
            .memmove,
            .atomic_store_unordered,
            .atomic_store_monotonic,
            .atomic_store_release,
            .atomic_store_seq_cst,
            => {
                const bin_op = air_data[@intFromEnum(air_inst_index)].bin_op;

                try isel.analyzeUse(bin_op.lhs);
                try isel.analyzeUse(bin_op.rhs);
            },
            .struct_field_ptr, .struct_field_val => {
                const ty_pl = air_data[@intFromEnum(air_inst_index)].ty_pl;
                const extra = isel.air.extraData(Air.StructField, ty_pl.payload).data;

                try isel.analyzeUse(extra.struct_operand);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .aggregate_init => {
                const ty_pl = air_data[@intFromEnum(air_inst_index)].ty_pl;
                const elements: []const Air.Inst.Ref = @ptrCast(isel.air.extra.items[ty_pl.payload..][0..@intCast(ty_pl.ty.toType().arrayLen(zcu))]);

                for (elements) |element| try isel.analyzeUse(element);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .union_init => {
                const ty_pl = air_data[@intFromEnum(air_inst_index)].ty_pl;
                const extra = isel.air.extraData(Air.UnionInit, ty_pl.payload).data;

                try isel.analyzeUse(extra.init);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .prefetch => {
                const prefetch = air_data[@intFromEnum(air_inst_index)].prefetch;
                try isel.analyzeUse(prefetch.ptr);
            },
            .field_parent_ptr => {
                const ty_pl = air_data[@intFromEnum(air_inst_index)].ty_pl;
                const extra = isel.air.extraData(Air.FieldParentPtr, ty_pl.payload).data;

                try isel.analyzeUse(extra.field_ptr);
                try isel.def_order.putNoClobber(gpa, air_inst_index, {});
            },
            .set_err_return_trace => {
                const un_op = air_data[@intFromEnum(air_inst_index)].un_op;
                try isel.analyzeUse(un_op);
            },
            inline .block, .dbg_inline_block => |air_tag| {
                const ty_pl = air_data[@intFromEnum(air_inst_index)].ty_pl;
                const extra = isel.air.extraData(switch (air_tag) {
                    else => comptime unreachable,
                    .block => Air.Block,
                    .dbg_inline_block => Air.DbgInlineBlock,
                }, ty_pl.payload);
                const result_ty = ty_pl.ty.toInterned().?;

                if (result_ty == .noreturn_type) {
                    try isel.analyze(@ptrCast(isel.air.extra.items[extra.end..][0..extra.data.body_len]));
                    break;
                }

                assert(!(try isel.blocks.getOrPut(gpa, air_inst_index)).found_existing);
                try isel.analyze(@ptrCast(isel.air.extra.items[extra.end..][0..extra.data.body_len]));
                const block_entry = isel.blocks.pop().?;
                assert(block_entry.key == air_inst_index);

                if (result_ty != .void_type) try isel.def_order.putNoClobber(gpa, air_inst_index, {});
                break;
            },
            .call,
            .call_always_tail,
            .call_never_tail,
            .call_never_inline,
            => {
                const pl_op = air_data[@intFromEnum(air_inst_index)].pl_op;
                const extra = isel.air.extraData(Air.Call, pl_op.payload);
                const args: []const Air.Inst.Ref = @ptrCast(isel.air.extra.items[extra.end..][0..extra.data.args_len]);
                isel.saved_registers.insert(.ra);
                const callee_ty = isel.air.typeOf(pl_op.operand, ip);
                const func_info = switch (ip.indexToKey(callee_ty.toIntern())) {
                    else => unreachable,
                    .func_type => |func_type| func_type,
                    .ptr_type => |ptr_type| ip.indexToKey(ptr_type.child).func_type,
                };

                try isel.analyzeUse(pl_op.operand);
                var cc_it: CallAbiIterator = .{ .isel = isel, .cc = &func_info.cc };

                const ret_ty = isel.air.typeOfIndex(air_inst_index, ip);
                if (try cc_it.resolve(ret_ty, true)) |ret_vi| {
                    tracking_log.debug("${d} <- %{d} (call return)", .{ @intFromEnum(ret_vi), @intFromEnum(air_inst_index) });
                    switch (ret_vi.parent(isel)) {
                        .unallocated, .stack_slot => {},
                        .value, .constant => unreachable,
                        .address => |address_vi| {
                            defer address_vi.deref(isel);
                            const ret_value = ret_vi.get(isel);
                            ret_value.flags.parent_tag = .unallocated;
                            ret_value.parent_payload = .{ .unallocated = {} };
                        },
                    }
                    try isel.live_values.putNoClobber(gpa, air_inst_index, ret_vi);

                    try isel.def_order.putNoClobber(gpa, air_inst_index, {});
                }

                for (args) |arg| {
                    const restore_values_len = isel.values.items.len;
                    defer isel.values.shrinkRetainingCapacity(restore_values_len);

                    const param_ty = isel.air.typeOf(arg, ip);
                    const param_vi = try cc_it.resolve(param_ty, false) orelse continue;
                    defer param_vi.deref(isel);

                    const passed_vi = switch (param_vi.parent(isel)) {
                        .unallocated, .stack_slot => param_vi,
                        .value, .constant => unreachable,
                        .address => |address_vi| address_vi,
                    };
                    switch (passed_vi.parent(isel)) {
                        .unallocated => {},
                        .stack_slot => |stack_slot| {
                            assert(stack_slot.base == Register.sp);
                            isel.stack_size = @max(
                                isel.stack_size,
                                stack_slot.offset + @as(u24, @intCast(passed_vi.size(isel))),
                            );
                        },
                        .value, .constant, .address => unreachable,
                    }

                    try isel.analyzeUse(arg);
                }
            },
        }
    }
    isel.def_order.shrinkRetainingCapacity(initial_def_order_len);
}

fn analyzeUse(isel: *Select, air_ref: Air.Inst.Ref) !void {
    const air_inst_index = air_ref.toIndex() orelse return;
    const def_order_index = isel.def_order.getIndex(air_inst_index).?;
    _ = def_order_index;
}

pub fn finishAnalysis(isel: *Select) !void {
    // const gpa = isel.pt.zcu.gpa;
    _ = isel;
}

pub fn verify(isel: *Select, check_values: bool) void {
    if (!std.debug.runtime_safety) return;
    assert(isel.blocks.count() == 1 and isel.blocks.keys()[0] == Select.Block.main);

    // assert(isel.active_loops.items.len == 0); TODO
    var live_reg_it = isel.live_registers.iterator();
    while (live_reg_it.next()) |live_reg_entry| switch (live_reg_entry.value.*) {
        _ => {
            tracking_log.err("${t} is still used by ${d}", .{ live_reg_entry.key, live_reg_entry.value.* });
            isel.dumpValues(.all);
            unreachable;
        },
        .allocating, .free => {},
    };
    if (check_values) for (isel.values.items) |value| if (value.refs != 0) {
        isel.dumpValues(.only_referenced);
        unreachable;
    };
    if (check_values) isel.dumpValues(.all);
}

pub fn body(isel: *Select, air_body: []const Air.Inst.Index) error{ OutOfMemory, CodegenFail }!void {
    const zcu = isel.pt.zcu;
    const ip = &zcu.intern_pool;
    const gpa = zcu.gpa;

    {
        var live_reg_it = isel.live_registers.iterator();
        while (live_reg_it.next()) |live_reg_entry| switch (live_reg_entry.value.*) {
            _ => {
                const ra = &live_reg_entry.value.get(isel).location_payload.small.register;
                assert(ra.* == live_reg_entry.key);
                ra.* = .zero;
                live_reg_entry.value.* = .free;
            },
            .allocating => live_reg_entry.value.* = .free,
            .free => {},
        };
    }

    var air: struct {
        isel: *Select,
        tag_items: []const Air.Inst.Tag,
        data_items: []const Air.Inst.Data,
        body: []const Air.Inst.Index,
        body_index: u32,
        inst_index: Air.Inst.Index,

        fn tag(it: *@This(), inst_index: Air.Inst.Index) Air.Inst.Tag {
            return it.tag_items[@intFromEnum(inst_index)];
        }

        fn data(it: *@This(), inst_index: Air.Inst.Index) Air.Inst.Data {
            return it.data_items[@intFromEnum(inst_index)];
        }

        fn next(it: *@This()) ?Air.Inst.Tag {
            if (it.body_index == 0) {
                @branchHint(.unlikely);
                return null;
            }
            it.body_index -= 1;
            it.inst_index = it.body[it.body_index];
            wip_mir_log.debug("{f}", .{it.fmtAir(it.inst_index)});
            return it.tag(it.inst_index);
        }

        fn fmtAir(it: @This(), inst: Air.Inst.Index) struct {
            isel: *Select,
            inst: Air.Inst.Index,
            pub fn format(fmt_air: @This(), writer: *std.Io.Writer) std.Io.Writer.Error!void {
                fmt_air.isel.air.writeInst(writer, fmt_air.inst, fmt_air.isel.pt, null);
            }
        } {
            return .{ .isel = it.isel, .inst = inst };
        }
    } = .{
        .isel = isel,
        .tag_items = isel.air.instructions.items(.tag),
        .data_items = isel.air.instructions.items(.data),
        .body = air_body,
        .body_index = @intCast(air_body.len),
        .inst_index = undefined,
    };
    while (air.next()) |air_tag| {
        switch (air_tag) {
            else => return isel.fail("unimplemented select for {s}", .{@tagName(air_tag)}),
            .unreach => {},
            .arg => {
                const arg_vi = isel.live_values.fetchRemove(air.inst_index).?.value;
                defer arg_vi.deref(isel);
                switch (arg_vi.parent(isel)) {
                    .unallocated, .stack_slot => if (arg_vi.hint(isel)) |arg_reg| {
                        try arg_vi.defLiveIn(isel, arg_reg, comptime &.initFill(.free));
                    } else {
                        var arg_part_it = arg_vi.parts(isel);
                        while (arg_part_it.next()) |arg_part| {
                            try arg_part.defLiveIn(isel, arg_part.hint(isel).?, comptime &.initFill(.free));
                        }
                    },
                    .value, .constant => unreachable,
                    .address => |address_vi| try address_vi.defLiveIn(isel, address_vi.hint(isel).?, comptime &.initFill(.free)),
                }
            },
            .br => {
                const br = air.data(air.inst_index).br;
                try isel.blocks.getPtr(br.block_inst).?.branch(isel);
                if (isel.live_values.get(br.block_inst)) |dst_vi| try dst_vi.move(isel, br.operand);
            },
            .trap, .breakpoint => try isel.emit(.@"break"(0)),
            .dbg_stmt, .dbg_var_ptr, .dbg_var_val, .dbg_arg_inline => {},
            .dbg_empty_stmt => try isel.emit(.ori(.r0, .r0, 0)),
            .dbg_inline_block => {
                const ty_pl = air.data(air.inst_index).ty_pl;
                const extra = isel.air.extraData(Air.DbgInlineBlock, ty_pl.payload);
                try isel.block(air.inst_index, ty_pl.ty.toType(), @ptrCast(
                    isel.air.extra.items[extra.end..][0..extra.data.body_len],
                ));
            },
            .block => {
                const ty_pl = air.data(air.inst_index).ty_pl;
                const extra = isel.air.extraData(Air.Block, ty_pl.payload);
                try isel.block(air.inst_index, ty_pl.ty.toType(), @ptrCast(
                    isel.air.extra.items[extra.end..][0..extra.data.body_len],
                ));
            },
            .call => {
                const pl_op = air.data(air.inst_index).pl_op;
                const extra = isel.air.extraData(Air.Call, pl_op.payload);
                const args: []const Air.Inst.Ref = @ptrCast(isel.air.extra.items[extra.end..][0..extra.data.args_len]);
                const callee_ty = isel.air.typeOf(pl_op.operand, ip);
                const func_info = switch (ip.indexToKey(callee_ty.toIntern())) {
                    else => unreachable,
                    .func_type => |func_type| func_type,
                    .ptr_type => |ptr_type| ip.indexToKey(ptr_type.child).func_type,
                };

                var cc_it: CallAbiIterator = .{ .isel = isel, .cc = &func_info.cc };

                // return value
                try call.prepareReturn(isel);
                const ret_ty = isel.air.typeOfIndex(air.inst_index, ip);
                const maybe_def_ret_vi = isel.live_values.fetchRemove(air.inst_index);
                const maybe_ret_vi = try cc_it.resolve(ret_ty, true);
                defer if (maybe_ret_vi) |ret_vi| ret_vi.deref(isel);

                const maybe_ret_indirects: ?[]call.IndirectValue = if (maybe_ret_vi) |ret_vi|
                    try call.returnAllocIndirect(isel, ret_vi)
                else
                    null;
                defer if (maybe_ret_indirects) |ret_indirects| {
                    for (ret_indirects) |ret_indirect| ret_indirect.addr_vi.deref(isel);
                    gpa.free(ret_indirects);
                };

                if (maybe_def_ret_vi) |def_ret_vi| {
                    defer def_ret_vi.value.deref(isel);
                    try def_ret_vi.value.copy(isel, ret_ty, maybe_ret_vi.?);
                }
                try call.finishReturn(isel);

                // call
                try call.prepareCallee(isel);
                if (pl_op.operand.toInterned()) |ct_callee| {
                    try isel.emit(.jirl(.ra, .ra, 0));
                    try isel.nav_relocs.append(gpa, switch (ip.indexToKey(ct_callee)) {
                        else => unreachable,
                        inline .@"extern", .func => |func| .{
                            .nav = func.owner_nav,
                            .reloc = .{ .label = @intCast(isel.instructions.items.len) },
                        },
                        .ptr => |ptr| .{
                            .nav = ptr.base_addr.nav,
                            .reloc = .{
                                .label = @intCast(isel.instructions.items.len),
                                .addend = @intCast(ptr.byte_offset),
                            },
                        },
                    });
                    try isel.emit(.pcaddu18i(.ra, 0));
                } else {
                    const callee_vi = try isel.use(pl_op.operand);
                    const callee_mat = try callee_vi.matReg(isel);
                    try isel.emit(.jirl(.ra, callee_mat.reg, 0));
                    try callee_mat.finish(isel);
                }
                try call.finishCallee(isel);

                // params
                try call.prepareParams(isel);
                if (maybe_ret_indirects) |ret_indirects| for (ret_indirects) |ret_indirect| {
                    const addr_mat = try ret_indirect.addr_vi.matReg(isel);
                    try ret_indirect.value_vi.address(isel, 0, addr_mat.reg);
                    try addr_mat.finish(isel);
                };
                for (args) |arg| {
                    const param_ty = isel.air.typeOf(arg, ip);
                    const param_vi = try cc_it.resolve(param_ty, false) orelse continue;
                    defer param_vi.deref(isel);
                    const arg_vi = try isel.use(arg);
                    switch (param_vi.parent(isel)) {
                        .unallocated => if (param_vi.hint(isel)) |param_ra| {
                            try call.paramLiveOut(isel, arg_vi, param_ra);
                        } else {
                            var param_part_it = param_vi.parts(isel);
                            var arg_part_it = arg_vi.parts(isel);
                            if (arg_part_it.only()) |_| {
                                try isel.values.ensureUnusedCapacity(gpa, param_part_it.remaining);
                                arg_vi.setParts(isel, param_part_it.remaining);
                                while (param_part_it.next()) |param_part_vi| _ = arg_vi.addPart(
                                    isel,
                                    param_part_vi.get(isel).offset_from_parent,
                                    param_part_vi.size(isel),
                                );
                                param_part_it = param_vi.parts(isel);
                                arg_part_it = arg_vi.parts(isel);
                            }
                            while (param_part_it.next()) |param_part_vi| {
                                const arg_part_vi = arg_part_it.next().?;
                                assert(arg_part_vi.get(isel).offset_from_parent ==
                                    param_part_vi.get(isel).offset_from_parent);
                                assert(arg_part_vi.size(isel) == param_part_vi.size(isel));
                                try call.paramLiveOut(isel, arg_part_vi, param_part_vi.hint(isel).?);
                            }
                        },
                        .stack_slot => |stack_slot| try arg_vi.store(isel, param_ty, stack_slot.base, .{
                            .offset = @intCast(stack_slot.offset),
                        }),
                        .value, .constant => unreachable,
                        .address => |address_vi| try arg_vi.address(isel, 0, address_vi.hint(isel).?),
                    }
                }
                try call.finishParams(isel);
            },
            .inferred_alloc, .inferred_alloc_comptime => unreachable,
            .ret, .ret_safe => {
                assert(isel.blocks.keys()[0] == Block.main);
                try isel.blocks.values()[0].branch(isel);
                if (isel.live_values.get(Block.main)) |ret_vi| {
                    const un_op = air.data(air.inst_index).un_op;
                    const src_vi = try isel.use(un_op);
                    switch (ret_vi.parent(isel)) {
                        .unallocated, .stack_slot => if (ret_vi.hint(isel)) |ret_ra| {
                            try src_vi.liveOut(isel, ret_ra);
                        } else {
                            var ret_part_it = ret_vi.parts(isel);
                            var src_part_it = src_vi.parts(isel);
                            if (src_part_it.only()) |_| {
                                try isel.values.ensureUnusedCapacity(gpa, ret_part_it.remaining);
                                src_vi.setParts(isel, ret_part_it.remaining);
                                while (ret_part_it.next()) |ret_part_vi| {
                                    const src_part_vi = src_vi.addPart(
                                        isel,
                                        ret_part_vi.get(isel).offset_from_parent,
                                        ret_part_vi.size(isel),
                                    );
                                    switch (ret_part_vi.signedness(isel)) {
                                        .signed => src_part_vi.setSignedness(isel, .signed),
                                        .unsigned => {},
                                    }
                                    src_part_vi.setRegisterClass(isel, ret_part_vi.registerClass(isel));
                                    src_part_vi.setModifier(isel, ret_part_vi.modifier(isel));
                                }
                                ret_part_it = ret_vi.parts(isel);
                                src_part_it = src_vi.parts(isel);
                            }
                            while (ret_part_it.next()) |ret_part_vi| {
                                const src_part_vi = src_part_it.next().?;
                                assert(ret_part_vi.get(isel).offset_from_parent == src_part_vi.get(isel).offset_from_parent);
                                assert(ret_part_vi.size(isel) == src_part_vi.size(isel));
                                try src_part_vi.liveOut(isel, ret_part_vi.hint(isel).?);
                            }
                        },
                        .value, .constant => unreachable,
                        .address => |address_vi| {
                            const ptr_mat = try address_vi.matReg(isel);
                            try src_vi.store(isel, isel.air.typeOf(un_op, ip), ptr_mat.reg, .{});
                            try ptr_mat.finish(isel);
                        },
                    }
                }
            },
            .ret_load => {
                const un_op = air.data(air.inst_index).un_op;
                const ptr_ty = isel.air.typeOf(un_op, ip);
                const ptr_info = ptr_ty.ptrInfo(zcu);
                if (ptr_info.packed_offset.host_size > 0) return isel.fail("packed load", .{});

                assert(isel.blocks.keys()[0] == Block.main);
                try isel.blocks.values()[0].branch(isel);
                if (isel.live_values.get(Block.main)) |ret_vi| switch (ret_vi.parent(isel)) {
                    .unallocated, .stack_slot => {
                        var ret_part_it: Value.PartIterator = if (ret_vi.hint(isel)) |_| .initOne(ret_vi) else ret_vi.parts(isel);
                        while (ret_part_it.next()) |ret_part_vi| try ret_part_vi.liveOut(isel, ret_part_vi.hint(isel).?);
                        const ptr_vi = try isel.use(un_op);
                        const ptr_mat = try ptr_vi.matReg(isel);
                        _ = try ret_vi.load(isel, .fromInterned(ptr_info.child), ptr_mat.reg, .{});
                        try ptr_mat.finish(isel);
                    },
                    .value, .constant => unreachable,
                    .address => {},
                };
            },
            .add, .add_safe, .add_optimized, .add_wrap, .sub, .sub_safe, .sub_optimized, .sub_wrap => {
                if (isel.live_values.fetchRemove(air.inst_index)) |res_vi| {
                    defer res_vi.value.deref(isel);

                    const bin_op = air.data(air.inst_index).bin_op;
                    const ty = isel.air.typeOf(bin_op.lhs, ip);
                    if (!ty.isRuntimeFloat()) try isel.addOrSubtract(ty, res_vi.value, switch (air_tag) {
                        else => unreachable,
                        .add, .add_safe, .add_wrap => .add,
                        .sub, .sub_safe, .sub_wrap => .sub,
                    }, try isel.use(bin_op.lhs), try isel.use(bin_op.rhs), .{
                        .overflow = switch (air_tag) {
                            else => unreachable,
                            .add, .sub => .@"unreachable",
                            .add_safe, .sub_safe => .{ .panic = .integer_overflow },
                            .add_wrap, .sub_wrap => .wrap,
                        },
                    }) else return isel.fail("unimplemented float", .{});
                }
            },
        }
        // isel.dumpValues(.all);
    }
    assert(air.body_index == 0);
}

/// Generates prologue and epilogue. Returns the length of epilogue.
pub fn layout(isel: *Select, cc_it: CallAbiIterator, mod: *const Package.Module) !usize {
    _ = cc_it;
    _ = mod;
    const zcu = isel.pt.zcu;
    const ip = &zcu.intern_pool;
    const nav = ip.getNav(isel.nav_index);
    wip_mir_log.debug("{f}<body>:\n", .{nav.fqn.fmt(ip)});

    const epilogue = isel.instructions.items.len;
    if (isel.returns) {
        try isel.emit(.jirl(.ra, .ra, 0));
        wip_mir_log.debug("{f}<epilogue>:\n", .{nav.fqn.fmt(ip)});
    }
    return epilogue;
}

fn emit(isel: *Select, instruction: Instruction) !void {
    wip_mir_log.debug("  | {f}", .{(Disassemble{}).fmtInstruction(instruction)});
    try isel.instructions.append(isel.pt.zcu.gpa, instruction);
}

fn block(
    isel: *Select,
    air_inst_index: Air.Inst.Index,
    res_ty: ZigType,
    air_body: []const Air.Inst.Index,
) !void {
    if (res_ty.toIntern() != .noreturn_type) {
        isel.blocks.putAssumeCapacityNoClobber(air_inst_index, .{
            .live_registers = isel.live_registers,
            .target_label = @intCast(isel.instructions.items.len),
        });
    }
    try isel.body(air_body);
    if (res_ty.toIntern() != .noreturn_type) {
        const block_entry = isel.blocks.pop().?;
        assert(block_entry.key == air_inst_index);
        if (isel.live_values.fetchRemove(air_inst_index)) |result_vi| result_vi.value.deref(isel);
    }
}

fn initValue(isel: *Select, ty: ZigType) Value.Index {
    const zcu = isel.pt.zcu;
    return isel.initValueAdvanced(ty.abiAlignment(zcu), 0, ty.abiSize(zcu));
}

fn initValueAdvanced(
    isel: *Select,
    parent_alignment: InternPool.Alignment,
    offset_from_parent: u64,
    size: u64,
) Value.Index {
    defer isel.values.addOneAssumeCapacity().* = .{
        .refs = 0,
        .flags = .{
            .alignment = .fromLog2Units(@min(parent_alignment.toLog2Units(), @ctz(offset_from_parent))),
            .parent_tag = .unallocated,
            .location_tag = if (size > 16) .large else .small,
            .parts_len_minus_one = 0,
        },
        .offset_from_parent = offset_from_parent,
        .parent_payload = .{ .unallocated = {} },
        .location_payload = if (size > 16) .{ .large = .{
            .size = size,
        } } else .{ .small = .{
            .size = @intCast(size),
            .signedness = .unsigned,
            .class = .int,
            .modifier = .general,
            .hint = .zero,
            .register = .zero,
        } },
        .parts = undefined,
    };
    return @enumFromInt(isel.values.items.len);
}

pub fn dumpValues(isel: *Select, which: enum { only_referenced, all }) void {
    errdefer |err| @panic(@errorName(err));
    const stderr, _ = std.debug.lockStderrWriter(&.{});
    defer std.debug.unlockStderrWriter();

    const zcu = isel.pt.zcu;
    const gpa = zcu.gpa;
    const ip = &zcu.intern_pool;
    const nav = ip.getNav(isel.nav_index);

    var reverse_live_values: std.AutoArrayHashMapUnmanaged(Value.Index, std.ArrayListUnmanaged(Air.Inst.Index)) = .empty;
    defer {
        for (reverse_live_values.values()) |*list| list.deinit(gpa);
        reverse_live_values.deinit(gpa);
    }
    {
        try reverse_live_values.ensureTotalCapacity(gpa, isel.live_values.count());
        var live_val_it = isel.live_values.iterator();
        while (live_val_it.next()) |live_val_entry| switch (live_val_entry.value_ptr.*) {
            _ => {
                const gop = reverse_live_values.getOrPutAssumeCapacity(live_val_entry.value_ptr.*);
                if (!gop.found_existing) gop.value_ptr.* = .empty;
                try gop.value_ptr.append(gpa, live_val_entry.key_ptr.*);
            },
            .allocating, .free => unreachable,
        };
    }

    var reverse_live_registers: std.AutoHashMapUnmanaged(Value.Index, Register) = .empty;
    defer reverse_live_registers.deinit(gpa);
    {
        try reverse_live_registers.ensureTotalCapacity(gpa, @typeInfo(Register).@"enum".fields.len);
        var live_reg_it = isel.live_registers.iterator();
        while (live_reg_it.next()) |live_reg_entry| switch (live_reg_entry.value.*) {
            _ => reverse_live_registers.putAssumeCapacityNoClobber(live_reg_entry.value.*, live_reg_entry.key),
            .allocating, .free => {},
        };
    }

    var roots: std.AutoArrayHashMapUnmanaged(Value.Index, u32) = .empty;
    defer roots.deinit(gpa);
    {
        try roots.ensureTotalCapacity(gpa, isel.values.items.len);
        var vi: Value.Index = @enumFromInt(isel.values.items.len);
        while (@intFromEnum(vi) > 0) {
            vi = @enumFromInt(@intFromEnum(vi) - 1);
            if (which == .only_referenced and vi.get(isel).refs == 0) continue;
            while (true) switch (vi.parent(isel)) {
                .unallocated, .stack_slot, .constant => break,
                .value => |parent_vi| vi = parent_vi,
                .address => |address_vi| break roots.putAssumeCapacity(address_vi, 0),
            };
            roots.putAssumeCapacity(vi, 0);
        }
    }

    try stderr.print("# Begin {s} Value Dump: {f}:\n", .{ @typeName(Select), nav.fqn.fmt(ip) });
    while (roots.pop()) |root_entry| {
        const vi = root_entry.key;
        try stderr.splatByteAll(' ', 2 * (@as(usize, 1) + root_entry.value));
        try stderr.print("${d}", .{@intFromEnum(vi)});
        {
            var first = true;
            if (reverse_live_values.get(vi)) |aiis| for (aiis.items) |aii| {
                if (aii == Block.main) {
                    try stderr.print("{s}%main", .{if (first) " <- " else ", "});
                } else {
                    try stderr.print("{s}%{d}", .{ if (first) " <- " else ", ", @intFromEnum(aii) });
                }
                first = false;
            };
            if (reverse_live_registers.get(vi)) |ra| {
                try stderr.print("{s}{t}", .{ if (first) " <- " else ", ", ra });
                first = false;
            }
        }
        try stderr.writeByte(':');
        try isel.printValue(stderr, vi);
        try stderr.writeByte('\n');

        const value = vi.get(isel);
        var part_index = value.flags.parts_len_minus_one;
        if (part_index > 0) while (true) : (part_index -= 1) {
            try roots.put(
                gpa,
                @enumFromInt(@intFromEnum(value.parts) + part_index),
                root_entry.value + 1,
            );
            if (part_index == 0) break;
        };
    }
    try stderr.print("# End {s} Value Dump: {f}\n", .{ @typeName(Select), nav.fqn.fmt(ip) });
}

fn printValueAndParts(isel: *Select, writer: *std.Io.Writer, target_vi: Value.Index) !void {
    const zcu = isel.pt.zcu;
    const gpa = zcu.gpa;

    var roots: std.AutoArrayHashMapUnmanaged(Value.Index, u32) = .empty;
    defer roots.deinit(gpa);

    var root_vi = target_vi;
    while (true) switch (root_vi.parent(isel)) {
        .unallocated, .stack_slot, .constant => break,
        .value => |parent_vi| root_vi = parent_vi,
        .address => |address_vi| break try roots.put(gpa, address_vi, 0),
    };
    try roots.put(gpa, root_vi, 0);

    while (roots.pop()) |root_entry| {
        const vi = root_entry.key;
        try writer.splatByteAll(' ', 2 * root_entry.value);
        try isel.printValue(writer, vi);

        const value = vi.get(isel);
        var part_index = value.flags.parts_len_minus_one;
        if (part_index > 0) while (true) : (part_index -= 1) {
            try roots.put(
                gpa,
                @enumFromInt(@intFromEnum(value.parts) + part_index),
                root_entry.value + 1,
            );
            if (part_index == 0) break;
        };

        if (roots.count() != 0)
            try writer.writeByte('\n');
    }
}

fn printValue(isel: *Select, writer: *std.Io.Writer, vi: Value.Index) !void {
    const zcu = isel.pt.zcu;

    const value = vi.get(isel);
    try writer.print("${d}", .{@intFromEnum(vi)});
    try writer.writeByte(':');
    switch (value.flags.parent_tag) {
        .unallocated => if (value.offset_from_parent != 0) try writer.print(" +0x{x}", .{value.offset_from_parent}),
        .stack_slot => {
            try writer.print(" [{s}, #{s}0x{x}", .{
                @tagName(value.parent_payload.stack_slot.base),
                if (value.parent_payload.stack_slot.offset < 0) "-" else "",
                @abs(value.parent_payload.stack_slot.offset),
            });
            if (value.offset_from_parent != 0) try writer.print("+0x{x}", .{value.offset_from_parent});
            try writer.writeByte(']');
        },
        .value => try writer.print(" ${d}+0x{x}", .{ @intFromEnum(value.parent_payload.value), value.offset_from_parent }),
        .address => try writer.print(" ${d}[0x{x}]", .{ @intFromEnum(value.parent_payload.address), value.offset_from_parent }),
        .constant => try writer.print(" <{f}, {f}>", .{
            isel.fmtType(value.parent_payload.constant.typeOf(zcu)),
            isel.fmtConstant(value.parent_payload.constant),
        }),
    }
    try writer.print(" align({s})", .{@tagName(value.flags.alignment)});
    switch (value.flags.location_tag) {
        .large => try writer.print(" size=0x{x} large", .{value.location_payload.large.size}),
        .small => {
            const loc = value.location_payload.small;
            try writer.print(" size=0x{x}", .{loc.size});
            switch (loc.signedness) {
                .unsigned => {},
                .signed => try writer.writeAll(" signed"),
            }
            if (loc.hint != Register.zero) try writer.print(" hint={t}", .{loc.hint});
            if (loc.register != Register.zero) try writer.print(" loc={t}", .{loc.register});
            if (loc.class != .int) try writer.print(" class={t}", .{loc.class});
            if (loc.modifier != .general) try writer.print(" modifier={t}", .{loc.modifier});
        },
    }
    try writer.print(" refs={d}", .{value.refs});
}

fn fmtType(isel: *Select, ty: ZigType) ZigType.Formatter {
    return ty.fmt(isel.pt);
}

fn fmtConstant(isel: *Select, constant: Constant) @typeInfo(@TypeOf(Constant.fmtValue)).@"fn".return_type.? {
    return constant.fmtValue(isel.pt);
}

fn fmtValue(isel: *Select, vi: Value.Index) struct {
    isel: *Select,
    vi: Value.Index,
    pub fn format(data: @This(), writer: *std.Io.Writer) std.Io.Writer.Error!void {
        data.isel.printValueAndParts(writer, data.vi) catch |err| switch (err) {
            error.OutOfMemory => try writer.writeAll("OOM"),
            error.WriteFailed => return error.WriteFailed,
        };
    }
} {
    return .{ .isel = isel, .vi = vi };
}

fn use(isel: *Select, air_ref: Air.Inst.Ref) !Value.Index {
    const zcu = isel.pt.zcu;
    const ip = &zcu.intern_pool;
    try isel.values.ensureUnusedCapacity(zcu.gpa, 1);
    const vi, const ty = if (air_ref.toIndex()) |air_inst_index| vi_ty: {
        const live_gop = try isel.live_values.getOrPut(zcu.gpa, air_inst_index);
        if (live_gop.found_existing) return live_gop.value_ptr.*;
        const ty = isel.air.typeOf(air_ref, ip);
        const vi = isel.initValue(ty);
        tracking_log.debug("${d} <- %{d}", .{
            @intFromEnum(vi),
            @intFromEnum(air_inst_index),
        });
        live_gop.value_ptr.* = vi.ref(isel);
        break :vi_ty .{ vi, ty };
    } else vi_ty: {
        const constant: Constant = .fromInterned(air_ref.toInterned().?);
        const ty = constant.typeOf(zcu);
        const vi = isel.initValue(ty);
        tracking_log.debug("${d} <- <{f}, {f}>", .{
            @intFromEnum(vi),
            isel.fmtType(ty),
            isel.fmtConstant(constant),
        });
        vi.setParent(isel, .{ .constant = constant });
        break :vi_ty .{ vi, ty };
    };
    if (ty.isAbiInt(zcu)) {
        const int_info = ty.intInfo(zcu);
        if (int_info.bits <= 16) vi.setSignedness(isel, int_info.signedness);
    }
    return vi;
}

fn fill(isel: *Select, dst: Register) error{ OutOfMemory, CodegenFail }!bool {
    switch (dst) {
        else => {},
        Register.zero, Register.ra, Register.tp, Register.sp, Register.fp => return false,
    }
    const dst_live_vi = isel.live_registers.getPtr(dst);
    const dst_vi = switch (dst_live_vi.*) {
        _ => |dst_vi| dst_vi,
        .allocating => return false,
        .free => return true,
    };
    const src = src: {
        if (dst_vi.hint(isel)) |hint| {
            assert(dst_live_vi.* == dst_vi);
            dst_live_vi.* = .allocating;
            defer dst_live_vi.* = dst_vi;
            if (try isel.fill(hint)) {
                isel.saved_registers.insert(hint);
                break :src hint;
            }
        }
        switch (isel.tryAllocReg(dst_vi.registerClass(isel))) {
            .allocated => |reg| break :src reg,
            .fill_candidate, .out_of_registers => return isel.fillMemory(dst),
        }
    };
    try dst_vi.liveIn(isel, src, comptime &.initFill(.free));
    const src_live_vi = isel.live_registers.getPtr(src);
    assert(src_live_vi.* == .allocating);
    src_live_vi.* = dst_vi;
    return true;
}

fn fillMemory(isel: *Select, dst: Register) error{ OutOfMemory, CodegenFail }!bool {
    _ = dst;
    return isel.fail("TODO fillMemory", .{});
}

fn merge(
    isel: *Select,
    expected_live_registers: *const LiveRegisters,
    comptime opts: struct { fill_extra: bool = false },
) !void {
    var live_reg_it = isel.live_registers.iterator();
    while (live_reg_it.next()) |live_reg_entry| {
        const ra = live_reg_entry.key;
        const actual_vi = live_reg_entry.value;
        const expected_vi = expected_live_registers.get(ra);
        switch (expected_vi) {
            else => switch (actual_vi.*) {
                _ => {},
                .allocating => unreachable,
                .free => actual_vi.* = .allocating,
            },
            .free => {},
        }
    }
    live_reg_it = isel.live_registers.iterator();
    while (live_reg_it.next()) |live_reg_entry| {
        const ra = live_reg_entry.key;
        const actual_vi = live_reg_entry.value;
        const expected_vi = expected_live_registers.get(ra);
        switch (expected_vi) {
            _ => {
                switch (actual_vi.*) {
                    _ => _ = if (opts.fill_extra) {
                        assert(try isel.fillMemory(ra));
                        assert(actual_vi.* == .free);
                    },
                    .allocating => actual_vi.* = .free,
                    .free => unreachable,
                }
                try expected_vi.liveIn(isel, ra, expected_live_registers);
            },
            .allocating => if (if (opts.fill_extra) try isel.fillMemory(ra) else try isel.fill(ra)) {
                assert(actual_vi.* == .free);
                actual_vi.* = .allocating;
            },
            .free => if (opts.fill_extra) assert(try isel.fillMemory(ra) and actual_vi.* == .free),
        }
    }
    live_reg_it = isel.live_registers.iterator();
    while (live_reg_it.next()) |live_reg_entry| {
        const ra = live_reg_entry.key;
        const actual_vi = live_reg_entry.value;
        const expected_vi = expected_live_registers.get(ra);
        switch (expected_vi) {
            _ => {
                assert(actual_vi.* == .allocating and expected_vi.register(isel) == ra);
                actual_vi.* = expected_vi;
            },
            .allocating => assert(actual_vi.* == .allocating),
            .free => if (opts.fill_extra) assert(actual_vi.* == .free),
        }
    }
}

const TryAllocRegResult = union(enum) {
    allocated: Register,
    fill_candidate: Register,
    out_of_registers,
};

fn tryAllocReg(isel: *Select, class: Register.Class) TryAllocRegResult {
    var failed_result: TryAllocRegResult = .out_of_registers;
    var reg: Register, const last_reg: Register = switch (class) {
        .int => .{ .r0, .r31 },
        .fp => .{ .f0, .f31 },
        .fcc => .{ .fcc0, .fcc7 },
    };
    while (true) : (reg = @enumFromInt(@intFromEnum(reg) + 1)) {
        if (reg == Register.zero) continue;
        if (reg == Register.sp) continue;
        if (reg == Register.fp) continue;
        const live_vi = isel.live_registers.getPtr(reg);
        switch (live_vi.*) {
            _ => switch (failed_result) {
                .allocated => unreachable,
                .fill_candidate => {},
                .out_of_registers => failed_result = .{ .fill_candidate = reg },
            },
            .allocating => {},
            .free => {
                live_vi.* = .allocating;
                isel.saved_registers.insert(reg);
                return .{ .allocated = reg };
            },
        }
        if (reg == last_reg) return failed_result;
    }
}

fn allocReg(isel: *Select, class: Register.Class) !Register {
    switch (isel.tryAllocReg(class)) {
        .allocated => |reg| return reg,
        .fill_candidate => |reg| {
            assert(try isel.fillMemory(reg));
            const live_vi = isel.live_registers.getPtr(reg);
            assert(live_vi.* == .free);
            live_vi.* = .allocating;
            return reg;
        },
        .out_of_registers => return isel.fail("ran out of {t} registers", .{class}),
    }
}

const RegLock = struct {
    reg: Register,
    const empty: RegLock = .{ .reg = .zero };
    fn unlock(lock: RegLock, isel: *Select) void {
        switch (lock.reg) {
            else => |reg| isel.freeReg(reg),
            Register.zero => {},
        }
    }
};

fn lockReg(isel: *Select, reg: Register) RegLock {
    assert(reg != Register.zero);
    const live_vi = isel.live_registers.getPtr(reg);
    assert(live_vi.* == .free);
    live_vi.* = .allocating;
    return .{ .reg = reg };
}

fn tryLockReg(isel: *Select, reg: Register) RegLock {
    assert(reg != Register.zero);
    const live_vi = isel.live_registers.getPtr(reg);
    switch (live_vi.*) {
        _ => unreachable,
        .allocating => return .{ .reg = .zero },
        .free => {
            live_vi.* = .allocating;
            return .{ .reg = reg };
        },
    }
}

fn freeReg(isel: *Select, reg: Register) void {
    assert(reg != Register.zero);
    const live_vi = isel.live_registers.getPtr(reg);
    assert(live_vi.* == .allocating);
    live_vi.* = .free;
}

/// Loads from memory [base + offset] to register
fn loadReg(
    isel: *Select,
    dst: Register,
    size: u64,
    signedness: std.builtin.Signedness,
    base: Register,
    offset: i64,
) !void {
    if (dst.class() != .int) return isel.fail("TODO loadReg {t}", .{dst});
    switch (size) {
        0 => unreachable,
        1 => {
            if (std.math.cast(i12, offset)) |small_off| return isel.emit(switch (signedness) {
                .signed => .@"ld.b"(dst, base, small_off),
                .unsigned => .@"ld.bu"(dst, base, small_off),
            });
        },
        2 => {
            if (std.math.cast(i12, offset)) |small_off| return isel.emit(switch (signedness) {
                .signed => .@"ld.h"(dst, base, small_off),
                .unsigned => .@"ld.hu"(dst, base, small_off),
            });
        },
        4 => {
            if (std.math.cast(i12, offset)) |small_off| return isel.emit(switch (signedness) {
                .signed => .@"ld.w"(dst, base, small_off),
                .unsigned => .@"ld.wu"(dst, base, small_off),
            });
            if (signedness == .signed) if (std.math.cast(i16, offset)) |small_off| {
                return isel.emit(.@"ldox4.w"(dst, base, @intCast(@divExact(small_off, 4))));
            };
        },
        8 => {
            if (std.math.cast(i12, offset)) |small_off| return isel.emit(.@"ld.d"(dst, base, small_off));
            if (std.math.cast(i16, offset)) |small_off| return isel.emit(.@"ldox4.d"(dst, base, @intCast(@divExact(small_off, 4))));
        },
        else => return isel.fail("bad load size: {d}", .{size}),
    }

    const ptr_reg = try isel.allocReg(.int);
    defer isel.freeReg(ptr_reg);
    switch (size) {
        1 => try isel.emit(switch (signedness) {
            .signed => .@"ldx.b"(dst, base, ptr_reg),
            .unsigned => .@"ldx.bu"(dst, base, ptr_reg),
        }),
        2 => try isel.emit(switch (signedness) {
            .signed => .@"ldx.h"(dst, base, ptr_reg),
            .unsigned => .@"ldx.hu"(dst, base, ptr_reg),
        }),
        4 => try isel.emit(switch (signedness) {
            .signed => .@"ldx.w"(dst, base, ptr_reg),
            .unsigned => .@"ldx.wu"(dst, base, ptr_reg),
        }),
        8 => try isel.emit(.@"ldx.d"(dst, base, ptr_reg)),
        else => {
            try isel.storeReg(dst, size, ptr_reg, 0);
            try isel.emit(.@"add.d"(ptr_reg, ptr_reg, base));
        },
    }
    try isel.moveImm(ptr_reg, offset);
}

/// Stores a register to memory [base + offset]
fn storeReg(
    isel: *Select,
    src: Register,
    size: u64,
    base: Register,
    offset: i64,
) !void {
    if (src.class() != .int) return isel.fail("TODO storeReg {t}", .{src});
    switch (size) {
        0 => unreachable,
        1 => {
            if (std.math.cast(i12, offset)) |small_off| return isel.emit(.@"st.b"(src, base, small_off));
        },
        2 => {
            if (std.math.cast(i12, offset)) |small_off| return isel.emit(.@"st.h"(src, base, small_off));
        },
        4 => {
            if (std.math.cast(i12, offset)) |small_off| return isel.emit(.@"st.w"(src, base, small_off));
            if (std.math.cast(i16, offset)) |small_off| return isel.emit(.@"stox4.w"(src, base, @intCast(@divExact(small_off, 4))));
        },
        8 => {
            if (std.math.cast(i12, offset)) |small_off| return isel.emit(.@"st.d"(src, base, small_off));
            if (std.math.cast(i16, offset)) |small_off| return isel.emit(.@"stox4.d"(src, base, @intCast(@divExact(small_off, 4))));
        },
        else => return isel.fail("bad store size: {d}", .{size}),
    }

    const ptr_reg = try isel.allocReg(.int);
    defer isel.freeReg(ptr_reg);
    switch (size) {
        1 => try isel.emit(.@"stx.b"(src, base, ptr_reg)),
        2 => try isel.emit(.@"stx.h"(src, base, ptr_reg)),
        4 => try isel.emit(.@"stx.w"(src, base, ptr_reg)),
        8 => try isel.emit(.@"stx.d"(src, base, ptr_reg)),
        else => {
            try isel.storeReg(src, size, ptr_reg, 0);
            try isel.emit(.@"add.d"(ptr_reg, ptr_reg, base));
        },
    }
    try isel.moveImm(ptr_reg, offset);
}

/// Moves an immediate to a register.
fn moveImm(isel: *Select, rd: Register, si64: i64) !void {
    wip_mir_log.debug("  | # moveImm {t}, 0x{x}", .{ rd, si64 });
    // fast path
    if (std.math.cast(u12, si64)) |imm12| return isel.emit(.ori(rd, .zero, imm12));

    // full path
    const ori12: u12 = @truncate(@as(u64, @bitCast(si64)));
    const lu12i20: i20 = @truncate(si64 >> 12);
    const use_lu12iw = lu12i20 != 0;
    const lu32i20: i20 = @truncate(si64 >> 32);
    const use_lu32id = lu32i20 != hi: {
        if (use_lu12iw) break :hi @as(i20, @intCast(@as(i1, @truncate(si64 >> 31))));
        break :hi 0;
    };
    const lu52i12: i12 = @truncate(si64 >> 52);
    const use_lu52id = lu52i12 != hi: {
        if (use_lu32id) break :hi @as(i12, @intCast(@as(i1, @truncate(si64 >> 51))));
        if (use_lu12iw) break :hi @as(i12, @intCast(@as(i1, @truncate(si64 >> 31))));
        break :hi 0;
    };
    const use_ori = (ori12 != 0) or (!use_lu12iw and use_lu32id) or si64 == 0;
    const ori_rj = if (use_lu12iw) rd else Register.zero;
    const lu52id_rj = if (use_ori or use_lu12iw) rd else Register.zero;

    if (use_lu52id) try isel.emit(.@"cu52i.d"(rd, lu52id_rj, lu52i12));
    if (use_lu32id) try isel.emit(.@"cu32i.d"(rd, lu32i20));
    if (use_ori) try isel.emit(.ori(rd, ori_rj, ori12));
    if (use_lu12iw) try isel.emit(.@"lu12i.w"(rd, lu12i20));
}

const AddOrSubtractOptions = struct {
    overflow: Overflow,

    const Overflow = union(enum) {
        @"unreachable",
        panic: Zcu.SimplePanicId,
        wrap,
        reg: Register,
    };
};

fn addOrSubtract(
    isel: *Select,
    ty: ZigType,
    res_vi: Value.Index,
    op: enum { add, sub },
    lhs_vi: Value.Index,
    rhs_vi: Value.Index,
    opts: AddOrSubtractOptions,
) !void {
    _ = opts; // TODO: overflow
    const zcu = isel.pt.zcu;
    assert(ty.isAbiInt(zcu));
    const int_info = ty.intInfo(zcu);

    if (int_info.bits <= 32) {
        const res_reg = try res_vi.defReg(isel) orelse return;
        const lhs_mat = try lhs_vi.matReg(isel);
        const rhs_mat = try rhs_vi.matReg(isel);

        if (int_info.bits < 32)
            try isel.emit(.@"bstrpick.w"(res_reg, res_reg, @intCast(int_info.bits - 1), 0));
        switch (op) {
            .add => try isel.emit(.@"add.w"(res_reg, lhs_mat.reg, rhs_mat.reg)),
            .sub => try isel.emit(.@"sub.w"(res_reg, lhs_mat.reg, rhs_mat.reg)),
        }

        try lhs_mat.finish(isel);
        try rhs_mat.finish(isel);
    } else if (int_info.bits <= 64) {
        const res_reg = try res_vi.defReg(isel) orelse return;
        const lhs_mat = try lhs_vi.matReg(isel);
        const rhs_mat = try rhs_vi.matReg(isel);

        if (int_info.bits < 64)
            try isel.emit(.@"bstrpick.d"(res_reg, res_reg, @intCast(int_info.bits - 1), 0));
        switch (op) {
            .add => try isel.emit(.@"add.d"(res_reg, lhs_mat.reg, rhs_mat.reg)),
            .sub => try isel.emit(.@"sub.d"(res_reg, lhs_mat.reg, rhs_mat.reg)),
        }

        try lhs_mat.finish(isel);
        try rhs_mat.finish(isel);
    } else return isel.fail("unimplemented {t} {f}", .{ op, isel.fmtType(ty) });
}

pub const CallAbiIterator = struct {
    isel: *Select,
    cc: *const std.builtin.CallingConvention,
    next_reg: std.EnumArray(RegisterClass, Register) = .init(.{
        .gpr = .r4,
        .fpr = .f0,
        .ret_byref = .r4,
    }),
    next_stack: usize = 0,

    const RegisterClass = enum {
        gpr,
        fpr,
        /// Virtual register class, for allocating GPRs for by-reference returning.
        ret_byref,
    };

    // fn hasNonZeroPtr(it: *CallAbiIterator, ty: ZigType) bool {
    //     const zcu = it.isel.pt.zcu;
    //     return switch (ty.zigTypeTag(zcu)) {
    //         .pointer => switch (ty.ptrSize(zcu)) {
    //             .c => false,
    //             else => true,
    //         },
    //         .@"struct", .@"union" => ty.bitSize(zcu) > (2 * it.isel.target.ptrBitWidth()),
    //         else => false,
    //     };
    // }

    fn allocReg(it: *CallAbiIterator, class: RegisterClass) ?Register {
        const last_reg: Register = switch (class) {
            .gpr, .ret_byref => .r11,
            .fpr => .f7,
        };
        const next = it.next_reg.getPtr(class);
        if (@intFromEnum(last_reg) >= @intFromEnum(next.*)) {
            const allocated = next.*;
            next.* = @enumFromInt(@intFromEnum(allocated) + 1);
            return allocated;
        } else return null;
    }

    /// Trys to allocate some registers, returning amount of allocated registers.
    fn allocRegs(it: *CallAbiIterator, class: RegisterClass, result: []Register) usize {
        const last_reg: Register = switch (class) {
            .gpr, .ret_byref => .r11,
            .fpr => .f7,
        };
        const next = it.next_reg.getPtr(class);
        const remaining = @intFromEnum(last_reg) - @intFromEnum(next.*) + 1;
        if (remaining >= result.len) {
            for (result, @intFromEnum(next.*)..) |*v, reg| v.* = @enumFromInt(reg);
            next.* = @enumFromInt(@intFromEnum(next.*) + result.len);
            return result.len;
        } else {
            for (@intFromEnum(next.*)..@intFromEnum(next.*) + remaining, result) |reg, *v| v.* = @enumFromInt(reg);
            next.* = @enumFromInt(@intFromEnum(next.*) + remaining);
            return remaining;
        }
    }

    fn assignStack(it: *CallAbiIterator, wip_vi: Value.Index) void {
        const isel = it.isel;
        it.next_stack = @intCast(wip_vi.alignment(isel).forward(it.next_stack));
        const parent_vi = switch (wip_vi.parent(isel)) {
            .unallocated, .stack_slot => wip_vi,
            .address, .constant => unreachable,
            .value => |parent_vi| parent_vi,
        };
        switch (parent_vi.parent(isel)) {
            .unallocated => parent_vi.setParent(isel, .{ .stack_slot = .{
                .base = .sp,
                .offset = @intCast(it.next_stack),
            } }),
            .stack_slot => {},
            .address, .value, .constant => unreachable,
        }
        it.next_stack += @intCast(wip_vi.size(isel));
    }

    fn assignUsize(it: *CallAbiIterator, isel: *Select, wip_vi: Value.Index) void {
        if (it.allocReg(.gpr)) |reg| {
            wip_vi.setHint(isel, reg);
        } else it.assignStack(wip_vi);
    }

    fn assignIndirect(it: *CallAbiIterator, isel: *Select, wip_vi: Value.Index, is_return: bool) void {
        const wip_address_vi = isel.initValue(.usize);
        wip_vi.setParent(isel, .{ .address = wip_address_vi });

        if (it.allocReg(if (is_return) .ret_byref else .gpr)) |reg| {
            wip_address_vi.setHint(isel, reg);
        } else it.assignStack(wip_address_vi);
    }

    pub fn resolve(it: *CallAbiIterator, ty: ZigType, is_return: bool) !?Value.Index {
        const isel = it.isel;
        const zcu = isel.pt.zcu;
        const ip = &zcu.intern_pool;

        if (ty.isNoReturn(zcu) or !ty.hasRuntimeBitsIgnoreComptime(zcu)) return null;
        try isel.values.ensureUnusedCapacity(zcu.gpa, Value.max_parts);
        const wip_vi = isel.initValue(ty);

        const grlen = isel.target.ptrBitWidth();
        const grlen_bytes = @divExact(grlen, 8);

        type_key: switch (ip.indexToKey(ty.toIntern())) {
            else => return isel.fail("CallAbiIterator.resolve({f})", .{isel.fmtType(ty)}),
            .int_type => |int_ty| {
                if (int_ty.bits <= grlen) {
                    it.assignUsize(isel, wip_vi);
                } else if (int_ty.bits <= 2 * grlen) {
                    var regs: [2]Register = undefined;
                    const allocated_regs = it.allocRegs(.gpr, &regs);
                    switch (allocated_regs) {
                        0 => it.assignStack(wip_vi),
                        1 => {
                            wip_vi.setParts(isel, 2);
                            wip_vi.addPart(isel, 0, grlen_bytes).setHint(isel, regs[0]);
                            it.assignStack(wip_vi.addPart(isel, grlen_bytes, @divExact(int_ty.bits - grlen, 8)));
                        },
                        2 => {
                            wip_vi.setParts(isel, 2);
                            wip_vi.addPart(isel, 0, grlen_bytes).setHint(isel, regs[0]);
                            wip_vi.addPart(isel, grlen_bytes, @divExact(int_ty.bits - grlen, 8)).setHint(isel, regs[1]);
                        },
                        else => unreachable,
                    }
                } else it.assignStack(wip_vi);
            },
            .ptr_type => |ptr_type| switch (ptr_type.flags.size) {
                .one, .many, .c => it.assignUsize(isel, wip_vi),
                .slice => continue :type_key .{ .int_type = .{
                    .signedness = .unsigned,
                    .bits = 2 * grlen,
                } },
            },
            .opt_type => |child_type| if (ty.optionalReprIsPayload(zcu))
                continue :type_key ip.indexToKey(child_type)
            else
                it.assignStack(wip_vi), // TODO optimize this
            .anyframe_type => unreachable,
            .simple_type => |simple_type| switch (simple_type) {
                .f80 => continue :type_key .{ .int_type = .{ .signedness = .unsigned, .bits = 80 } },
                .usize,
                .isize,
                .c_char,
                .c_short,
                .c_ushort,
                .c_int,
                .c_uint,
                .c_long,
                .c_ulong,
                .c_longlong,
                .c_ulonglong,
                => continue :type_key .{ .int_type = ty.intInfo(zcu) },
                .anyopaque, .bool => it.assignUsize(isel, wip_vi),
                .anyerror => continue :type_key .{ .int_type = .{
                    .signedness = .unsigned,
                    .bits = zcu.errorSetBits(),
                } },
                .f16, .f32, .f64, .f128, .c_longdouble => return isel.fail("CallAbiIterator.resolve({t})", .{simple_type}),
                else => return isel.fail("CallAbiIterator.resolve({t})", .{simple_type}),
            },
            .struct_type, .union_type => {
                // TODO: implement floating-point structures rules defined in lapcs
                const ty_size = ty.bitSize(zcu);
                if (ty_size <= (2 * grlen))
                    continue :type_key .{ .int_type = .{ .signedness = .unsigned, .bits = @intCast(ty_size) } };
                it.assignIndirect(isel, wip_vi, is_return);
            },
            // .tuple_type => |tuple_ty| {},
            .opaque_type, .func_type => continue :type_key .{ .simple_type = .anyopaque },
            .enum_type => continue :type_key ip.indexToKey(ip.loadEnumType(ty.toIntern()).tag_ty),
            .error_set_type,
            .inferred_error_set_type,
            => continue :type_key .{ .simple_type = .anyerror },
        }

        if (is_return) {
            it.next_reg = .init(.{
                .gpr = it.next_reg.get(.ret_byref), // skip registers for by-ref returning
                .fpr = .f0,
                .ret_byref = .zero,
            });
            it.next_stack = 0;
            abi_log.debug("| Return: {f} -> {f}", .{ isel.fmtType(ty), isel.fmtValue(wip_vi) });
        } else {
            abi_log.debug("| Param: {f} -> {f}", .{ isel.fmtType(ty), isel.fmtValue(wip_vi) });
        }

        return wip_vi.ref(isel);
    }
};

const call = struct {
    const param_reg: Value.Index = @enumFromInt(@intFromEnum(Value.Index.allocating) - 2);
    const callee_clobbered_reg: Value.Index = @enumFromInt(@intFromEnum(Value.Index.allocating) - 1);
    const caller_saved_regs: LiveRegisters = .init(.{
        .r0 = .free,
        .r1 = callee_clobbered_reg,
        .r2 = .free,
        .r3 = .free,
        .r4 = param_reg,
        .r5 = param_reg,
        .r6 = param_reg,
        .r7 = param_reg,
        .r8 = param_reg,
        .r9 = param_reg,
        .r10 = param_reg,
        .r11 = param_reg,
        .r12 = callee_clobbered_reg,
        .r13 = callee_clobbered_reg,
        .r14 = callee_clobbered_reg,
        .r15 = callee_clobbered_reg,
        .r16 = callee_clobbered_reg,
        .r17 = callee_clobbered_reg,
        .r18 = callee_clobbered_reg,
        .r19 = callee_clobbered_reg,
        .r20 = callee_clobbered_reg,
        .r21 = .free,
        .r22 = .free,
        .r23 = .free,
        .r24 = .free,
        .r25 = .free,
        .r26 = .free,
        .r27 = .free,
        .r28 = .free,
        .r29 = .free,
        .r30 = .free,
        .r31 = .free,

        .f0 = param_reg,
        .f1 = param_reg,
        .f2 = param_reg,
        .f3 = param_reg,
        .f4 = param_reg,
        .f5 = param_reg,
        .f6 = param_reg,
        .f7 = param_reg,
        .f8 = callee_clobbered_reg,
        .f9 = callee_clobbered_reg,
        .f10 = callee_clobbered_reg,
        .f11 = callee_clobbered_reg,
        .f12 = callee_clobbered_reg,
        .f13 = callee_clobbered_reg,
        .f14 = callee_clobbered_reg,
        .f15 = callee_clobbered_reg,
        .f16 = callee_clobbered_reg,
        .f17 = callee_clobbered_reg,
        .f18 = callee_clobbered_reg,
        .f19 = callee_clobbered_reg,
        .f20 = callee_clobbered_reg,
        .f21 = callee_clobbered_reg,
        .f22 = callee_clobbered_reg,
        .f23 = callee_clobbered_reg,
        .f24 = .free,
        .f25 = .free,
        .f26 = .free,
        .f27 = .free,
        .f28 = .free,
        .f29 = .free,
        .f30 = .free,
        .f31 = .free,

        .fcc0 = callee_clobbered_reg,
        .fcc1 = callee_clobbered_reg,
        .fcc2 = callee_clobbered_reg,
        .fcc3 = callee_clobbered_reg,
        .fcc4 = callee_clobbered_reg,
        .fcc5 = callee_clobbered_reg,
        .fcc6 = callee_clobbered_reg,
        .fcc7 = callee_clobbered_reg,
    });

    fn prepareReturn(isel: *Select) !void {
        var live_reg_it = isel.live_registers.iterator();
        while (live_reg_it.next()) |live_reg_entry| switch (caller_saved_regs.get(live_reg_entry.key)) {
            else => unreachable,
            param_reg, callee_clobbered_reg => switch (live_reg_entry.value.*) {
                _ => {},
                .allocating => unreachable,
                .free => live_reg_entry.value.* = .allocating,
            },
            .free => {},
        };
    }

    fn returnFill(isel: *Select, reg: Register) !void {
        const live_vi = isel.live_registers.getPtr(reg);
        if (try isel.fill(reg)) {
            assert(live_vi.* == .free);
            live_vi.* = .allocating;
        }
        assert(live_vi.* == .allocating);
    }

    const IndirectValue = struct {
        value_vi: Value.Index,
        addr_vi: Value.Index,
    };

    /// Allocates stack-slots for by-reference returning.
    ///
    /// Caller owns returned memory. Caller owns references to addr_vi.
    fn returnAllocIndirect(isel: *Select, vi: Value.Index) ![]IndirectValue {
        var allocated: std.ArrayList(IndirectValue) = .empty;
        try returnAllocIndirectDfs(isel, vi, &allocated);
        return try allocated.toOwnedSlice(isel.pt.zcu.gpa);
    }
    fn returnAllocIndirectDfs(isel: *Select, vi: Value.Index, allocated: *std.ArrayList(IndirectValue)) !void {
        switch (vi.parent(isel)) {
            .unallocated => {
                var vi_parts_it = vi.parts(isel);
                while (vi_parts_it.next()) |vi_part|
                    if (vi_part != vi) try returnAllocIndirectDfs(isel, vi_part, allocated);
            },
            .stack_slot => {},
            .value, .constant => unreachable,
            .address => |addr_vi| {
                const stack_slot = vi.allocStackSlot(isel);
                vi.setParent(isel, .{ .stack_slot = stack_slot });
                try allocated.append(isel.pt.zcu.gpa, .{ .value_vi = vi, .addr_vi = addr_vi });
                return;
            },
        }
    }

    fn finishReturn(isel: *Select) !void {
        var live_reg_it = isel.live_registers.iterator();
        while (live_reg_it.next()) |live_reg_entry| {
            switch (live_reg_entry.value.*) {
                _ => |live_vi| switch (live_vi.size(isel)) {
                    else => unreachable,
                    1, 2, 4, 8 => {},
                    16 => {
                        assert(try isel.fillMemory(live_reg_entry.key));
                        assert(live_reg_entry.value.* == .free);
                        switch (caller_saved_regs.get(live_reg_entry.key)) {
                            else => unreachable,
                            param_reg, callee_clobbered_reg => live_reg_entry.value.* = .allocating,
                            .free => {},
                        }
                        continue;
                    },
                },
                .allocating, .free => {},
            }
            switch (caller_saved_regs.get(live_reg_entry.key)) {
                else => unreachable,
                param_reg, callee_clobbered_reg => switch (live_reg_entry.value.*) {
                    _ => {
                        assert(try isel.fill(live_reg_entry.key));
                        assert(live_reg_entry.value.* == .free);
                        live_reg_entry.value.* = .allocating;
                    },
                    .allocating => {},
                    .free => unreachable,
                },
                .free => {},
            }
        }
    }
    fn prepareCallee(isel: *Select) !void {
        var live_reg_it = isel.live_registers.iterator();
        while (live_reg_it.next()) |live_reg_entry| switch (caller_saved_regs.get(live_reg_entry.key)) {
            else => unreachable,
            param_reg => assert(live_reg_entry.value.* == .allocating),
            callee_clobbered_reg => isel.freeReg(live_reg_entry.key),
            .free => {},
        };
    }
    fn finishCallee(_: *Select) !void {}
    fn prepareParams(_: *Select) !void {}
    fn paramLiveOut(isel: *Select, vi: Value.Index, reg: Register) !void {
        isel.freeReg(reg);
        try vi.liveOut(isel, reg);
        const live_vi = isel.live_registers.getPtr(reg);
        if (live_vi.* == .free) live_vi.* = .allocating;
    }
    fn finishParams(isel: *Select) !void {
        var live_reg_it = isel.live_registers.iterator();
        while (live_reg_it.next()) |live_reg_entry| switch (caller_saved_regs.get(live_reg_entry.key)) {
            else => unreachable,
            param_reg => switch (live_reg_entry.value.*) {
                _ => {},
                .allocating => live_reg_entry.value.* = .free,
                .free => unreachable,
            },
            callee_clobbered_reg, .free => {},
        };
    }
};

const Air = @import("../../Air.zig");
const assert = std.debug.assert;
const codegen = @import("../../codegen.zig");
const Constant = @import("../../Value.zig");
const InternPool = @import("../../InternPool.zig");
const Package = @import("../../Package.zig");
const Select = @This();
const std = @import("std");
const tracking_log = std.log.scoped(.tracking);
const wip_mir_log = std.log.scoped(.@"wip-mir");
const abi_log = std.log.scoped(.abi);
const Zcu = @import("../../Zcu.zig");
const ZigType = @import("../../Type.zig");
