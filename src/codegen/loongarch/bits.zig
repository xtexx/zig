const std = @import("std");
const Target = std.Target;
const expectEqual = std.testing.expectEqual;
const Writer = std.Io.Writer;

const InternPool = @import("../../InternPool.zig");

/// Register, one per set of aliasing registers
pub const Register = enum(u7) {
    // zig fmt: off
    // integer registers
    r0, r1, r2, r3, r4, r5, r6, r7,
    r8, r9, r10, r11, r12, r13, r14, r15,
    r16, r17, r18, r19, r20, r21, r22, r23,
    r24, r25, r26, r27, r28, r29, r30, r31,

    // float-point/LSX/LASX registers
    f0, f1, f2, f3, f4, f5, f6, f7,
    f8, f9, f10, f11, f12, f13, f14, f15,
    f16, f17, f18, f19, f20, f21, f22, f23,
    f24, f25, f26, f27, f28, f29, f30, f31,

    // float-point condition code registers
    fcc0, fcc1, fcc2, fcc3, fcc4, fcc5, fcc6, fcc7,
    // zig fmt: on

    pub const zero: Register = .r0;
    pub const ra: Register = .r1;
    pub const tp: Register = .r2;
    pub const sp: Register = .r3;
    pub const fp: Register = .r22;
    pub const t0: Register = .r12;
    pub const t1: Register = .r13;
    pub const t2: Register = .r14;
    pub const t3: Register = .r15;

    pub const Class = enum { int, fp, fcc };
    pub const Modifier = enum { general, lsx, lasx };

    pub fn class(reg: Register) Class {
        return switch (@intFromEnum(reg)) {
            @intFromEnum(Register.r0)...@intFromEnum(Register.r31) => .int,
            @intFromEnum(Register.f0)...@intFromEnum(Register.f31) => .fp,
            @intFromEnum(Register.fcc0)...@intFromEnum(Register.fcc7) => .fcc,
            else => unreachable,
        };
    }

    pub fn encode(reg: Register) u5 {
        const base: u7 = switch (@intFromEnum(reg)) {
            @intFromEnum(Register.r0)...@intFromEnum(Register.r31) => @intFromEnum(Register.r0),
            @intFromEnum(Register.f0)...@intFromEnum(Register.f31) => @intFromEnum(Register.f0),
            @intFromEnum(Register.fcc0)...@intFromEnum(Register.fcc7) => @intFromEnum(Register.fcc0),
            else => unreachable,
        };
        return @intCast(@intFromEnum(reg) - base);
    }

    pub fn decode(reg_class: Class, reg: u5) Register {
        const base: u7 = switch (reg_class) {
            .int => @intFromEnum(Register.r0),
            .fp => @intFromEnum(Register.f0),
            .fcc => @intFromEnum(Register.fcc0),
        };
        return @enumFromInt(base + @as(u7, reg));
    }
};

test "register classes" {
    try expectEqual(.int, Register.r0.class());
    try expectEqual(.int, Register.r31.class());
    try expectEqual(.float, Register.f0.class());
    try expectEqual(.float, Register.f31.class());
    try expectEqual(.fcc, Register.fcc0.class());
    try expectEqual(.fcc, Register.fcc7.class());
}

test "register encoding" {
    try expectEqual(0, Register.r0.encode());
    try expectEqual(31, Register.r31.encode());
    try expectEqual(0, Register.f0.encode());
    try expectEqual(31, Register.f31.encode());
    try expectEqual(0, Register.fcc0.encode());
    try expectEqual(7, Register.fcc7.encode());
}

test "register decoding" {
    try expectEqual(.r0, Register.decode(.int, 0));
    try expectEqual(.r31, Register.decode(.int, 31));
    try expectEqual(.f0, Register.decode(.fp, 0));
    try expectEqual(.f31, Register.decode(.fp, 31));
    try expectEqual(.fcc0, Register.decode(.fcc, 0));
    try expectEqual(.fcc7, Register.decode(.fcc, 7));
}
