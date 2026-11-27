// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue
//
// Zig 0.17.0 compile-time (`comptime`) + runtime verifier for Pillar II:
//   1. `comptime` verification of maximal-cardinality Megyesi t-RQLS(q) for
//      F_7 (t=1), F_9 (t=2), F_11 (t=3), F_13 (t=4), F_16 (t=3), F_17 (t=6), F_19 (t=7)
//   2. Exhaustive runtime proof over ALL 7! = 5,040 permutations of F_8 (mu(0)=0):
//      168 F_2-linear (48 orthomorphisms), 4,872 non-linear (0 with t >= 1!)
//   3. Exhaustive runtime audit over ALL 6! = 720 permutations of F_7 (mu(0)=0):
//      exactly 84 non-linear maximal-cardinality 1-RQLS(7) maps!

const std = @import("std");

fn gf8Mul(a_in: u8, b_in: u8) u8 {
    var a: u8 = a_in;
    var b: u8 = b_in;
    var r: u8 = 0;
    for (0..3) |_| {
        if ((b & 1) != 0) r ^= a;
        const hi = a & 4;
        a = (a << 1) & 7;
        if (hi != 0) a ^= 3;
        b >>= 1;
    }
    return r;
}

fn gf16Mul(a_in: u8, b_in: u8) u8 {
    var a: u8 = a_in;
    var b: u8 = b_in;
    var r: u8 = 0;
    for (0..4) |_| {
        if ((b & 1) != 0) r ^= a;
        const hi = a & 8;
        a = (a << 1) & 15;
        if (hi != 0) a ^= 3;
        b >>= 1;
    }
    return r;
}

fn gf16Trace(x: u8) u8 {
    const x2 = gf16Mul(x, x);
    const x4 = gf16Mul(x2, x2);
    const x8 = gf16Mul(x4, x4);
    return (x ^ x2 ^ x4 ^ x8) & 1;
}

fn gf9Add(x: u8, y: u8) u8 {
    return 3 * (((x / 3) + (y / 3)) % 3) + (((x % 3) + (y % 3)) % 3);
}

fn gf9Mul(x: u8, y: u8) u8 {
    const a1 = x / 3;
    const b1 = x % 3;
    const a2 = y / 3;
    const b2 = y % 3;
    const re = (a1 * a2 + 2 * b1 * b2) % 3;
    const im = (a1 * b2 + b1 * a2) % 3;
    return 3 * re + im;
}

fn gf9Trace(x: u8) u8 {
    return (2 * (x / 3)) % 3;
}

fn verifyPrimeMegyesi(comptime p: usize) usize {
    @setEvalBranchQuota(200000);
    // Find primitive root g
    var g: usize = 2;
    while (g < p) : (g += 1) {
        var seen: [p]bool = @splat(false);
        var cur: usize = 1;
        var cnt: usize = 0;
        for (0..(p - 1)) |_| {
            if (!seen[cur]) {
                seen[cur] = true;
                cnt += 1;
            }
            cur = (cur * g) % p;
        }
        if (cnt == p - 1) break;
    }
    var is_qr: [p]bool = @splat(false);
    var cur: usize = 1;
    for (0..((p - 1) / 2)) |_| {
        is_qr[cur] = true;
        cur = (cur * g * g) % p;
    }
    var f: [p]usize = undefined;
    f[0] = 0;
    for (1..p) |x| {
        f[x] = if (is_qr[x]) x else (g * x) % p;
    }
    // Find first undetermined slope m0
    var m0: usize = 0;
    var found_m0 = false;
    for (0..p) |m| {
        var seen: [p]bool = @splat(false);
        var ok = true;
        for (0..p) |x| {
            const y = (f[x] + p - (m * x) % p) % p;
            if (seen[y]) {
                ok = false;
                break;
            }
            seen[y] = true;
        }
        if (ok) {
            m0 = m;
            found_m0 = true;
            break;
        }
    }
    if (!found_m0) @panic("m0 not found");
    var mu: [p]usize = undefined;
    for (0..p) |x| {
        mu[x] = (f[x] + p - (m0 * x) % p) % p;
    }
    // Count nonzero undetermined directions c
    var t: usize = 0;
    for (1..p) |c| {
        var seen: [p]bool = @splat(false);
        var ok = true;
        for (0..p) |x| {
            const y = (mu[x] + c * x) % p;
            if (seen[y]) {
                ok = false;
                break;
            }
            seen[y] = true;
        }
        if (ok) t += 1;
    }
    // Verify maximal cardinality: for all (a,b)!=(0,0), a*mu(z) + b*z not constant
    for (0..p) |a| {
        for (0..p) |b| {
            if (a == 0 and b == 0) continue;
            var nonconst = false;
            for (1..p) |z| {
                if ((a * mu[z] + b * z) % p != 0) {
                    nonconst = true;
                    break;
                }
            }
            if (!nonconst) @panic("Not maximal cardinality");
        }
    }
    return t;
}

fn verifyF9Comptime() usize {
    @setEvalBranchQuota(100000);
    var mu: [9]u8 = undefined;
    for (0..9) |x| {
        const xb: u8 = @intCast(x);
        mu[x] = if (xb == 0) 0 else if (xb == 1 or xb == 2 or xb == 3 or xb == 6) xb else gf9Mul(6, xb);
    }
    var t: usize = 0;
    for (1..9) |c| {
        var seen: [9]bool = @splat(false);
        var ok = true;
        for (0..9) |x| {
            const y = gf9Add(mu[x], gf9Mul(@intCast(c), @intCast(x)));
            if (seen[y]) {
                ok = false;
                break;
            }
            seen[y] = true;
        }
        if (ok) t += 1;
    }
    for (0..9) |a| {
        for (0..9) |b| {
            if (a == 0 and b == 0) continue;
            var nonconst = false;
            for (1..9) |z| {
                if (gf9Trace(gf9Add(gf9Mul(@intCast(a), mu[z]), gf9Mul(@intCast(b), @intCast(z)))) != 0) {
                    nonconst = true;
                    break;
                }
            }
            if (!nonconst) @panic("F9 not maximal cardinality");
        }
    }
    return t;
}

fn verifyF16Comptime() usize {
    @setEvalBranchQuota(200000);
    var mu: [16]u8 = undefined;
    for (0..16) |x| {
        const xb: u8 = @intCast(x);
        mu[x] = if (xb == 4 or xb == 5 or xb == 6 or xb == 9 or xb == 14) gf16Mul(8, xb) else xb;
    }
    var t: usize = 0;
    for (1..16) |c| {
        var seen: [16]bool = @splat(false);
        var ok = true;
        for (0..16) |x| {
            const y = mu[x] ^ gf16Mul(@intCast(c), @intCast(x));
            if (seen[y]) {
                ok = false;
                break;
            }
            seen[y] = true;
        }
        if (ok) t += 1;
    }
    for (0..16) |a| {
        for (0..16) |b| {
            if (a == 0 and b == 0) continue;
            var nonconst = false;
            for (1..16) |z| {
                if (gf16Trace(gf16Mul(@intCast(a), mu[z]) ^ gf16Mul(@intCast(b), @intCast(z))) != 0) {
                    nonconst = true;
                    break;
                }
            }
            if (!nonconst) @panic("F16 not maximal cardinality");
        }
    }
    return t;
}

// COMPILE-TIME PROOF BLOCK: Zig compiler refuses to emit binary unless ALL 7 assertions hold!
comptime {
    if (verifyPrimeMegyesi(7) != 1) @compileError("F_7 Megyesi t != 1");
    if (verifyF9Comptime() != 2) @compileError("F_9 Megyesi t != 2");
    if (verifyPrimeMegyesi(11) != 3) @compileError("F_11 Megyesi t != 3");
    if (verifyPrimeMegyesi(13) != 4) @compileError("F_13 Megyesi t != 4");
    if (verifyF16Comptime() != 3) @compileError("F_16 Megyesi t != 3");
    if (verifyPrimeMegyesi(17) != 6) @compileError("F_17 Megyesi t != 6");
    if (verifyPrimeMegyesi(19) != 7) @compileError("F_19 Megyesi t != 7");
}

fn nextPermutation(a: []u8) bool {
    if (a.len < 2) return false;
    var i: usize = a.len - 2;
    while (true) {
        if (a[i] < a[i + 1]) break;
        if (i == 0) return false;
        i -= 1;
    }
    var j: usize = a.len - 1;
    while (a[j] <= a[i]) : (j -= 1) {}
    const tmp = a[i];
    a[i] = a[j];
    a[j] = tmp;
    var l = i + 1;
    var r = a.len - 1;
    while (l < r) {
        const t = a[l];
        a[l] = a[r];
        a[r] = t;
        l += 1;
        r -= 1;
    }
    return true;
}

const F8Audit = struct {
    total_perms: usize,
    linear_count: usize,
    nonlinear_count: usize,
    orthomorphism_count: usize,
    nonlinear_t_ge1: usize,
};

fn auditF8Exhaustive() F8Audit {
    var perm = [_]u8{ 1, 2, 3, 4, 5, 6, 7 };
    var res = F8Audit{
        .total_perms = 0,
        .linear_count = 0,
        .nonlinear_count = 0,
        .orthomorphism_count = 0,
        .nonlinear_t_ge1 = 0,
    };
    while (true) {
        res.total_perms += 1;
        const mu = [_]u8{ 0, perm[0], perm[1], perm[2], perm[3], perm[4], perm[5], perm[6] };
        const is_lin = (mu[3] == (mu[1] ^ mu[2])) and
            (mu[5] == (mu[1] ^ mu[4])) and
            (mu[6] == (mu[2] ^ mu[4])) and
            (mu[7] == (mu[3] ^ mu[4]));
        if (is_lin) res.linear_count += 1 else res.nonlinear_count += 1;

        var good_c: usize = 0;
        var is_ortho = false;
        for (1..8) |c| {
            var seen: u8 = 0;
            for (0..8) |x| {
                const y = mu[x] ^ gf8Mul(@intCast(c), @intCast(x));
                seen |= (@as(u8, 1) << @intCast(y));
            }
            if (seen == 0xFF) {
                good_c += 1;
                if (c == 1) is_ortho = true;
            }
        }
        if (is_ortho) res.orthomorphism_count += 1;
        if (!is_lin and good_c > 0) res.nonlinear_t_ge1 += 1;

        if (!nextPermutation(&perm)) break;
    }
    return res;
}

fn auditF7Exhaustive() usize {
    var perm = [_]u8{ 1, 2, 3, 4, 5, 6 };
    var nonlin_mc: usize = 0;
    while (true) {
        const mu = [_]u8{ 0, perm[0], perm[1], perm[2], perm[3], perm[4], perm[5] };
        var is_lin = true;
        for (1..7) |x| {
            if (mu[x] != (mu[1] * @as(u8, @intCast(x))) % 7) {
                is_lin = false;
                break;
            }
        }
        if (!is_lin) {
            var good_c: usize = 0;
            for (1..7) |c| {
                var seen: u8 = 0;
                for (0..7) |x| {
                    const y = (mu[x] + @as(u8, @intCast(c * x))) % 7;
                    seen |= (@as(u8, 1) << @intCast(y));
                }
                if (seen == 0x7F) good_c += 1;
            }
            if (good_c >= 1) nonlin_mc += 1;
        }
        if (!nextPermutation(&perm)) break;
    }
    return nonlin_mc;
}

pub fn main() !void {
    const f8 = auditF8Exhaustive();
    const f7_mc = auditF7Exhaustive();
    const ok = (f8.total_perms == 5040) and
        (f8.linear_count == 168) and
        (f8.nonlinear_count == 4872) and
        (f8.orthomorphism_count == 48) and
        (f8.nonlinear_t_ge1 == 0) and
        (f7_mc == 84);

    std.debug.print(
        "[Zig 0.17 comptime+runtime] comptime_verified=(F7:t=1,F9:t=2,F11:t=3,F13:t=4,F16:t=3,F17:t=6,F19:t=7) F8=(total={d},lin={d},nonlin={d},ortho={d},nonlin_t>=1={d}) F7_nonlin_mc={d} all_ok={}\n",
        .{ f8.total_perms, f8.linear_count, f8.nonlinear_count, f8.orthomorphism_count, f8.nonlinear_t_ge1, f7_mc, ok },
    );
    if (!ok) std.process.exit(1);
}

test "comptime Megyesi t-RQLS and exhaustive F8/F7 obstruction" {
    try std.testing.expectEqual(@as(usize, 1), comptime verifyPrimeMegyesi(7));
    try std.testing.expectEqual(@as(usize, 2), comptime verifyF9Comptime());
    try std.testing.expectEqual(@as(usize, 3), comptime verifyPrimeMegyesi(11));
    try std.testing.expectEqual(@as(usize, 4), comptime verifyPrimeMegyesi(13));
    try std.testing.expectEqual(@as(usize, 3), comptime verifyF16Comptime());
    try std.testing.expectEqual(@as(usize, 6), comptime verifyPrimeMegyesi(17));
    try std.testing.expectEqual(@as(usize, 7), comptime verifyPrimeMegyesi(19));

    const f8 = auditF8Exhaustive();
    try std.testing.expectEqual(@as(usize, 5040), f8.total_perms);
    try std.testing.expectEqual(@as(usize, 168), f8.linear_count);
    try std.testing.expectEqual(@as(usize, 4872), f8.nonlinear_count);
    try std.testing.expectEqual(@as(usize, 48), f8.orthomorphism_count);
    try std.testing.expectEqual(@as(usize, 0), f8.nonlinear_t_ge1);

    try std.testing.expectEqual(@as(usize, 84), auditF7Exhaustive());
}
