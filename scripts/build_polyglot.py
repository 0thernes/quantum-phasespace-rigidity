# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Cross-platform build & verification orchestrator for all native/polyglot engines."""
from __future__ import annotations

import pathlib
import platform
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
IS_WIN = platform.system() == "Windows"
EXE = ".exe" if IS_WIN else ""


def run(cmd: list[str], cwd: pathlib.Path) -> str:
    print(f">>> [{cwd.name}] {' '.join(cmd)}", flush=True)
    res = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True)
    if res.stdout:
        print(res.stdout.strip(), flush=True)
    if res.stderr:
        print(res.stderr.strip(), file=sys.stderr, flush=True)
    if res.returncode != 0:
        raise RuntimeError(f"Command failed ({res.returncode}): {' '.join(cmd)}")
    return res.stdout


def main() -> int:
    # 1. C++20 Exact Cyclotomic Ring Z[zeta_p] Engine
    cpp_dir = REPO / "cpp"
    (cpp_dir / "build").mkdir(exist_ok=True)
    cpp_bin = cpp_dir / "build" / f"qpr_cpp{EXE}"
    run(["g++", "-std=c++20", "-O2", "-Wall", "-Wextra", "-Werror", "-pedantic",
         "-o", str(cpp_bin), "src/qpr_cyclotomic.cpp"], cpp_dir)
    run([str(cpp_bin), "--verify-all"], cpp_dir)

    # 2. ISO C11 + x86-64 NASM Assembly + Vendored MIT Moonlab + QGTL + 100k Fuzzer
    c_dir = REPO / "c"
    (c_dir / "build").mkdir(exist_ok=True)
    asm_obj = c_dir / "build" / "pauli_popcnt.o"
    nasm_flags = ["-f", "win64", "-DWIN64"] if IS_WIN else ["-f", "elf64"]
    run(["nasm", *nasm_flags, "-o", str(asm_obj), "../asm/pauli_popcnt.asm"], c_dir)
    moon_srcs = [
        ("sha3.o", "third_party/moonlab/crypto/sha3/sha3.c"),
        ("aes.o", "third_party/moonlab/crypto/aes/aes.c"),
        ("ctr_drbg.o", "third_party/moonlab/crypto/drbg/ctr_drbg.c"),
        ("health_tests.o", "third_party/moonlab/applications/health_tests.c"),
    ]
    moon_objs = []
    for obj_name, src in moon_srcs:
        obj = c_dir / "build" / obj_name
        run(["gcc", "-std=c11", "-D_DEFAULT_SOURCE", "-O2", "-Wall", "-Wextra",
             "-Ithird_party/moonlab", "-Ithird_party/moonlab/applications",
             "-c", "-o", str(obj), src], c_dir)
        moon_objs.append(str(obj))
    c_bin = c_dir / "build" / f"qpr_c{EXE}"
    run(["gcc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-Iinclude",
         "-o", str(c_bin), "src/main.c", "src/qpr_core.c", "src/qgtl_metric.c", "src/qrng_fw.c",
         *moon_objs, str(asm_obj), "-lm"], c_dir)
    fuzz_bin = c_dir / "build" / f"fuzz_qpr{EXE}"
    run(["gcc", "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-Iinclude",
         "-o", str(fuzz_bin), "tests/fuzz_qpr.c", str(asm_obj)], c_dir)
    run([str(c_bin), "--verify-all"], c_dir)
    run([str(fuzz_bin), "100000"], c_dir)

    # 3. Zig 0.17.0 comptime + exhaustive F_8/F_7 engine
    zig_dir = REPO / "zig"
    (zig_dir / "zig-out").mkdir(exist_ok=True)
    run(["zig", "test", "src/main.zig"], zig_dir)
    zig_bin = zig_dir / "zig-out" / f"qpr_zig{EXE}"
    run(["zig", "build-exe", "-OReleaseSafe", "src/main.zig", f"-femit-bin={zig_bin}"], zig_dir)
    run([str(zig_bin), "--verify-all"], zig_dir)

    # 4. Rust 1.94.1 (#![forbid(unsafe_code)], zero deps)
    rust_dir = REPO / "rust"
    run(["cargo", "clippy", "--all-targets", "--", "-D", "warnings"], rust_dir)
    run(["cargo", "test", "--release"], rust_dir)
    run(["cargo", "run", "--release", "--", "--verify-all"], rust_dir)

    # 5. Eshkol Forward-Mode Dual-Number AD
    run([sys.executable, str(REPO / "eshkol" / "run_eshkol_ad.py"), "--verify-all"], REPO)

    print("\n=== ALL 5 POLYGLOT NATIVE & AD ENGINES PASSED 100%! ===", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
