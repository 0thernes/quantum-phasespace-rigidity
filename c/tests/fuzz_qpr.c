/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2026 Alexander Stephen Donahue */
/*
 * Deterministic 100k+ iteration fuzzer for NASM x86-64 Assembly vs. reference C11
 * commuting-weight homomorphism (T1d): wt(u ^ v) + wt(u) + wt(v) == symp(u, v) (mod 2)
 */
#include "qpr_c.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

/* Optional libFuzzer entry point (-DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION -fsanitize=fuzzer) */
#ifdef FUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 32) return 0;
    uint64_t v[4];
    for (int i = 0; i < 4; ++i) {
        uint64_t acc = 0;
        for (int b = 0; b < 8; ++b) acc |= ((uint64_t)data[i * 8 + b]) << (8 * b);
        v[i] = acc;
    }
    uint32_t s = qpr_asm_symp_f2(v[0], v[1], v[2], v[3]);
    uint32_t w1 = qpr_asm_pauli_weight(v[0], v[1]);
    uint32_t w2 = qpr_asm_pauli_weight(v[2], v[3]);
    uint32_t w12 = qpr_asm_pauli_weight(v[0] ^ v[2], v[1] ^ v[3]);
    if (((w12 + w1 + w2) & 1U) != s) __builtin_trap();
    if (qpr_asm_symp_f2(v[2], v[3], v[0], v[1]) != s) __builtin_trap();
    return 0;
}
#else

int main(int argc, char **argv) {
    uint64_t iters = 100000ULL;
    if (argc > 1) {
        long long v = atoll(argv[1]);
        if (v > 0) iters = (uint64_t)v;
    }
    uint64_t rng = 0x0743935020260020ULL;
    for (uint64_t t = 0; t < iters; ++t) {
        uint64_t x1 = splitmix64(&rng);
        uint64_t z1 = splitmix64(&rng);
        uint64_t x2 = splitmix64(&rng);
        uint64_t z2 = splitmix64(&rng);
        uint32_t s = qpr_asm_symp_f2(x1, z1, x2, z2);
        uint32_t w1 = qpr_asm_pauli_weight(x1, z1);
        uint32_t w2 = qpr_asm_pauli_weight(x2, z2);
        uint32_t w12 = qpr_asm_pauli_weight(x1 ^ x2, z1 ^ z2);
        if (((w12 + w1 + w2) & 1U) != s) {
            fprintf(stderr, "FUZZ FAIL at iter %llu\n", (unsigned long long)t);
            return 1;
        }
        /* Check symmetry of symplectic form */
        if (qpr_asm_symp_f2(x2, z2, x1, z1) != s) {
            fprintf(stderr, "SYMP SYM FAIL at iter %llu\n", (unsigned long long)t);
            return 1;
        }
    }
    printf("[FUZZ C11+NASM] Passed %llu random 64-qubit symplectic homomorphism checks!\n",
           (unsigned long long)iters);
    return 0;
}
#endif
