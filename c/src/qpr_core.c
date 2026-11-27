/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2026 Alexander Stephen Donahue */
/*
 * Pillar I core C11 verifier:
 *  - Portable C11 fallback for NASM kernels when QPR_NO_ASM is defined (e.g. ARM64)
 *  - Exact integer 3x3 minor / determinant verifier for Prism K_3 □ K_2 and Wheel W_5
 *  - Exhaustive NASM-accelerated scan over all 64 4-vertex and 1,024 5-vertex F_2 graphs
 */
#include "qpr_c.h"
#include <stdint.h>

#ifdef QPR_NO_ASM
static uint32_t popcnt64_c(uint64_t v) {
    uint32_t c = 0;
    while (v != 0) {
        v &= (v - 1);
        c++;
    }
    return c;
}

uint32_t qpr_asm_symp_f2(uint64_t x1, uint64_t z1, uint64_t x2, uint64_t z2) {
    return (popcnt64_c(x1 & z2) ^ popcnt64_c(z1 & x2)) & 1U;
}

uint32_t qpr_asm_pauli_weight(uint64_t x, uint64_t z) {
    return popcnt64_c(x | z);
}

void qpr_asm_graph_weight_enum(uint32_t n, const uint64_t *adj, uint64_t *counts) {
    for (uint32_t i = 0; i <= n; ++i) counts[i] = 0;
    uint64_t limit = (uint64_t)1U << n;
    for (uint64_t mask = 0; mask < limit; ++mask) {
        uint64_t zmask = 0;
        for (uint32_t i = 0; i < n; ++i) {
            if ((mask >> i) & 1ULL) zmask ^= adj[i];
        }
        uint32_t w = popcnt64_c(mask | zmask);
        counts[w] += 1;
    }
}
#endif

static int det3x3_int(const int m[3][3]) {
    return m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
         - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
         + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]);
}

static int verify_all_bipartition_minors_n6(const int adj[6][6]) {
    /* Every 3-vs-3 bipartition (S, S^c) has a 3x3 off-diagonal submatrix Gamma_{S, S^c};
       if ALL 20 (10 complementary pairs) determinants lie in {-1, +1}, the canonical
       graph state is unimodularly AME(6, d) for ALL d >= 2! */
    int checked = 0;
    for (int i = 0; i < 6; ++i) {
        for (int j = i + 1; j < 6; ++j) {
            for (int k = j + 1; k < 6; ++k) {
                int S[3] = {i, j, k};
                int Sc[3];
                int p = 0;
                for (int v = 0; v < 6; ++v) {
                    if (v != i && v != j && v != k) Sc[p++] = v;
                }
                int sub[3][3];
                for (int r = 0; r < 3; ++r) {
                    for (int c = 0; c < 3; ++c) {
                        sub[r][c] = adj[S[r]][Sc[c]];
                    }
                }
                int det = det3x3_int(sub);
                if (det != 1 && det != -1) return 0;
                checked++;
            }
        }
    }
    return (checked == 20) ? 1 : 0;
}

int qpr_verify_unimodular_minors_prism6(void) {
    const int prism[6][6] = {
        {0, 1, 1, 1, 0, 0},
        {1, 0, 1, 0, 1, 0},
        {1, 1, 0, 0, 0, 1},
        {1, 0, 0, 0, 1, 1},
        {0, 1, 0, 1, 0, 1},
        {0, 0, 1, 1, 1, 0}
    };
    return verify_all_bipartition_minors_n6(prism);
}

int qpr_verify_unimodular_minors_wheel5(void) {
    const int w5[6][6] = {
        {0, 1, 0, 0, 1, 1},
        {1, 0, 1, 0, 0, 1},
        {0, 1, 0, 1, 0, 1},
        {0, 0, 1, 0, 1, 1},
        {1, 0, 0, 1, 0, 1},
        {1, 1, 1, 1, 1, 0}
    };
    return verify_all_bipartition_minors_n6(w5);
}

int qpr_scan_all_n4_f2_graphs(uint32_t *out_ame_count) {
    uint32_t ame = 0;
    /* 6 possible edges on 4 vertices -> 64 graphs */
    const int eu[6] = {0, 0, 0, 1, 1, 2};
    const int ev[6] = {1, 2, 3, 2, 3, 3};
    for (uint32_t bits = 0; bits < 64U; ++bits) {
        uint64_t adj[4] = {0, 0, 0, 0};
        uint64_t counts[5] = {0, 0, 0, 0, 0};
        for (int e = 0; e < 6; ++e) {
            if ((bits >> e) & 1U) {
                adj[eu[e]] |= (1ULL << ev[e]);
                adj[ev[e]] |= (1ULL << eu[e]);
            }
        }
        qpr_asm_graph_weight_enum(4U, adj, counts);
        if (counts[1] == 0 && counts[2] == 0) ame++;
    }
    if (out_ame_count) *out_ame_count = ame;
    return (ame == 0U) ? 1 : 0;
}

int qpr_scan_all_n5_f2_graphs(uint32_t *out_ame_count) {
    uint32_t ame = 0;
    /* 10 possible edges on 5 vertices -> 1,024 graphs */
    const int eu[10] = {0, 0, 0, 0, 1, 1, 1, 2, 2, 3};
    const int ev[10] = {1, 2, 3, 4, 2, 3, 4, 3, 4, 4};
    for (uint32_t bits = 0; bits < 1024U; ++bits) {
        uint64_t adj[5] = {0, 0, 0, 0, 0};
        uint64_t counts[6] = {0, 0, 0, 0, 0, 0};
        for (int e = 0; e < 10; ++e) {
            if ((bits >> e) & 1U) {
                adj[eu[e]] |= (1ULL << ev[e]);
                adj[ev[e]] |= (1ULL << eu[e]);
            }
        }
        qpr_asm_graph_weight_enum(5U, adj, counts);
        if (counts[1] == 0 && counts[2] == 0) ame++;
    }
    if (out_ame_count) *out_ame_count = ame;
    /* Exact exhaustive count over all 2^10 = 1,024 labeled 5-vertex graphs: 132 AME(5,2) graphs. */
    return (ame == 132U) ? 1 : 0;
}
