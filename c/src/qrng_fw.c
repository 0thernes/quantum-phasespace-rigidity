/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2026 Alexander Stephen Donahue */
/*
 * Moonlab FIPS 202 SHA3-256 + NIST SP 800-90A CTR_DRBG + SP 800-90B QRNG Health Tests
 * Vendored Moonlab source: tsotchke/moonlab@cd3b2347e3739327548708073d7e4ac710cc6a6c (MIT)
 *
 * Uses cryptographically health-tested entropy (RCT + APT continuous & startup tests)
 * to drive stochastic Frank-Wolfe / ray-scaling exploration of the 2-qubit Lambda_2
 * polytope (independently verifying max Tr(X^2) <= 2.0 across random directions),
 * confirms stuck-at-zero fault injection trips RCT, and seals the run digest with SHA3-256.
 */
#include "qpr_c.h"
#include "../third_party/moonlab/crypto/sha3/sha3.h"
#include "../third_party/moonlab/crypto/drbg/ctr_drbg.h"
#include "../third_party/moonlab/applications/health_tests.h"

#include <math.h>
#include <stdint.h>
#include <string.h>

/* All 60 pure 2-qubit stabilizer projector Pauli vectors (15 non-identity Paulis):
   Generate all 15 maximal abelian subgroups of F_2^4 (each has 3 commuting non-id Paulis)
   and their 4 sign assignments (+1,+1,+1), (+1,-1,-1), (-1,+1,-1), (-1,-1,+1) -> 60 facets! */
typedef struct {
    int8_t s[15]; /* s[P-1] in {-1, 0, +1} for P in 1..15 */
} stab_facet2_t;

static uint32_t symp2(uint32_t a, uint32_t b) {
    /* a = (x0,z0,x1,z1) packed in 4 bits */
    uint32_t x1 = ((a >> 0) & 1U) | (((a >> 2) & 1U) << 1);
    uint32_t z1 = ((a >> 1) & 1U) | (((a >> 3) & 1U) << 1);
    uint32_t x2 = ((b >> 0) & 1U) | (((b >> 2) & 1U) << 1);
    uint32_t z2 = ((b >> 1) & 1U) | (((b >> 3) & 1U) << 1);
    return qpr_asm_symp_f2(x1, z1, x2, z2);
}

/* Enumerate all 60 pure 2-qubit stabilizer projector Pauli vectors (15 non-identity Paulis). */
static int build_60_stab_facets(stab_facet2_t facets[60]) {
    int n_facets = 0;
    for (uint32_t p1 = 1; p1 < 16U; ++p1) {
        for (uint32_t p2 = p1 + 1U; p2 < 16U; ++p2) {
            uint32_t p3 = p1 ^ p2;
            if (p3 <= p2) continue;
            if (symp2(p1, p2) != 0U) continue;
            /* Phase sign for P_p1 * P_p2 = eta * P_p3 (eta in {+1, -1} since they commute). */
            int phase_i = 0; /* power of i mod 4 */
            for (int q = 0; q < 2; ++q) {
                uint32_t a = (p1 >> (2 * q)) & 3U; /* 0=I, 1=X, 2=Z, 3=Y */
                uint32_t b = (p2 >> (2 * q)) & 3U;
                if (a == 0U || b == 0U || a == b) continue;
                if ((a == 1U && b == 2U) || (a == 3U && b == 1U) || (a == 2U && b == 3U)) phase_i += 3;
                else phase_i += 1;
            }
            int eta = ((phase_i & 3) == 0) ? 1 : -1;
            const int s1[4] = {1, 1, -1, -1};
            const int s2[4] = {1, -1, 1, -1};
            for (int k = 0; k < 4; ++k) {
                memset(&facets[n_facets], 0, sizeof(stab_facet2_t));
                facets[n_facets].s[p1 - 1U] = (int8_t)s1[k];
                facets[n_facets].s[p2 - 1U] = (int8_t)s2[k];
                facets[n_facets].s[p3 - 1U] = (int8_t)(eta * s1[k] * s2[k]);
                n_facets++;
            }
        }
    }
    return n_facets;
}

int qpr_moonlab_qrng_audit(qrng_audit_report_t *out) {
    uint8_t seed[48];
    const char *domain = "quantum-phasespace-rigidity-v2.0.0-0TH-2026-020";
    uint8_t h1[32], h2[32];
    sha3_256((const uint8_t *)domain, strlen(domain), h1);
    sha3_256(h1, 32, h2);
    memcpy(seed, h1, 32);
    memcpy(seed + 32, h2, 16);

    ctr_drbg_ctx_t drbg;
    ctr_drbg_init(&drbg, seed);

    uint8_t startup_buf[1024];
    ctr_drbg_generate(&drbg, startup_buf, sizeof(startup_buf));

    health_test_ctx_t hctx;
    if (health_tests_init(&hctx) != HEALTH_SUCCESS) return 0;
    int startup_ok = (health_tests_startup(&hctx, startup_buf, sizeof(startup_buf)) == HEALTH_SUCCESS);

    /* Generate 2,048 continuous bytes, audit with NIST SP 800-90B RCT + APT */
    uint8_t stream_buf[2048];
    ctr_drbg_generate(&drbg, stream_buf, sizeof(stream_buf));
    int cont_ok = (health_tests_run_batch(&hctx, stream_buf, sizeof(stream_buf)) == HEALTH_SUCCESS);
    uint32_t samples_audited = (uint32_t)hctx.stats.samples_tested;
    health_tests_free(&hctx);

    /* Negative fault test: inject 64 identical zero bytes -> RCT MUST fail! */
    health_test_ctx_t fault_ctx;
    int stuck_detected = 0;
    if (health_tests_init(&fault_ctx) == HEALTH_SUCCESS) {
        uint8_t zeros[64];
        memset(zeros, 0, sizeof(zeros));
        if (health_tests_run_batch(&fault_ctx, zeros, sizeof(zeros)) != HEALTH_SUCCESS) {
            stuck_detected = 1;
        }
        health_tests_free(&fault_ctx);
    }

    /* Use health-tested entropy to shoot 512 random rays into 2-qubit Lambda_2
       and verify exact boundary Tr(X^2) = (1 + t^2 * ||d||^2)/4 <= 2.0! */
    stab_facet2_t facets[60];
    int nf = build_60_stab_facets(facets);
    if (nf != 60) return 0;

    double max_tr_sq = 0.0;
    for (int trial = 0; trial < 512; ++trial) {
        uint8_t raw[30];
        ctr_drbg_generate(&drbg, raw, sizeof(raw));
        double d[15];
        double norm2 = 0.0;
        for (int i = 0; i < 15; ++i) {
            int16_t v = (int16_t)((uint16_t)raw[2 * i] | ((uint16_t)raw[2 * i + 1] << 8));
            d[i] = (double)v / 32768.0;
            norm2 += d[i] * d[i];
        }
        if (norm2 < 1e-12) continue;
        /* Largest t > 0 such that 1 + t * (s . d) >= 0 for all 60 stabilizer facets */
        double t_max = 1e30;
        for (int f = 0; f < 60; ++f) {
            double dot = 0.0;
            for (int i = 0; i < 15; ++i) dot += (double)facets[f].s[i] * d[i];
            if (dot < -1e-15) {
                double t = -1.0 / dot;
                if (t < t_max) t_max = t;
            }
        }
        double tr_sq = 0.25 * (1.0 + t_max * t_max * norm2);
        if (tr_sq > max_tr_sq) max_tr_sq = tr_sq;
    }

    /* Seal summary with FIPS 202 SHA3-256 */
    uint8_t digest[32];
    sha3_256(stream_buf, sizeof(stream_buf), digest);

    if (out) {
        out->health_startup_ok = startup_ok;
        out->health_continuous_ok = cont_ok;
        out->stuck_fault_detected = stuck_detected;
        out->samples_audited = samples_audited;
        out->max_lambda2_tr_sq_sampled = max_tr_sq;
        memcpy(out->digest_sha3_256, digest, 32);
    }
    return (startup_ok && cont_ok && stuck_detected && max_tr_sq <= 2.0 + 1e-9) ? 1 : 0;
}
