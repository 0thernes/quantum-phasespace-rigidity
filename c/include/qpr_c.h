/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2026 Alexander Stephen Donahue */
#ifndef QPR_C_H
#define QPR_C_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Bare-metal x86-64 NASM Assembly exports (or portable C11 fallback if QPR_NO_ASM) */
uint32_t qpr_asm_symp_f2(uint64_t x1, uint64_t z1, uint64_t x2, uint64_t z2);
uint32_t qpr_asm_pauli_weight(uint64_t x, uint64_t z);
void qpr_asm_graph_weight_enum(uint32_t n, const uint64_t *adj, uint64_t *counts);

/* Pillar I exact integer verification */
int qpr_verify_unimodular_minors_prism6(void);
int qpr_verify_unimodular_minors_wheel5(void);
int qpr_scan_all_n4_f2_graphs(uint32_t *out_ame_count);
int qpr_scan_all_n5_f2_graphs(uint32_t *out_ame_count);

/* QGTL Quantum Geometric Tensor (Fubini-Study metric g_{mu,nu} & Berry curvature Omega_{mu,nu}) */
typedef struct {
    double g_tt;
    double g_pp;
    double g_tp;
    double omega_tp;
    double max_analytic_err;
} qgtl_tensor_2d_t;

int qpr_qgtl_verify_entangled_astab_manifold(qgtl_tensor_2d_t *out);
int qpr_qgtl_verify_rqls11_phase_manifold(qgtl_tensor_2d_t *out);

/* Moonlab FIPS 202 SHA3-256 + NIST SP 800-90A CTR_DRBG + SP 800-90B QRNG Health-Tested Sampler */
typedef struct {
    int health_startup_ok;
    int health_continuous_ok;
    int stuck_fault_detected;
    uint32_t samples_audited;
    double max_lambda2_tr_sq_sampled;
    uint8_t digest_sha3_256[32];
} qrng_audit_report_t;

int qpr_moonlab_qrng_audit(qrng_audit_report_t *out);

#ifdef __cplusplus
}
#endif

#endif /* QPR_C_H */
