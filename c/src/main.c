/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2026 Alexander Stephen Donahue */
#include "qpr_c.h"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

int main(int argc, char **argv) {
    int json_mode = (argc > 1 && strcmp(argv[1], "--json") == 0);

    /* 1. NASM x86-64 / C11 symplectic & weight-enumerator tests */
    uint64_t adj_c5[5] = {0x12ULL, 0x05ULL, 0x0AULL, 0x14ULL, 0x09ULL};
    uint64_t w_c5[6] = {0};
    qpr_asm_graph_weight_enum(5U, adj_c5, w_c5);
    int c5_ok = (w_c5[0] == 1 && w_c5[1] == 0 && w_c5[2] == 0 && w_c5[3] == 10 && w_c5[4] == 15 && w_c5[5] == 6);

    uint64_t adj_prism[6] = {0x0EULL, 0x15ULL, 0x23ULL, 0x31ULL, 0x2AULL, 0x1CULL};
    uint64_t w_prism[7] = {0};
    qpr_asm_graph_weight_enum(6U, adj_prism, w_prism);
    int prism_ok = (w_prism[0] == 1 && w_prism[1] == 0 && w_prism[2] == 0 && w_prism[3] == 0 &&
                    w_prism[4] == 45 && w_prism[5] == 0 && w_prism[6] == 18);

    int minors_prism = qpr_verify_unimodular_minors_prism6();
    int minors_w5 = qpr_verify_unimodular_minors_wheel5();

    uint32_t ame4_cnt = 999, ame5_cnt = 0;
    int scan4_ok = qpr_scan_all_n4_f2_graphs(&ame4_cnt);
    int scan5_ok = qpr_scan_all_n5_f2_graphs(&ame5_cnt);

    /* 2. QGTL Fubini-Study metric & Berry curvature verification */
    qgtl_tensor_2d_t qgt_ent = {0, 0, 0, 0, 0};
    qgtl_tensor_2d_t qgt_rqls = {0, 0, 0, 0, 0};
    int qgt1_ok = qpr_qgtl_verify_entangled_astab_manifold(&qgt_ent);
    int qgt2_ok = qpr_qgtl_verify_rqls11_phase_manifold(&qgt_rqls);

    /* 3. Moonlab SHA3-256 + CTR_DRBG + SP 800-90B QRNG Health-Tested Lambda_2 audit */
    qrng_audit_report_t qrng;
    memset(&qrng, 0, sizeof(qrng));
    int qrng_ok = qpr_moonlab_qrng_audit(&qrng);

    int all_ok = c5_ok && prism_ok && minors_prism && minors_w5 &&
                 scan4_ok && scan5_ok && qgt1_ok && qgt2_ok && qrng_ok;

    if (json_mode) {
        printf("{\n");
        printf("  \"engine\": \"c11-nasm-moonlab-qgtl\",\n");
        printf("  \"c5_weights\": [%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "],\n",
               w_c5[0], w_c5[1], w_c5[2], w_c5[3], w_c5[4], w_c5[5]);
        printf("  \"prism6_weights\": [%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "],\n",
               w_prism[0], w_prism[1], w_prism[2], w_prism[3], w_prism[4], w_prism[5], w_prism[6]);
        printf("  \"prism6_unimodular\": %s,\n", minors_prism ? "true" : "false");
        printf("  \"wheel5_unimodular\": %s,\n", minors_w5 ? "true" : "false");
        printf("  \"n4_f2_ame_count\": %u,\n", ame4_cnt);
        printf("  \"n5_f2_ame_count\": %u,\n", ame5_cnt);
        printf("  \"qgtl_entangled_astab\": {\"g_tt\": %.12f, \"g_pp\": %.12f, \"omega_tp\": %.12f, \"err\": %.3e},\n",
               qgt_ent.g_tt, qgt_ent.g_pp, qgt_ent.omega_tp, qgt_ent.max_analytic_err);
        printf("  \"qgtl_rqls11\": {\"g_aa\": %.12f, \"g_bb\": %.12f, \"g_ab\": %.12f, \"omega_ab\": %.12f, \"err\": %.3e},\n",
               qgt_rqls.g_tt, qgt_rqls.g_pp, qgt_rqls.g_tp, qgt_rqls.omega_tp, qgt_rqls.max_analytic_err);
        printf("  \"moonlab_qrng\": {\"startup_ok\": %s, \"continuous_ok\": %s, \"stuck_detected\": %s, \"samples\": %u, \"max_lambda2_tr_sq\": %.9f, \"sha3_256\": \"",
               qrng.health_startup_ok ? "true" : "false",
               qrng.health_continuous_ok ? "true" : "false",
               qrng.stuck_fault_detected ? "true" : "false",
               qrng.samples_audited, qrng.max_lambda2_tr_sq_sampled);
        for (int i = 0; i < 32; ++i) printf("%02x", qrng.digest_sha3_256[i]);
        printf("\"},\n");
        printf("  \"all_ok\": %s\n", all_ok ? "true" : "false");
        printf("}\n");
    } else {
        printf("[C11+NASM] C5 A=[%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "] ok=%d\n",
               w_c5[0], w_c5[1], w_c5[2], w_c5[3], w_c5[4], w_c5[5], c5_ok);
        printf("[C11+NASM] Prism6 A=[%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64 "] ok=%d unimod=%d W5_unimod=%d\n",
               w_prism[0], w_prism[1], w_prism[2], w_prism[3], w_prism[4], w_prism[5], w_prism[6],
               prism_ok, minors_prism, minors_w5);
        printf("[C11+NASM] Exhaustive F_2 graphs: N=4 AME=%u (ok=%d), N=5 AME=%u (ok=%d)\n",
               ame4_cnt, scan4_ok, ame5_cnt, scan5_ok);
        printf("[QGTL] Entangled-ASTAB: g_tt=%.9f g_pp=%.9f omega_tp=%.9f err=%.2e (ok=%d)\n",
               qgt_ent.g_tt, qgt_ent.g_pp, qgt_ent.omega_tp, qgt_ent.max_analytic_err, qgt1_ok);
        printf("[QGTL] 3-RQLS(11) Torus: g_aa=%.9f g_bb=%.9f g_ab=%.9f omega_ab=%.2e err=%.2e (ok=%d)\n",
               qgt_rqls.g_tt, qgt_rqls.g_pp, qgt_rqls.g_tp, qgt_rqls.omega_tp, qgt_rqls.max_analytic_err, qgt2_ok);
        printf("[Moonlab+QRNG] SP800-90B startup=%d cont=%d stuck_catch=%d samples=%u max_Lambda2_TrX2=%.9f (ok=%d)\n",
               qrng.health_startup_ok, qrng.health_continuous_ok, qrng.stuck_fault_detected,
               qrng.samples_audited, qrng.max_lambda2_tr_sq_sampled, qrng_ok);
    }
    return all_ok ? 0 : 1;
}
