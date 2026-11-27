/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (c) 2026 Alexander Stephen Donahue */
/*
 * Quantum Geometric Tensor (QGTL) C11 Engine
 * Reference formulation: tsotchke/quantum_geometric_tensor@770994aa (MIT)
 *
 * Computes the Quantum Geometric Tensor
 *   Q_{mu,nu} = <d_mu psi | (I - |psi><psi|) | d_nu psi> = g_{mu,nu} - (i/2) Omega_{mu,nu}
 * by BOTH exact closed-form analytical expressions and central-difference numerical
 * verification on two manifolds connecting our solved 2026 problems:
 *   1. Purification manifold of our Pillar III entangled-ASTAB witness rho_ent
 *      with spectrum (11/20, 3/20, 3/20, 3/20) under SU(2) phase-entangling orbits.
 *   2. Continuous phase-deformation manifold of our Pillar II maximal-cardinality
 *      3-RQLS(11) rays |psi_{x,y}(alpha, beta)> over F_11.
 */
#include "qpr_c.h"
#include <math.h>
#include <stdint.h>

#ifndef M_PI
#define M_PI 3.14159265358979323846264338327950288
#endif

typedef struct {
    double re;
    double im;
} cpx_t;

static cpx_t cpx_add(cpx_t a, cpx_t b) { cpx_t r = {a.re + b.re, a.im + b.im}; return r; }
static cpx_t cpx_sub(cpx_t a, cpx_t b) { cpx_t r = {a.re - b.re, a.im - b.im}; return r; }
static cpx_t cpx_mul(cpx_t a, cpx_t b) {
    cpx_t r = {a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re};
    return r;
}
static cpx_t cpx_conj(cpx_t a) { cpx_t r = {a.re, -a.im}; return r; }
static cpx_t cpx_scale(cpx_t a, double s) { cpx_t r = {a.re * s, a.im * s}; return r; }

static cpx_t inner_prod(int dim, const cpx_t *u, const cpx_t *v) {
    cpx_t acc = {0.0, 0.0};
    for (int i = 0; i < dim; ++i) {
        acc = cpx_add(acc, cpx_mul(cpx_conj(u[i]), v[i]));
    }
    return acc;
}

static void eval_qgt_fd(
    int dim, double p1, double p2, double eps,
    void (*state_fn)(double, double, cpx_t *),
    qgtl_tensor_2d_t *out) {

    cpx_t psi[16], p1_p[16], p1_m[16], p2_p[16], p2_m[16], d1[16], d2[16];
    state_fn(p1, p2, psi);
    state_fn(p1 + eps, p2, p1_p);
    state_fn(p1 - eps, p2, p1_m);
    state_fn(p1, p2 + eps, p2_p);
    state_fn(p1, p2 - eps, p2_m);

    double inv2e = 0.5 / eps;
    for (int i = 0; i < dim; ++i) {
        d1[i] = cpx_scale(cpx_sub(p1_p[i], p1_m[i]), inv2e);
        d2[i] = cpx_scale(cpx_sub(p2_p[i], p2_m[i]), inv2e);
    }

    cpx_t a1 = inner_prod(dim, psi, d1);
    cpx_t a2 = inner_prod(dim, psi, d2);
    cpx_t q11 = cpx_sub(inner_prod(dim, d1, d1), cpx_mul(cpx_conj(a1), a1));
    cpx_t q22 = cpx_sub(inner_prod(dim, d2, d2), cpx_mul(cpx_conj(a2), a2));
    cpx_t q12 = cpx_sub(inner_prod(dim, d1, d2), cpx_mul(cpx_conj(a1), a2));

    out->g_tt = q11.re;
    out->g_pp = q22.re;
    out->g_tp = q12.re;
    /* Q_{12} = g_{12} - (i/2) Omega_{12}  =>  Omega_{12} = -2 * Im(Q_{12}) */
    out->omega_tp = -2.0 * q12.im;
}

/*
 * Manifold 1: Entangled-ASTAB Purification Orbit (4-dim Schmidt space of rho_ent)
 *   |Psi(theta, phi)> = sqrt(11/20) [ cos(theta/2)|0> + sin(theta/2) e^{i phi}|1> ]
 *                     + sqrt(3/20) |2> + sqrt(3/20) e^{i phi} |3> + sqrt(3/20) |4> (5-dim)
 * Analytical QGT:
 *   Let p = 11/20, q = 3/20.
 *   d_theta|Psi> = sqrt(p)/2 [ -sin(t/2)|0> + cos(t/2) e^{ip}|1> ]
 *     => <Psi|d_theta Psi> = 0,  g_{tt} = p / 4 = 11/80 = 0.1375.
 *   d_phi|Psi> = i * sqrt(p) sin(t/2) e^{ip}|1> + i * sqrt(q) e^{ip}|3>
 *     => <Psi|d_phi Psi> = i * (p sin^2(t/2) + q)
 *     => <d_phi Psi|d_phi Psi> = p sin^2(t/2) + q
 *     => g_{pp} = (p sin^2(t/2) + q) * (1 - p sin^2(t/2) - q)
 *   <d_theta Psi|d_phi Psi> = i * (p/2) sin(t/2) cos(t/2) = i * (p/4) sin(t)
 *     => g_{tp} = 0,  Omega_{tp} = -2 * (p/4) sin(t) = -(p/2) sin(t)!
 */
static void entangled_astab_state(double theta, double phi, cpx_t *psi) {
    double sp = sqrt(11.0 / 20.0);
    double sq = sqrt(3.0 / 20.0);
    double ct = cos(0.5 * theta);
    double st = sin(0.5 * theta);
    cpx_t ep = {cos(phi), sin(phi)};
    psi[0].re = sp * ct; psi[0].im = 0.0;
    psi[1].re = sp * st * ep.re; psi[1].im = sp * st * ep.im;
    psi[2].re = sq; psi[2].im = 0.0;
    psi[3].re = sq * ep.re; psi[3].im = sq * ep.im;
    psi[4].re = sq; psi[4].im = 0.0;
}

int qpr_qgtl_verify_entangled_astab_manifold(qgtl_tensor_2d_t *out) {
    const double theta = 1.1;
    const double phi = 0.7;
    const double eps = 1e-6;
    qgtl_tensor_2d_t num = {0, 0, 0, 0, 0};
    eval_qgt_fd(5, theta, phi, eps, entangled_astab_state, &num);

    const double p = 11.0 / 20.0;
    const double q = 3.0 / 20.0;
    const double s2 = sin(0.5 * theta) * sin(0.5 * theta);
    const double w = p * s2 + q;
    const double g_tt_exact = p * 0.25;
    const double g_pp_exact = w * (1.0 - w);
    const double g_tp_exact = 0.0;
    const double om_tp_exact = -0.5 * p * sin(theta);

    double err = fabs(num.g_tt - g_tt_exact);
    double e2 = fabs(num.g_pp - g_pp_exact);
    double e3 = fabs(num.g_tp - g_tp_exact);
    double e4 = fabs(num.omega_tp - om_tp_exact);
    if (e2 > err) err = e2;
    if (e3 > err) err = e3;
    if (e4 > err) err = e4;
    num.max_analytic_err = err;
    if (out) *out = num;
    return (err < 1e-9) ? 1 : 0;
}

/*
 * Manifold 2: Continuous Phase Deformation of 3-RQLS(11) Ray |psi_{1,1}(alpha, beta)>
 *   |psi(a, b)> = (1/sqrt(11)) sum_{z=0}^{10} exp(i * (a * z + b * mu11(z))) |z>
 * Since every amplitude has uniform modulus 1/sqrt(11) and purely real phases:
 *   g_{aa} = Var_z(z) = (11^2 - 1)/12 = 10.0
 *   g_{bb} = Var_z(mu11(z)) = 10.0  (because mu11 is a BIJECTION on {0..10}!)
 *   g_{ab} = Cov_z(z, mu11(z))      (exact non-zero metric coupling!)
 *   Omega_{ab} = 0                  (exact zero Berry curvature on flat Hadamard torus!)
 */
static const int MU11_TAB[11] = {0, 7, 5, 10, 6, 2, 4, 1, 9, 8, 3};

static void rqls11_ray_state(double alpha, double beta, cpx_t *psi) {
    const double inv_s11 = 1.0 / sqrt(11.0);
    for (int z = 0; z < 11; ++z) {
        double ph = alpha * (double)z + beta * (double)MU11_TAB[z];
        psi[z].re = inv_s11 * cos(ph);
        psi[z].im = inv_s11 * sin(ph);
    }
}

int qpr_qgtl_verify_rqls11_phase_manifold(qgtl_tensor_2d_t *out) {
    const double alpha = 2.0 * M_PI / 11.0;
    const double beta = 2.0 * M_PI / 11.0;
    const double eps = 1e-6;
    qgtl_tensor_2d_t num = {0, 0, 0, 0, 0};
    eval_qgt_fd(11, alpha, beta, eps, rqls11_ray_state, &num);

    /* Exact analytical moments over uniform z in {0..10} */
    double ez = 5.0;
    double cov_sum = 0.0;
    for (int z = 0; z < 11; ++z) {
        cov_sum += ((double)z - ez) * ((double)MU11_TAB[z] - ez);
    }
    double g_aa_exact = 10.0;
    double g_bb_exact = 10.0;
    double g_ab_exact = cov_sum / 11.0;
    double om_ab_exact = 0.0;

    double err = fabs(num.g_tt - g_aa_exact);
    double e2 = fabs(num.g_pp - g_bb_exact);
    double e3 = fabs(num.g_tp - g_ab_exact);
    double e4 = fabs(num.omega_tp - om_ab_exact);
    if (e2 > err) err = e2;
    if (e3 > err) err = e3;
    if (e4 > err) err = e4;
    num.max_analytic_err = err;
    if (out) *out = num;
    return (err < 1e-7) ? 1 : 0;
}
