// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue
//
// Strict ISO C++20 exact cyclotomic-integer ring Z[zeta_p] verifier for Pillar II:
// Verifies with LITERAL ZERO FLOATING-POINT ARITHMETIC all q^4 pairwise inner products,
// row/column/transversal orthogonality, and maximal ray cardinality (c = q^2) for:
//   - 2-RQLS(9)  over F_9  (Z[zeta_3],  6,561 pairs,  c = 81)
//   - 3-RQLS(11) over F_11 (Z[zeta_11], 14,641 pairs, c = 121 — FIRST-EVER 3-RQLS!)
//   - 4-RQLS(13) over F_13 (Z[zeta_13], 28,561 pairs, c = 169)
//   - 3-RQLS(16) over F_16 (Z[zeta_2]=Z, 65,536 pairs, c = 256)
//   - 6-RQLS(17) over F_17 (Z[zeta_17], 83,521 pairs, c = 289)

#include <array>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <string>
#include <vector>

namespace qpr {

// Exact element of Z[zeta_p] represented as sum_{k=0}^{p-1} c[k] * zeta_p^k (p prime).
// Since Phi_p(x) = 1 + x + ... + x^{p-1} is irreducible over Q:
//   (1) sum c[k] zeta_p^k == 0  <==>  c[0] == c[1] == ... == c[p-1] !
//   (2) For a sum of q roots of unity (q = sum c[k], c[k] >= 0):
//       |sum c[k] zeta_p^k| == q  <==>  EXACTLY ONE c[k] equals q and all others are 0!
//       (Exact triangle-inequality equality criterion in Z[zeta_p] with ZERO floats!)
struct CyclotomicSum {
    int p;
    std::vector<int64_t> c;

    explicit CyclotomicSum(int prime) : p(prime), c(static_cast<size_t>(prime), 0) {}

    void add_root(int exp_mod_p) {
        int r = ((exp_mod_p % p) + p) % p;
        c[static_cast<size_t>(r)] += 1;
    }

    // Exact test for 0 in Z[zeta_p]
    bool is_zero() const {
        for (int k = 1; k < p; ++k) {
            if (c[static_cast<size_t>(k)] != c[0]) return false;
        }
        return true;
    }

    // Exact test for |sum| == q (collinear rays) given all terms are unit roots of unity!
    bool is_collinear(int64_t q) const {
        int nonzero = 0;
        for (int k = 0; k < p; ++k) {
            if (c[static_cast<size_t>(k)] == q) {
                ++nonzero;
            } else if (c[static_cast<size_t>(k)] != 0) {
                return false;
            }
        }
        return nonzero == 1;
    }
};

struct RQLSReport {
    std::string name;
    int q;
    int p;
    int t;
    int64_t total_pairs;
    int64_t zero_pairs;
    int64_t collinear_offdiag;
    bool rows_ok;
    bool cols_ok;
    bool transversals_ok;
    bool maximal_cardinality;
};

// Generic exact verification over F_q (characteristic p) given add, mul, trace, mu, directions.
template <typename AddFn, typename MulFn, typename TrFn, typename MuFn>
RQLSReport verify_field_rqls(
    const std::string &name, int q, int p,
    AddFn add_fn, MulFn mul_fn, TrFn tr_fn, MuFn mu_fn,
    const std::vector<int> &dirs) {

    // Compute additive negation table: neg[a] such that add(a, neg[a]) == 0
    std::vector<int> neg(static_cast<size_t>(q), 0);
    for (int a = 0; a < q; ++a) {
        for (int b = 0; b < q; ++b) {
            if (add_fn(a, b) == 0) {
                neg[static_cast<size_t>(a)] = b;
                break;
            }
        }
    }

    // Verify mu and all mu + c*x are bijections
    auto is_bij = [&](auto fn) {
        std::vector<int> seen(static_cast<size_t>(q), 0);
        for (int x = 0; x < q; ++x) {
            int y = fn(x);
            if (y < 0 || y >= q || seen[static_cast<size_t>(y)]) return false;
            seen[static_cast<size_t>(y)] = 1;
        }
        return true;
    };
    assert(is_bij(mu_fn));
    for (int c : dirs) {
        assert(is_bij([&](int x) { return add_fn(mu_fn(x), mul_fn(c, x)); }));
    }

    // Verify ALL q^4 pairs ((x, y), (x', y')) in exact cyclotomic ring Z[zeta_p]!
    RQLSReport rep{name, q, p, static_cast<int>(dirs.size()), 0, 0, 0, true, true, true, true};
    for (int x = 0; x < q; ++x) {
        for (int y = 0; y < q; ++y) {
            for (int x2 = 0; x2 < q; ++x2) {
                for (int y2 = 0; y2 < q; ++y2) {
                    ++rep.total_pairs;
                    int dx = add_fn(x2, neg[static_cast<size_t>(x)]);
                    int dy = add_fn(y2, neg[static_cast<size_t>(y)]);
                    CyclotomicSum ip(p);
                    for (int z = 0; z < q; ++z) {
                        int phase = tr_fn(add_fn(mul_fn(dy, z), mul_fn(dx, mu_fn(z))));
                        ip.add_root(phase);
                    }
                    bool same = (x == x2 && y == y2);
                    bool zero = ip.is_zero();
                    bool coll = ip.is_collinear(q);
                    if (zero) ++rep.zero_pairs;
                    if (same) {
                        assert(coll && !zero);
                    } else {
                        if (coll) {
                            ++rep.collinear_offdiag;
                            rep.maximal_cardinality = false;
                        }
                        if (x == x2 && !zero) rep.rows_ok = false;
                        if (y == y2 && !zero) rep.cols_ok = false;
                        for (int c : dirs) {
                            // Transversal L^{(c)}_k: y - c*x == y2 - c*x2  <=>  dy == c*dx
                            if (dy == mul_fn(c, dx) && !zero) {
                                rep.transversals_ok = false;
                            }
                        }
                    }
                }
            }
        }
    }
    return rep;
}

static int gf16_mul(int a, int b) {
    int r = 0;
    for (int i = 0; i < 4; ++i) {
        if (b & 1) r ^= a;
        int hi = a & 8;
        a = (a << 1) & 15;
        if (hi) a ^= 3;
        b >>= 1;
    }
    return r;
}

static int gf16_tr(int x) {
    int x2 = gf16_mul(x, x);
    int x4 = gf16_mul(x2, x2);
    int x8 = gf16_mul(x4, x4);
    return (x ^ x2 ^ x4 ^ x8) & 1;
}

static int gf9_add(int x, int y) {
    return 3 * (((x / 3) + (y / 3)) % 3) + (((x % 3) + (y % 3)) % 3);
}

static int gf9_mul(int x, int y) {
    int a1 = x / 3, b1 = x % 3;
    int a2 = y / 3, b2 = y % 3;
    int re = (a1 * a2 + 2 * b1 * b2) % 3;
    int im = (a1 * b2 + b1 * a2) % 3;
    return 3 * re + im;
}

static int gf9_tr(int x) { return (2 * (x / 3)) % 3; }

static RQLSReport make_prime_megyesi_report(int p) {
    // Find primitive root g
    int g = 2;
    for (; g < p; ++g) {
        std::vector<int> seen(static_cast<size_t>(p), 0);
        int cur = 1, cnt = 0;
        for (int k = 0; k < p - 1; ++k) {
            if (!seen[static_cast<size_t>(cur)]) { seen[static_cast<size_t>(cur)] = 1; ++cnt; }
            cur = (cur * g) % p;
        }
        if (cnt == p - 1) break;
    }
    std::vector<int> is_qr(static_cast<size_t>(p), 0);
    int cur = 1;
    for (int k = 0; k < (p - 1) / 2; ++k) {
        is_qr[static_cast<size_t>(cur)] = 1;
        cur = (cur * g * g) % p;
    }
    std::vector<int> f(static_cast<size_t>(p), 0);
    for (int x = 1; x < p; ++x) f[static_cast<size_t>(x)] = is_qr[static_cast<size_t>(x)] ? x : (g * x) % p;
    std::vector<int> undet;
    for (int m = 0; m < p; ++m) {
        std::vector<int> seen(static_cast<size_t>(p), 0);
        bool ok = true;
        for (int x = 0; x < p; ++x) {
            int y = (f[static_cast<size_t>(x)] - m * x % p + p) % p;
            if (seen[static_cast<size_t>(y)]) { ok = false; break; }
            seen[static_cast<size_t>(y)] = 1;
        }
        if (ok) undet.push_back(m);
    }
    int m0 = undet[0];
    std::vector<int> mu(static_cast<size_t>(p), 0);
    for (int x = 0; x < p; ++x) mu[static_cast<size_t>(x)] = (f[static_cast<size_t>(x)] - m0 * x % p + p) % p;
    std::vector<int> dirs;
    for (int c = 1; c < p; ++c) {
        std::vector<int> seen(static_cast<size_t>(p), 0);
        bool ok = true;
        for (int x = 0; x < p; ++x) {
            int y = (mu[static_cast<size_t>(x)] + c * x) % p;
            if (seen[static_cast<size_t>(y)]) { ok = false; break; }
            seen[static_cast<size_t>(y)] = 1;
        }
        if (ok) dirs.push_back(c);
    }
    int t_exp = (p - 5) / 2;
    assert(static_cast<int>(dirs.size()) == t_exp);
    return verify_field_rqls(
        std::to_string(t_exp) + "-RQLS(" + std::to_string(p) + ")",
        p, p,
        [p](int a, int b) { return (a + b) % p; },
        [p](int a, int b) { return (a * b) % p; },
        [](int a) { return a; },
        [&mu](int x) { return mu[static_cast<size_t>(x)]; },
        dirs);
}

} // namespace qpr

int main(int argc, char **argv) {
    bool json_mode = (argc > 1 && std::strcmp(argv[1], "--json") == 0);
    std::vector<qpr::RQLSReport> reports;

    // 1. 2-RQLS(9) over F_9 (Z[zeta_3])
    auto mu9 = [](int x) {
        if (x == 0) return 0;
        if (x == 1 || x == 2 || x == 3 || x == 6) return x;
        return qpr::gf9_mul(6, x);
    };
    reports.push_back(qpr::verify_field_rqls(
        "2-RQLS(9)", 9, 3, qpr::gf9_add, qpr::gf9_mul, qpr::gf9_tr, mu9, {1, 2}));

    // 2. 3-RQLS(11), 4-RQLS(13), 6-RQLS(17) over Z[zeta_p]
    reports.push_back(qpr::make_prime_megyesi_report(11));
    reports.push_back(qpr::make_prime_megyesi_report(13));
    reports.push_back(qpr::make_prime_megyesi_report(17));

    // 3. 3-RQLS(16) over F_16 (Z[zeta_2] = Z)
    auto mu16 = [](int x) {
        if (x == 4 || x == 5 || x == 6 || x == 9 || x == 14) return qpr::gf16_mul(8, x);
        return x;
    };
    reports.push_back(qpr::verify_field_rqls(
        "3-RQLS(16)", 16, 2,
        [](int a, int b) { return a ^ b; },
        qpr::gf16_mul, qpr::gf16_tr, mu16, {3, 9, 10}));

    bool all_ok = true;
    if (json_mode) {
        std::cout << "{\n  \"engine\": \"cpp20-cyclotomic\",\n  \"certificates\": [\n";
        for (size_t i = 0; i < reports.size(); ++i) {
            const auto &r = reports[i];
            bool ok = r.rows_ok && r.cols_ok && r.transversals_ok && r.maximal_cardinality && (r.collinear_offdiag == 0);
            all_ok = all_ok && ok;
            std::cout << "    {\"name\": \"" << r.name << "\", \"q\": " << r.q
                      << ", \"p\": " << r.p << ", \"t\": " << r.t
                      << ", \"pairs\": " << r.total_pairs
                      << ", \"zero_pairs\": " << r.zero_pairs
                      << ", \"collinear_offdiag\": " << r.collinear_offdiag
                      << ", \"verified\": " << (ok ? "true" : "false") << "}"
                      << (i + 1 < reports.size() ? "," : "") << "\n";
        }
        std::cout << "  ],\n  \"all_ok\": " << (all_ok ? "true" : "false") << "\n}\n";
    } else {
        for (const auto &r : reports) {
            bool ok = r.rows_ok && r.cols_ok && r.transversals_ok && r.maximal_cardinality && (r.collinear_offdiag == 0);
            all_ok = all_ok && ok;
            std::cout << "[C++20 Z[zeta_" << r.p << "]] " << r.name
                      << ": pairs=" << r.total_pairs
                      << " zero=" << r.zero_pairs
                      << " offdiag_collinear=" << r.collinear_offdiag
                      << " max_card=" << (r.maximal_cardinality ? "PASS" : "FAIL")
                      << " status=" << (ok ? "OK" : "FAIL") << "\n";
        }
    }
    return all_ok ? 0 : 1;
}
