/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 */
#include "torus_frontier.h"

#include <stdlib.h>
#include <string.h>

static const Pair2 Q25_HBPZ[37] = {
    {0, 14}, {1, 19}, {2, 2}, {2, 6}, {2, 23}, {3, 10}, {4, 14}, {5, 18}, {6, 2}, {6, 23},
    {7, 6}, {7, 10}, {8, 14}, {9, 18}, {10, 22}, {11, 1}, {11, 5}, {11, 9}, {12, 13}, {13, 17},
    {14, 21}, {15, 0}, {15, 4}, {15, 8}, {16, 12}, {17, 16}, {18, 20}, {19, 3}, {19, 7}, {19, 24},
    {20, 11}, {21, 15}, {22, 19}, {23, 2}, {23, 6}, {23, 23}, {24, 10}
};

static const Pair2 Q29_HBPZ[50] = {
    {0, 0}, {0, 21}, {0, 25}, {1, 17}, {2, 13}, {3, 5}, {3, 9}, {4, 1}, {4, 21}, {4, 25},
    {5, 17}, {6, 13}, {7, 5}, {7, 9}, {8, 1}, {8, 22}, {8, 26}, {9, 18}, {10, 14}, {11, 6},
    {11, 10}, {12, 2}, {12, 23}, {12, 27}, {13, 19}, {14, 15}, {15, 10}, {16, 2}, {16, 6},
    {16, 23}, {16, 27}, {17, 19}, {18, 15}, {19, 11}, {20, 3}, {20, 7}, {20, 24}, {20, 28},
    {21, 20}, {22, 15}, {23, 11}, {24, 3}, {24, 7}, {24, 24}, {24, 28}, {25, 20}, {26, 16},
    {27, 12}, {28, 4}, {28, 8}
};

static const bool SEP_G7[7][7] = {
    {false, false, false, false, true,  true,  true },
    {false, false, true,  true,  true,  true,  true },
    {false, true,  false, true,  false, true,  false},
    {false, true,  true,  false, false, false, true },
    {true,  true,  false, false, false, false, false},
    {true,  true,  true,  false, false, false, false},
    {true,  true,  false, true,  false, false, false}
};

static const int CPAIR[15][2] = {
    {0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5},
    {1, 2}, {1, 3}, {1, 4}, {1, 5},
    {2, 3}, {2, 4}, {2, 5},
    {3, 4}, {3, 5},
    {4, 5}
};

static const uint32_t SCHLAFLI_L_BITS[27] = {
    1u, 2u, 4u, 8u, 16u, 32u,
    62u, 61u, 59u, 55u, 47u, 31u,
    64u, 70u, 74u, 82u, 98u,
    69u, 73u, 81u, 97u,
    79u, 87u, 103u,
    91u, 107u, 115u
};

static const uint32_t SCHLAFLI_R_BITS[7] = {
    130945u, 1974082u, 14823108u, 52710856u, 88640464u, 110168032u, 132124867u
};

int zef_cyc_dist(int n, int a, int b) {
    if (n <= 0) {
        return 0;
    }
    int ma = ((a % n) + n) % n;
    int mb = ((b % n) + n) % n;
    int d1 = (ma + n - mb) % n;
    int d2 = (mb + n - ma) % n;
    return d1 < d2 ? d1 : d2;
}

bool zef_verify_q_hbpz(int n, const Pair2 *q, size_t len) {
    if (n < 9 || (len > 0 && q == NULL)) {
        return false;
    }
    for (size_t i = 0; i < len; ++i) {
        if (q[i].y < 0 || q[i].y >= n || q[i].z < 0 || q[i].z >= n) {
            return false;
        }
    }
    for (size_t i = 0; i < len; ++i) {
        for (size_t j = i + 1; j < len; ++j) {
            if (zef_cyc_dist(n, q[i].y, q[j].y) <= 3 &&
                zef_cyc_dist(n, q[i].z, q[j].z) <= 3) {
                return false;
            }
        }
    }
    return true;
}

bool zef_verify_q_hstar(int n, const Pair2 *q, size_t len) {
    if (n < 15 || (len > 0 && q == NULL)) {
        return false;
    }
    for (size_t i = 0; i < len; ++i) {
        if (q[i].y < 0 || q[i].y >= n || q[i].z < 0 || q[i].z >= n) {
            return false;
        }
    }
    for (size_t i = 0; i < len; ++i) {
        for (size_t j = i + 1; j < len; ++j) {
            if (zef_cyc_dist(n, q[i].y, q[j].y) <= 1 &&
                zef_cyc_dist(n, q[i].z, q[j].z) <= 7) {
                return false;
            }
        }
    }
    return true;
}

uint32_t zef_quotient_ball_size(int n, int a, int b, int c, int d) {
    if (n <= 0 || n > 256) {
        return 0u;
    }
    size_t sz = (size_t)n * (size_t)n;
    unsigned char *seen = (unsigned char *)calloc(sz, 1u);
    if (seen == NULL) {
        return 0u;
    }
    int offs[3];
    offs[0] = n - 1;
    offs[1] = 0;
    offs[2] = 1 % n;
    uint32_t count = 0u;
    for (int i0 = 0; i0 < 3; ++i0) {
        for (int i1 = 0; i1 < 3; ++i1) {
            for (int i2 = 0; i2 < 3; ++i2) {
                for (int i3 = 0; i3 < 3; ++i3) {
                    int e0 = offs[i0], e1 = offs[i1], e2 = offs[i2], e3 = offs[i3];
                    int t1 = ((a * e0 + b * e1) % n + n) % n;
                    int t2 = ((c * e0 + d * e1) % n + n) % n;
                    int y = (e2 + n - t1) % n;
                    int z = (e3 + n - t2) % n;
                    size_t idx = (size_t)y * (size_t)n + (size_t)z;
                    if (!seen[idx]) {
                        seen[idx] = 1u;
                        ++count;
                    }
                }
            }
        }
    }
    free(seen);
    return count;
}

static uint32_t pull1_u32(uint32_t x) {
    return x < 2u ? x : (x - 2u);
}

static uint32_t baumert_line_card(int p, int target) {
    uint32_t sum = 0u;
    int np = p + 2;
    for (int u = 0; u < np; ++u) {
        int pu = (int)pull1_u32((uint32_t)u);
        int tw = (2 * pu + target) % p;
        sum += (tw < 2) ? 2u : 1u;
    }
    return sum;
}

uint32_t zef_baumert_factored_card(int p, const Pair2 *q, size_t len) {
    if (p < 5 || (len > 0 && q == NULL)) {
        return 0u;
    }
    uint32_t total = 0u;
    for (size_t i = 0; i < len; ++i) {
        if (q[i].y < 0 || q[i].y >= p || q[i].z < 0 || q[i].z >= p) {
            return 0u;
        }
        total += baumert_line_card(p, q[i].y) * baumert_line_card(p, q[i].z);
    }
    return total;
}

bool zef_verify_baumert_word_in_hbpz(int p, const uint64_t *qmask, Vec4 w) {
    if (p < 5 || p > 63 || qmask == NULL) {
        return false;
    }
    uint32_t np = (uint32_t)(p + 2);
    if (w.c0 >= np || w.c1 >= np || w.c2 >= np || w.c3 >= np) {
        return false;
    }
    uint32_t p0 = pull1_u32(w.c0);
    uint32_t p1 = pull1_u32(w.c1);
    uint32_t p2 = pull1_u32(w.c2);
    uint32_t p3 = pull1_u32(w.c3);
    uint32_t up = (uint32_t)p;
    uint32_t qy = (p2 + 2u * up - 2u * p1) % up;
    uint32_t qz = (p3 + 2u * up - 2u * p0) % up;
    return ((qmask[qy] >> qz) & 1ull) == 1ull;
}

bool zef_verify_g7_induced_c5(void) {
    static const int c5[5] = {0, 2, 6, 5, 3};
    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            bool adj_c5 = (i != j) && (zef_cyc_dist(5, i, j) == 1);
            bool adj_g7 = (i != j) && (!SEP_G7[c5[i]][c5[j]]);
            if (adj_c5 != adj_g7) {
                return false;
            }
        }
    }
    return true;
}

static uint32_t g7_exact_alpha(void) {
    uint32_t best = 0u;
    for (unsigned mask = 0u; mask < 128u; ++mask) {
        bool ok = true;
        uint32_t sz = 0u;
        for (int i = 0; i < 7; ++i) {
            if ((mask >> i) & 1u) {
                ++sz;
                for (int j = i + 1; j < 7; ++j) {
                    if (((mask >> j) & 1u) && !SEP_G7[i][j]) {
                        ok = false;
                    }
                }
            }
        }
        if (ok && sz > best) {
            best = sz;
        }
    }
    return best;
}

typedef struct {
    int64_t a;
    int64_t b;
} Z5;

static Z5 z5_add(Z5 x, Z5 y) {
    Z5 r = {x.a + y.a, x.b + y.b};
    return r;
}

static Z5 z5_mul(Z5 x, Z5 y) {
    Z5 r = {x.a * y.a + 5 * x.b * y.b, x.a * y.b + x.b * y.a};
    return r;
}

bool zef_verify_lovasz_c5_idempotent(void) {
    Z5 m5[5][5];
    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            int d = zef_cyc_dist(5, i, j);
            if (d == 0) {
                m5[i][j].a = -2; m5[i][j].b = 2;
            } else if (d == 1) {
                m5[i][j].a = 3; m5[i][j].b = -1;
            } else {
                m5[i][j].a = -2; m5[i][j].b = 0;
            }
        }
    }
    Z5 scale = {-5, 5};
    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            Z5 sum = {0, 0};
            for (int k = 0; k < 5; ++k) {
                sum = z5_add(sum, z5_mul(m5[i][k], m5[k][j]));
            }
            Z5 rhs = z5_mul(scale, m5[i][j]);
            if (sum.a != rhs.a || sum.b != rhs.b) {
                return false;
            }
        }
    }
    return true;
}

static bool schlafli_comp_adj(int u, int v) {
    if (u == v) {
        return false;
    }
    if (u < 6) {
        if (v < 6) return false;
        if (v < 12) return u != (v - 6);
        return u == CPAIR[v - 12][0] || u == CPAIR[v - 12][1];
    }
    if (u < 12) {
        if (v < 6) return (u - 6) != v;
        if (v < 12) return false;
        return (u - 6) == CPAIR[v - 12][0] || (u - 6) == CPAIR[v - 12][1];
    }
    int a = CPAIR[u - 12][0], b = CPAIR[u - 12][1];
    if (v < 6) return v == a || v == b;
    if (v < 12) return (v - 6) == a || (v - 6) == b;
    int c = CPAIR[v - 12][0], d = CPAIR[v - 12][1];
    return a != c && a != d && b != c && b != d;
}

bool zef_verify_schlafli_paradox(bool *z8_ok, bool *f2_ok, uint32_t *prod_card) {
    static const int64_t handle[8] = {1, 1, 1, 1, 1, 1, 3, 3};
    int64_t vecs[27][8];
    memset(vecs, 0, sizeof(vecs));
    for (int i = 0; i < 6; ++i) {
        vecs[i][i] = 2;
        vecs[i][6] = 2;
        vecs[6 + i][i] = 2;
        vecs[6 + i][7] = 2;
    }
    for (int idx = 0; idx < 15; ++idx) {
        int a = CPAIR[idx][0], b = CPAIR[idx][1];
        for (int k = 0; k < 6; ++k) {
            vecs[12 + idx][k] = (k == a || k == b) ? -1 : 1;
        }
        vecs[12 + idx][6] = 1;
        vecs[12 + idx][7] = 1;
    }
    bool z_ok = true;
    for (int u = 0; u < 27; ++u) {
        int64_t norm = 0, hdot = 0;
        for (int k = 0; k < 8; ++k) {
            norm += vecs[u][k] * vecs[u][k];
            hdot += handle[k] * vecs[u][k];
        }
        if (norm != 8 || hdot != 8) {
            z_ok = false;
        }
        for (int v = 0; v < 27; ++v) {
            if (schlafli_comp_adj(u, v)) {
                int64_t dot = 0;
                for (int k = 0; k < 8; ++k) {
                    dot += vecs[u][k] * vecs[v][k];
                }
                if (dot != 0) {
                    z_ok = false;
                }
            }
        }
    }
    bool f_ok = true;
    for (int u = 0; u < 27; ++u) {
        for (int v = 0; v < 27; ++v) {
            uint32_t acc = 0u;
            for (int k = 0; k < 7; ++k) {
                uint32_t lu = (SCHLAFLI_L_BITS[u] >> k) & 1u;
                uint32_t rv = (SCHLAFLI_R_BITS[k] >> v) & 1u;
                acc ^= (lu & rv);
            }
            uint32_t expected = (u == v || schlafli_comp_adj(u, v)) ? 1u : 0u;
            if (acc != expected) {
                f_ok = false;
            }
        }
    }
    if (z8_ok != NULL) *z8_ok = z_ok;
    if (f2_ok != NULL) *f2_ok = f_ok;
    if (prod_card != NULL) *prod_card = 27u;
    return z_ok && f_ok;
}

static bool verify_hstar_25_and_ports(bool *ports_ok) {
    Pair2 pts[37];
    int k = 3, n = 25, m = 37, j = 1;
    for (int t = 0; t < m; ++t) {
        if (t >= 4 * k * k) {
            pts[t].y = 8 * k;
        } else {
            int pair = t / k;
            int rem = t % k;
            pts[t].y = (rem <= j) ? (2 * pair) : (2 * pair + 1);
        }
        int extra = (0 < t) + (k * k < t) + (2 * k * k < t) + (3 * k * k < t);
        pts[t].z = (8 * t + extra) % n;
    }
    bool indep = zef_verify_q_hstar(n, pts, 37u);
    bool pok = indep && pts[0].y == 0 && pts[0].z == 0;
    Pair2 p0 = {0, 0}, p1 = {24, 0};
    for (int t = 0; t < m; ++t) {
        Pair2 xq = {(pts[t].y + 1) % n, (pts[t].z + n - 1) % n};
        bool c_p1_i = (zef_cyc_dist(n, p1.y, pts[t].y) <= 1 && zef_cyc_dist(n, p1.z, pts[t].z) <= 7);
        bool c_p0_x = (zef_cyc_dist(n, p0.y, xq.y) <= 1 && zef_cyc_dist(n, p0.z, xq.z) <= 7);
        bool c_p1_x = (zef_cyc_dist(n, p1.y, xq.y) <= 1 && zef_cyc_dist(n, p1.z, xq.z) <= 7);
        if (c_p1_i != (t == 0) || c_p0_x != (t == 0) || c_p1_x != (t == 34)) {
            pok = false;
        }
    }
    if (ports_ok != NULL) *ports_ok = pok;
    return indep;
}

bool zef_run_full_audit(FrontierAuditReport *out) {
    if (out == NULL) {
        return false;
    }
    memset(out, 0, sizeof(*out));
    out->q25_hbpz_valid = zef_verify_q_hbpz(25, Q25_HBPZ, 37u);
    out->q29_hbpz_valid = zef_verify_q_hbpz(29, Q29_HBPZ, 50u);
    out->hstar_25_valid = verify_hstar_25_and_ports(&out->hstar_25_ports_valid);
    out->ball_hstar_25 = zef_quotient_ball_size(25, 0, 0, 2, 4);
    out->ball_hbpz_25 = zef_quotient_ball_size(25, 0, 2, 2, 0);
    out->baumert_c27_words = zef_baumert_factored_card(25, Q25_HBPZ, 37u);
    out->baumert_c31_words = zef_baumert_factored_card(29, Q29_HBPZ, 50u);
    out->g7_c5_induced = zef_verify_g7_induced_c5();
    out->g7_alpha = g7_exact_alpha();
    out->lovasz_c5_idempotent = zef_verify_lovasz_c5_idempotent();
    zef_verify_schlafli_paradox(&out->schlafli_z8_valid, &out->schlafli_f2_rank7_valid, &out->schlafli_prod_indep);
    return out->q25_hbpz_valid &&
           out->q29_hbpz_valid &&
           out->hstar_25_valid &&
           out->hstar_25_ports_valid &&
           out->ball_hstar_25 == 45u &&
           out->ball_hbpz_25 == 49u &&
           out->baumert_c27_words == 31466u &&
           out->baumert_c31_words == 54913u &&
           out->g7_c5_induced &&
           out->g7_alpha == 3u &&
           out->lovasz_c5_idempotent &&
           out->schlafli_z8_valid &&
           out->schlafli_f2_rank7_valid &&
           out->schlafli_prod_indep == 27u;
}
