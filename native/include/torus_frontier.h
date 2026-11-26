/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 */
#ifndef ZERO_ERROR_TORUS_FRONTIER_H
#define ZERO_ERROR_TORUS_FRONTIER_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    int y;
    int z;
} Pair2;

typedef struct {
    uint32_t c0;
    uint32_t c1;
    uint32_t c2;
    uint32_t c3;
} Vec4;

typedef struct {
    bool q25_hbpz_valid;
    bool q29_hbpz_valid;
    bool hstar_25_valid;
    bool hstar_25_ports_valid;
    uint32_t ball_hstar_25;
    uint32_t ball_hbpz_25;
    uint32_t baumert_c27_words;
    uint32_t baumert_c31_words;
    bool g7_c5_induced;
    uint32_t g7_alpha;
    bool lovasz_c5_idempotent;
    bool schlafli_z8_valid;
    bool schlafli_f2_rank7_valid;
    uint32_t schlafli_prod_indep;
} FrontierAuditReport;

int zef_cyc_dist(int n, int a, int b);
bool zef_verify_q_hbpz(int n, const Pair2 *q, size_t len);
bool zef_verify_q_hstar(int n, const Pair2 *q, size_t len);
uint32_t zef_quotient_ball_size(int n, int a, int b, int c, int d);
uint32_t zef_baumert_factored_card(int p, const Pair2 *q, size_t len);
bool zef_verify_baumert_word_in_hbpz(int p, const uint64_t *qmask, Vec4 w);
bool zef_verify_g7_induced_c5(void);
bool zef_verify_lovasz_c5_idempotent(void);
bool zef_verify_schlafli_paradox(bool *z8_ok, bool *f2_ok, uint32_t *prod_card);
bool zef_run_full_audit(FrontierAuditReport *out);

#ifdef __cplusplus
}
#endif

#endif /* ZERO_ERROR_TORUS_FRONTIER_H */
