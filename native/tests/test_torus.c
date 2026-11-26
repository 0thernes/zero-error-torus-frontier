/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 */
#include "torus_frontier.h"

#include <assert.h>
#include <stdio.h>

int main(void) {
    FrontierAuditReport rep;
    bool ok = zef_run_full_audit(&rep);
    if (!ok) {
        fprintf(stderr, "zef_run_full_audit failed\n");
        return 1;
    }
    assert(ok);
    assert(rep.ball_hstar_25 == 45u);
    assert(rep.ball_hbpz_25 == 49u);
    assert(rep.baumert_c27_words == 31466u);
    assert(rep.baumert_c31_words == 54913u);
    assert(rep.g7_c5_induced);
    assert(rep.g7_alpha == 3u);
    assert(rep.lovasz_c5_idempotent);
    assert(rep.schlafli_z8_valid);
    assert(rep.schlafli_f2_rank7_valid);
    assert(rep.schlafli_prod_indep == 27u);

    /* Negative tests (B06): colliding and out-of-range inputs MUST be rejected */
    Pair2 bad_hbpz[2] = {{0, 0}, {2, 2}};
    assert(!zef_verify_q_hbpz(25, bad_hbpz, 2u));
    assert(!zef_verify_q_hbpz(7, bad_hbpz, 1u));
    assert(!zef_verify_q_hbpz(25, NULL, 1u));
    Pair2 oob[1] = {{25, 0}};
    assert(!zef_verify_q_hbpz(25, oob, 1u));
    assert(!zef_verify_q_hstar(25, bad_hbpz, 2u));
    assert(zef_baumert_factored_card(3, bad_hbpz, 1u) == 0u);
    assert(zef_quotient_ball_size(0, 0, 0, 2, 4) == 0u);

    printf("C11 unit & negative tests: ALL PASSED\n");
    return 0;
}
