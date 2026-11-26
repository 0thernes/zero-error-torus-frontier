/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 */
#include "torus_frontier.h"

#include <stdio.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc > 1 && (strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-h") == 0)) {
        printf("torus_cli v1.0.0 (ISO C11 verifier)\n");
        printf("Usage: torus_cli [--verify-all|--json]\n");
        return 0;
    }
    FrontierAuditReport rep;
    bool ok = zef_run_full_audit(&rep);
    printf(
        "{\"all_ok\":%s,\"q25_hbpz_valid\":%s,\"q29_hbpz_valid\":%s,"
        "\"hstar_25_valid\":%s,\"hstar_25_ports_valid\":%s,"
        "\"ball_hstar_25\":%u,\"ball_hbpz_25\":%u,"
        "\"baumert_c27_words\":%u,\"baumert_c31_words\":%u,"
        "\"g7_c5_induced\":%s,\"g7_alpha\":%u,"
        "\"lovasz_c5_idempotent\":%s,\"schlafli_z8_valid\":%s,"
        "\"schlafli_f2_rank7_valid\":%s,\"schlafli_prod_indep\":%u}\n",
        ok ? "true" : "false",
        rep.q25_hbpz_valid ? "true" : "false",
        rep.q29_hbpz_valid ? "true" : "false",
        rep.hstar_25_valid ? "true" : "false",
        rep.hstar_25_ports_valid ? "true" : "false",
        rep.ball_hstar_25,
        rep.ball_hbpz_25,
        rep.baumert_c27_words,
        rep.baumert_c31_words,
        rep.g7_c5_induced ? "true" : "false",
        rep.g7_alpha,
        rep.lovasz_c5_idempotent ? "true" : "false",
        rep.schlafli_z8_valid ? "true" : "false",
        rep.schlafli_f2_rank7_valid ? "true" : "false",
        rep.schlafli_prod_indep
    );
    return ok ? 0 : 1;
}
