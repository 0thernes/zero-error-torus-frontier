/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * libFuzzer harness (Build Standard B15) exercising all public C11 verifier entry points:
 *   clang -std=c11 -g -O1 -fsanitize=fuzzer,address,undefined \
 *     -Inative/include native/src/torus_frontier.c native/tests/libfuzzer_torus.c -o build/libfuzzer_torus
 */
#include "torus_frontier.h"

#include <stddef.h>
#include <stdint.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (size < 6u) {
        return 0;
    }
    int n = (int)(data[0] % 45u) - 5;
    int a = (int)data[1] - 64;
    int b = (int)data[2] - 64;
    int d1 = zef_cyc_dist(n, a, b);
    int d2 = zef_cyc_dist(n, b, a);
    if (d1 != d2) {
        __builtin_trap();
    }
    if (n > 0 && (d1 < 0 || d1 > n / 2)) {
        __builtin_trap();
    }
    size_t len = (size - 3u) / 2u;
    if (len > 32u) {
        len = 32u;
    }
    Pair2 pts[32];
    for (size_t i = 0; i < len; ++i) {
        pts[i].y = (int)data[3u + 2u * i] % 40 - 2;
        pts[i].z = (int)data[4u + 2u * i] % 40 - 2;
    }
    (void)zef_verify_q_hbpz(n, pts, len);
    (void)zef_verify_q_hstar(n, pts, len);
    (void)zef_baumert_factored_card(n, pts, len);
    uint32_t bsz = zef_quotient_ball_size(
        (int)(data[0] % 29u),
        (int)(data[1] % 19u),
        (int)(data[2] % 19u),
        (int)(data[3] % 19u),
        (int)(data[4] % 19u)
    );
    if (bsz > 81u) {
        __builtin_trap();
    }
    return 0;
}
