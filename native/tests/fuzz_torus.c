/* SPDX-License-Identifier: Apache-2.0
 * Copyright (c) 2026 Alexander Stephen Donahue
 *
 * Deterministic PRNG fuzz harness (Build Standard B15/B16) exercising all
 * public C11 entry points on arbitrary / adversarial inputs under ASan+UBSan.
 */
#include "torus_frontier.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t xorshift64(uint64_t *state) {
    uint64_t x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    return x;
}

int main(int argc, char **argv) {
    unsigned long iters = 25000ul;
    if (argc > 1) {
        long parsed = strtol(argv[1], NULL, 10);
        if (parsed > 0) {
            iters = (unsigned long)parsed;
        }
    }
    uint64_t rng = 0x2026014CAFEBABE1ull;
    for (unsigned long it = 0; it < iters; ++it) {
        int n = (int)(xorshift64(&rng) % 45ull) - 5;
        int a = (int)(xorshift64(&rng) % 60ull) - 10;
        int b = (int)(xorshift64(&rng) % 60ull) - 10;
        int d1 = zef_cyc_dist(n, a, b);
        int d2 = zef_cyc_dist(n, b, a);
        assert(d1 == d2);
        if (n > 0) {
            assert(d1 >= 0 && d1 <= n / 2);
        } else {
            assert(d1 == 0);
        }

        size_t len = (size_t)(xorshift64(&rng) % 12ull);
        Pair2 pts[12];
        for (size_t i = 0; i < len; ++i) {
            pts[i].y = (int)(xorshift64(&rng) % 40ull) - 2;
            pts[i].z = (int)(xorshift64(&rng) % 40ull) - 2;
        }
        (void)zef_verify_q_hbpz(n, pts, len);
        (void)zef_verify_q_hstar(n, pts, len);
        (void)zef_baumert_factored_card(n, pts, len);

        if ((it & 127ul) == 0ul) {
            int bn = (int)(xorshift64(&rng) % 29ull);
            uint32_t bsz = zef_quotient_ball_size(
                bn,
                (int)(xorshift64(&rng) % 19ull),
                (int)(xorshift64(&rng) % 19ull),
                (int)(xorshift64(&rng) % 19ull),
                (int)(xorshift64(&rng) % 19ull)
            );
            assert(bsz <= 81u);
        }
    }
    printf("C11 fuzz harness (%lu iterations): PASS\n", iters);
    return 0;
}
