# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Core Python package for zero-error-torus-frontier (v1.0.0)."""

from .verifier import (
    Q25_HBPZ,
    Q29_HBPZ,
    SEP_G7,
    baumert_factored_card,
    cyc_dist,
    helical_hbpz_family,
    hstar_family,
    pull1,
    quotient_ball_size,
    verify_all_pillars,
    verify_g7_c5_and_alpha,
    verify_hstar_odd_ports,
    verify_lovasz_c5_idempotent,
    verify_q_hbpz,
    verify_q_hstar,
    verify_schlafli_paradox,
)

__version__ = "1.0.0"
__all__ = [
    "Q25_HBPZ",
    "Q29_HBPZ",
    "SEP_G7",
    "__version__",
    "baumert_factored_card",
    "cyc_dist",
    "helical_hbpz_family",
    "hstar_family",
    "pull1",
    "quotient_ball_size",
    "verify_all_pillars",
    "verify_g7_c5_and_alpha",
    "verify_hstar_odd_ports",
    "verify_lovasz_c5_idempotent",
    "verify_q_hbpz",
    "verify_q_hstar",
    "verify_schlafli_paradox",
]
