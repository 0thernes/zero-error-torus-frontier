# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Comprehensive Build Standard v1.2.0 test suite (B03, B05-B14, B20)."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
sys.path.insert(0, str(ROOT / "reference"))

from capacity_oracle import certify_all_four_records, lovasz_theta_odd_cycle
from torus_frontier.verifier import (
    Q25_HBPZ,
    Q29_HBPZ,
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

# ---------------------------------------------------------------------------
# B05: Falsifiable tests per claim (C-1a .. C-4d)
# ---------------------------------------------------------------------------

def test_pillar1_quotient_packings_and_infinite_families() -> None:
    assert verify_q_hbpz(25, Q25_HBPZ)
    assert verify_q_hbpz(29, Q29_HBPZ)
    assert len(Q25_HBPZ) == 37
    assert len(Q29_HBPZ) == 50 == (29 * (29 // 4)) // 4
    # C-1c: 45 vs 49 ball dichotomy
    for n in (19, 21, 23, 25):
        assert quotient_ball_size(n, 0, 0, 2, 4) == 45
        assert quotient_ball_size(n, 0, 2, 2, 0) == 49
    # C-1d: Infinite helical H_BPZ family
    for m in (5, 8, 9, 12, 13, 16, 17, 20, 21, 24):
        n, pts = helical_hbpz_family(m)
        assert len(pts) == (n * (n // 4)) // 4
        assert verify_q_hbpz(n, pts)
    # C-1e: Infinite H* family and odd-k port systems
    for k in range(3, 16):
        n, pts = hstar_family(k)
        assert len(pts) == (n * (n // 8)) // 2
        assert verify_q_hstar(n, pts)
        if k % 2 == 1:
            assert verify_hstar_odd_ports(k)


def test_pillar2_exact_world_records_oracle() -> None:
    """B12 exact arbitrary-precision oracle check against Lean WorldRecords.lean targets."""
    recs = certify_all_four_records()
    assert recs["C25"]["target_int"] == 12344196091426841
    assert recs["C27"]["target_int"] == 13319390984674515
    assert recs["C29"]["target_int"] == 14319949949077991
    assert recs["C31"]["target_int"] == 15308776193986504
    assert recs["C25"]["g7_barrier_exact"] == "46875/2"
    # Every certified lower bound strictly surpasses Baumert-Hales AND stays below Lovasz theta!
    bh = {"C25": 12.3310604178, "C27": 13.3176204000, "C29": 14.3045513000, "C31": 15.2906289000}
    for k, n in (("C25", 25), ("C27", 27), ("C29", 29), ("C31", 31)):
        val = recs[k]["target_int"] / 1e15
        assert val > bh[k], f"{k} must beat Baumert-Hales"
        assert val < float(lovasz_theta_odd_cycle(n)), f"{k} cannot exceed Lovasz theta"


def test_pillar3_and_pillar4() -> None:
    assert verify_g7_c5_and_alpha() == (True, 3)
    assert verify_lovasz_c5_idempotent() is True
    assert verify_schlafli_paradox() == (True, True, 27)


# ---------------------------------------------------------------------------
# B06: Negative & boundary tests
# ---------------------------------------------------------------------------

def test_negative_invalid_inputs_rejected() -> None:
    assert not verify_q_hbpz(7, [(0, 0)])
    assert not verify_q_hbpz(25, [(0, 0), (3, 3)])
    assert not verify_q_hbpz(25, [(25, 0)])
    assert not verify_q_hstar(13, [(0, 0)])
    assert not verify_q_hstar(25, [(0, 0), (1, 7)])
    assert not verify_hstar_odd_ports(4)
    assert not verify_hstar_odd_ports(1)
    assert baumert_factored_card(3, [(0, 0)]) == 0
    with pytest.raises(ValueError):
        cyc_dist(0, 1, 2)


# ---------------------------------------------------------------------------
# B07: Regression tests for bugs caught during development
# ---------------------------------------------------------------------------

def test_regression_hstar_four_jump_staircase_and_lovasz_j_term() -> None:
    # Regression 1: H* odd-k requires the exact 4-jump staircase (not linear slope), verified for k=3,5,7
    n, pts = hstar_family(3)
    assert n == 25 and len(pts) == 37
    assert pts[0] == (0, 0) and pts[34] == (22, 1)
    assert verify_hstar_odd_ports(3)
    # Regression 2: Lovasz M_5 requires non-edge entry -2 (subtracting J) for idempotence
    assert verify_lovasz_c5_idempotent()


# ---------------------------------------------------------------------------
# B08 & B09: Golden snapshot & JSON schema contract tests
# ---------------------------------------------------------------------------

def test_golden_witnesses_contract() -> None:
    wpath = ROOT / "data" / "witnesses.json"
    data = json.loads(wpath.read_text(encoding="utf-8"))
    assert data["schema_version"] == "1.0.0"
    assert data["archive_id"] == "0TH-2026-016"
    assert set(data["records"].keys()) == {"C25", "C27", "C29", "C31"}
    assert len(data["c27_baumert_ports"]["ports"]) == 88
    assert len(data["c27_baumert_ports"]["A"]) == 237
    assert len(data["c27_baumert_ports"]["D"]) == 150
    assert len(data["c31_baumert_ports"]["ports"]) == 133
    assert len(data["c31_baumert_ports"]["A"]) == 337
    assert len(data["c31_baumert_ports"]["D"]) == 205
    rep = verify_all_pillars(wpath)
    assert rep["all_ok"] is True
    assert rep["witness_q25_match"] is True
    assert rep["witness_q29_match"] is True
    assert rep["witness_hstar25_match"] is True


# ---------------------------------------------------------------------------
# B10: Property-based tests (Hypothesis)
# ---------------------------------------------------------------------------

@given(
    n=st.integers(min_value=5, max_value=80),
    a=st.integers(min_value=0, max_value=200),
    b=st.integers(min_value=0, max_value=200),
    s=st.integers(min_value=0, max_value=200),
)
@settings(max_examples=200)
def test_property_cyc_dist_metric_and_shift_invariance(n: int, a: int, b: int, s: int) -> None:
    d = cyc_dist(n, a, b)
    assert 0 <= d <= n // 2
    assert d == cyc_dist(n, b, a)
    assert cyc_dist(n, a + s, b + s) == d
    assert (d == 0) == (a % n == b % n)


@given(
    p=st.integers(min_value=5, max_value=45),
    u=st.integers(min_value=0, max_value=46),
    v=st.integers(min_value=0, max_value=46),
)
@settings(max_examples=200)
def test_property_baumert_pull1_locally_injective(p: int, u: int, v: int) -> None:
    np_ = p + 2
    u %= np_
    v %= np_
    if cyc_dist(np_, u, v) <= 1:
        assert cyc_dist(p, pull1(u), pull1(v)) <= 1
        if pull1(u) == pull1(v):
            assert u == v


# ---------------------------------------------------------------------------
# B14: Metamorphic tests (cyclic shift invariance of quotient packings)
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("sy,sz", [(1, 0), (0, 7), (13, 19), (24, 24)])
def test_metamorphic_torus_translation_invariance(sy: int, sz: int) -> None:
    shifted_25 = [((y + sy) % 25, (z + sz) % 25) for y, z in Q25_HBPZ]
    assert verify_q_hbpz(25, shifted_25)
    _, qstar = hstar_family(3)
    shifted_star = [((y + sy) % 25, (z + sz) % 25) for y, z in qstar]
    assert verify_q_hstar(25, shifted_star)


# ---------------------------------------------------------------------------
# B11: Cross-language differential test (Python vs Rust binary, and C11 if built)
# ---------------------------------------------------------------------------

def test_differential_python_vs_rust_and_c11() -> None:
    py_rep = verify_all_pillars(ROOT / "data" / "witnesses.json")
    rust_bin = ROOT / "rust" / "target" / "release" / ("zero-error-torus-frontier.exe" if sys.platform == "win32" else "zero-error-torus-frontier")
    if rust_bin.exists():
        out = subprocess.check_output([str(rust_bin), "--verify-all"], text=True).strip()
        rs_rep = json.loads(out)
        for key in (
            "all_ok", "q25_hbpz_valid", "q29_hbpz_valid", "hstar_25_valid",
            "ball_hstar_25", "ball_hbpz_25", "baumert_c27_words", "baumert_c31_words",
            "g7_c5_induced", "g7_alpha", "lovasz_c5_idempotent",
            "schlafli_z8_valid", "schlafli_f2_rank7_valid", "schlafli_prod_indep",
        ):
            assert py_rep[key] == rs_rep[key], f"Python/Rust mismatch on {key}"
    c_bin = ROOT / "native" / "build" / ("torus_cli.exe" if sys.platform == "win32" else "torus_cli")
    if c_bin.exists():
        out = subprocess.check_output([str(c_bin), "--verify-all"], text=True).strip()
        c_rep = json.loads(out)
        for key in (
            "all_ok", "q25_hbpz_valid", "q29_hbpz_valid", "hstar_25_valid",
            "ball_hstar_25", "ball_hbpz_25", "baumert_c27_words", "baumert_c31_words",
            "g7_c5_induced", "g7_alpha", "lovasz_c5_idempotent",
            "schlafli_z8_valid", "schlafli_f2_rank7_valid", "schlafli_prod_indep",
        ):
            assert py_rep[key] == c_rep[key], f"Python/C11 mismatch on {key}"


# ---------------------------------------------------------------------------
# B13: Deterministic mutation-kill verification (planted faults MUST be caught!)
# ---------------------------------------------------------------------------

def test_mutation_kill_planted_faults() -> None:
    # Mutant 1: perturb a single coordinate of Q25_HBPZ to create a collision -> MUST fail
    mut_q25 = list(Q25_HBPZ)
    mut_q25[0] = (mut_q25[1][0], (mut_q25[1][1] + 2) % 25)
    assert not verify_q_hbpz(25, mut_q25)

    # Mutant 2: perturb a single coordinate of H* -> MUST fail
    _, mut_hs = hstar_family(3)
    mut_hs[0] = (mut_hs[1][0], (mut_hs[1][1] + 5) % 25)
    assert not verify_q_hstar(25, mut_hs)

    # Mutant 3: add 1 ULP to every certified 15-decimal record -> MUST violate exact inequality!
    recs = certify_all_four_records()
    assert (recs["C29"]["target_int"] + 1) ** 4 > 42050 * (10**15) ** 4


# ---------------------------------------------------------------------------
# B03: Determinism check
# ---------------------------------------------------------------------------

def test_determinism_identical_across_runs() -> None:
    r1 = verify_all_pillars(ROOT / "data" / "witnesses.json")
    r2 = verify_all_pillars(ROOT / "data" / "witnesses.json")
    assert r1 == r2
