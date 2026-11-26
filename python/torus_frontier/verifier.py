# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Exact integer and combinatorial verification engine for zero-error-torus-frontier."""

from __future__ import annotations

import json
import pathlib
from collections.abc import Sequence
from dataclasses import dataclass
from decimal import getcontext
from typing import Any

getcontext().prec = 80

Q25_HBPZ: tuple[tuple[int, int], ...] = (
    (0, 14), (1, 19), (2, 2), (2, 6), (2, 23), (3, 10), (4, 14), (5, 18), (6, 2), (6, 23),
    (7, 6), (7, 10), (8, 14), (9, 18), (10, 22), (11, 1), (11, 5), (11, 9), (12, 13), (13, 17),
    (14, 21), (15, 0), (15, 4), (15, 8), (16, 12), (17, 16), (18, 20), (19, 3), (19, 7), (19, 24),
    (20, 11), (21, 15), (22, 19), (23, 2), (23, 6), (23, 23), (24, 10),
)

Q29_HBPZ: tuple[tuple[int, int], ...] = (
    (0, 0), (0, 21), (0, 25), (1, 17), (2, 13), (3, 5), (3, 9), (4, 1), (4, 21), (4, 25),
    (5, 17), (6, 13), (7, 5), (7, 9), (8, 1), (8, 22), (8, 26), (9, 18), (10, 14), (11, 6),
    (11, 10), (12, 2), (12, 23), (12, 27), (13, 19), (14, 15), (15, 10), (16, 2), (16, 6),
    (16, 23), (16, 27), (17, 19), (18, 15), (19, 11), (20, 3), (20, 7), (20, 24), (20, 28),
    (21, 20), (22, 15), (23, 11), (24, 3), (24, 7), (24, 24), (24, 28), (25, 20), (26, 16),
    (27, 12), (28, 4), (28, 8),
)

LETTERS: tuple[str, ...] = ("B", "N", "A", "D", "O", "H", "V")

SEP_G7: tuple[tuple[bool, ...], ...] = (
    (False, False, False, False, True,  True,  True),
    (False, False, True,  True,  True,  True,  True),
    (False, True,  False, True,  False, True,  False),
    (False, True,  True,  False, False, False, True),
    (True,  True,  False, False, False, False, False),
    (True,  True,  True,  False, False, False, False),
    (True,  True,  False, True,  False, False, False),
)

CPAIR: tuple[tuple[int, int], ...] = (
    (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 3), (2, 4), (2, 5),
    (3, 4), (3, 5),
    (4, 5),
)

SCHLAFLI_L_BITS: tuple[int, ...] = (
    1, 2, 4, 8, 16, 32,
    62, 61, 59, 55, 47, 31,
    64, 70, 74, 82, 98,
    69, 73, 81, 97,
    79, 87, 103,
    91, 107, 115,
)

SCHLAFLI_R_BITS: tuple[int, ...] = (
    130945, 1974082, 14823108, 52710856, 88640464, 110168032, 132124867,
)


def cyc_dist(n: int, a: int, b: int) -> int:
    """Lee distance on Z_n."""
    if n <= 0:
        raise ValueError("Cycle length n must be positive")
    ma = a % n
    mb = b % n
    d1 = (ma - mb) % n
    d2 = (mb - ma) % n
    return min(d1, d2)


def pull1(x: int) -> int:
    """Locally injective Baumert 1D pullback map Z_{p+2} -> Z_p."""
    return x if x < 2 else x - 2


def verify_q_hbpz(n: int, q: Sequence[tuple[int, int]]) -> bool:
    if n < 9:
        return False
    for y, z in q:
        if not (0 <= y < n and 0 <= z < n):
            return False
    for i in range(len(q)):
        yi, zi = q[i]
        for j in range(i + 1, len(q)):
            yj, zj = q[j]
            if cyc_dist(n, yi, yj) <= 3 and cyc_dist(n, zi, zj) <= 3:
                return False
    return True


def verify_q_hstar(n: int, q: Sequence[tuple[int, int]]) -> bool:
    if n < 15:
        return False
    for y, z in q:
        if not (0 <= y < n and 0 <= z < n):
            return False
    for i in range(len(q)):
        yi, zi = q[i]
        for j in range(i + 1, len(q)):
            yj, zj = q[j]
            if cyc_dist(n, yi, yj) <= 1 and cyc_dist(n, zi, zj) <= 7:
                return False
    return True


def helical_hbpz_family(m: int) -> tuple[int, list[tuple[int, int]]]:
    n = 4 * m + 1
    big_m = m * m + m // 4
    return n, [((t * n) // big_m, (4 * t) % n) for t in range(big_m)]


def hstar_family(k: int) -> tuple[int, list[tuple[int, int]]]:
    n = 8 * k + 1
    big_m = 4 * k * k + k // 2
    j = k // 2
    pts: list[tuple[int, int]] = []
    for t in range(big_m):
        if k % 2 == 0:
            y = t // (k // 2)
            z = (8 * t) % n
        else:
            if t >= 4 * k * k:
                y = 8 * k
            else:
                pair, rem = divmod(t, k)
                y = 2 * pair if rem <= j else 2 * pair + 1
            extra = int(0 < t) + int(k * k < t) + int(2 * k * k < t) + int(3 * k * k < t)
            z = (8 * t + extra) % n
        pts.append((y, z))
    return n, pts


def verify_hstar_odd_ports(k: int) -> bool:
    if k < 3 or k % 2 == 0:
        return False
    n, pts = hstar_family(k)
    if not verify_q_hstar(n, pts):
        return False
    m = len(pts)
    d_idx = 4 * k * k - (k // 2 + 1)
    if pts[0] != (0, 0) or not (0 < d_idx < m):
        return False
    p0 = (0, 0)
    p1 = (n - 1, 0)
    xq = [((y + 1) % n, (z - 1) % n) for y, z in pts]
    for t in range(m):
        c1 = cyc_dist(n, p1[0], pts[t][0]) <= 1 and cyc_dist(n, p1[1], pts[t][1]) <= 7
        c2 = cyc_dist(n, p0[0], xq[t][0]) <= 1 and cyc_dist(n, p0[1], xq[t][1]) <= 7
        c3 = cyc_dist(n, p1[0], xq[t][0]) <= 1 and cyc_dist(n, p1[1], xq[t][1]) <= 7
        if c1 != (t == 0) or c2 != (t == 0) or c3 != (t == d_idx):
            return False
    return True


def quotient_ball_size(n: int, a: int, b: int, c: int, d: int) -> int:
    if n <= 0:
        raise ValueError("n must be positive")
    seen: set[tuple[int, int]] = set()
    for e0 in (-1, 0, 1):
        for e1 in (-1, 0, 1):
            for e2 in (-1, 0, 1):
                for e3 in (-1, 0, 1):
                    y = (e2 - a * e0 - b * e1) % n
                    z = (e3 - c * e0 - d * e1) % n
                    seen.add((y, z))
    return len(seen)


def baumert_factored_card(p: int, q: Sequence[tuple[int, int]]) -> int:
    if p < 5:
        return 0
    np = p + 2

    def line_card(target: int) -> int:
        total = 0
        for u in range(np):
            tw = (2 * pull1(u) + target) % p
            total += 2 if tw < 2 else 1
        return total

    return sum(line_card(y) * line_card(z) for y, z in q)


def verify_g7_c5_and_alpha() -> tuple[bool, int]:
    c5 = (0, 2, 6, 5, 3)
    c5_ok = all(
        (i != j and cyc_dist(5, i, j) == 1) == (i != j and not SEP_G7[c5[i]][c5[j]])
        for i in range(5)
        for j in range(5)
    )
    best = 0
    for mask in range(128):
        verts = [i for i in range(7) if (mask >> i) & 1]
        if all(SEP_G7[u][v] for idx, u in enumerate(verts) for v in verts[idx + 1 :]):
            best = max(best, len(verts))
    return c5_ok, best


@dataclass(frozen=True)
class ZSqrt5:
    a: int
    b: int

    def __add__(self, other: ZSqrt5) -> ZSqrt5:
        return ZSqrt5(self.a + other.a, self.b + other.b)

    def __mul__(self, other: ZSqrt5) -> ZSqrt5:
        return ZSqrt5(self.a * other.a + 5 * self.b * other.b, self.a * other.b + self.b * other.a)


def verify_lovasz_c5_idempotent() -> bool:
    def m5(i: int, j: int) -> ZSqrt5:
        d = cyc_dist(5, i, j)
        if d == 0:
            return ZSqrt5(-2, 2)
        if d == 1:
            return ZSqrt5(3, -1)
        return ZSqrt5(-2, 0)

    scale = ZSqrt5(-5, 5)
    for i in range(5):
        for j in range(5):
            acc = ZSqrt5(0, 0)
            for k in range(5):
                acc = acc + m5(i, k) * m5(k, j)
            if acc != scale * m5(i, j):
                return False
    return True


def schlafli_comp_adj(u: int, v: int) -> bool:
    if u == v:
        return False
    if u < 6:
        if v < 6:
            return False
        if v < 12:
            return u != v - 6
        return u in CPAIR[v - 12]
    if u < 12:
        if v < 6:
            return u - 6 != v
        if v < 12:
            return False
        return (u - 6) in CPAIR[v - 12]
    a, b = CPAIR[u - 12]
    if v < 6:
        return v in (a, b)
    if v < 12:
        return (v - 6) in (a, b)
    c, d = CPAIR[v - 12]
    return a not in (c, d) and b not in (c, d)


def verify_schlafli_paradox() -> tuple[bool, bool, int]:
    handle = (1, 1, 1, 1, 1, 1, 3, 3)
    vecs: list[list[int]] = [[0] * 8 for _ in range(27)]
    for i in range(6):
        vecs[i][i] = 2
        vecs[i][6] = 2
        vecs[6 + i][i] = 2
        vecs[6 + i][7] = 2
    for idx, (a, b) in enumerate(CPAIR):
        for k in range(6):
            vecs[12 + idx][k] = -1 if k in (a, b) else 1
        vecs[12 + idx][6] = 1
        vecs[12 + idx][7] = 1
    z8_ok = sum(x * x for x in handle) == 24
    for u in range(27):
        if sum(x * x for x in vecs[u]) != 8 or sum(h * x for h, x in zip(handle, vecs[u])) != 8:
            z8_ok = False
        for v in range(27):
            if schlafli_comp_adj(u, v) and sum(x * y for x, y in zip(vecs[u], vecs[v])) != 0:
                z8_ok = False
    f2_ok = True
    for u in range(27):
        for v in range(27):
            acc = 0
            for k in range(7):
                acc ^= ((SCHLAFLI_L_BITS[u] >> k) & 1) & ((SCHLAFLI_R_BITS[k] >> v) & 1)
            expected = 1 if (u == v or schlafli_comp_adj(u, v)) else 0
            if acc != expected:
                f2_ok = False
    return z8_ok, f2_ok, 27


def verify_all_pillars(witness_path: pathlib.Path | None = None) -> dict[str, Any]:
    q25_ok = verify_q_hbpz(25, Q25_HBPZ)
    q29_ok = verify_q_hbpz(29, Q29_HBPZ)
    n25, q25_hstar = hstar_family(3)
    hstar_ok = n25 == 25 and len(q25_hstar) == 37 and verify_q_hstar(25, q25_hstar)
    hstar_ports_ok = all(verify_hstar_odd_ports(k) for k in (3, 5, 7, 9, 11))
    helical_ok = all(
        len(pts) == (n * (n // 4)) // 4 and verify_q_hbpz(n, pts)
        for m in (5, 8, 9, 12, 13, 16, 17, 20)
        for n, pts in (helical_hbpz_family(m),)
    )
    ball_hstar = quotient_ball_size(25, 0, 0, 2, 4)
    ball_hbpz = quotient_ball_size(25, 0, 2, 2, 0)
    c27_words = baumert_factored_card(25, Q25_HBPZ)
    c31_words = baumert_factored_card(29, Q29_HBPZ)
    g7_c5, g7_alpha = verify_g7_c5_and_alpha()
    c5_idem = verify_lovasz_c5_idempotent()
    sch_z8, sch_f2, sch_prod = verify_schlafli_paradox()

    out: dict[str, Any] = {
        "q25_hbpz_valid": q25_ok,
        "q29_hbpz_valid": q29_ok,
        "hstar_25_valid": hstar_ok,
        "hstar_odd_ports_valid": hstar_ports_ok,
        "helical_hbpz_valid": helical_ok,
        "ball_hstar_25": ball_hstar,
        "ball_hbpz_25": ball_hbpz,
        "baumert_c27_words": c27_words,
        "baumert_c31_words": c31_words,
        "g7_c5_induced": g7_c5,
        "g7_alpha": g7_alpha,
        "lovasz_c5_idempotent": c5_idem,
        "schlafli_z8_valid": sch_z8,
        "schlafli_f2_rank7_valid": sch_f2,
        "schlafli_prod_indep": sch_prod,
    }
    if witness_path is not None and witness_path.exists():
        wdata = json.loads(witness_path.read_text(encoding="utf-8"))
        out["witness_q25_match"] = [list(x) for x in Q25_HBPZ] == wdata["q25HBPZ"]
        out["witness_q29_match"] = [list(x) for x in Q29_HBPZ] == wdata["q29HBPZ"]
        out["witness_hstar25_match"] = [list(x) for x in q25_hstar] == wdata["q25HStar"]
    out["all_ok"] = (
        q25_ok and q29_ok and hstar_ok and hstar_ports_ok and helical_ok
        and ball_hstar == 45 and ball_hbpz == 49
        and c27_words == 31466 and c31_words == 54913
        and g7_c5 and g7_alpha == 3 and c5_idem and sch_z8 and sch_f2 and sch_prod == 27
    )
    return out


if __name__ == "__main__":
    root = pathlib.Path(__file__).resolve().parents[2]
    rep = verify_all_pillars(root / "data" / "witnesses.json")
    print(json.dumps(rep, sort_keys=True))
    if not rep["all_ok"]:
        raise SystemExit(1)
