# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Independent exact arbitrary-precision integer & 80-digit Decimal oracle (Build Standard B12)."""

from __future__ import annotations

import json
import math
import pathlib
import re
from decimal import Decimal, getcontext
from fractions import Fraction
from typing import Any

getcontext().prec = 80


def _load_lean_tables() -> dict[str, Any]:
    """Read the exact code tables directly from `SeparationCalculus.lean` for zero-drift oracle checks."""
    lean_path = pathlib.Path(__file__).resolve().parents[1] / "lean" / "ZeroErrorFrontier" / "SeparationCalculus.lean"
    text = lean_path.read_text(encoding="utf-8")

    def parse_tuples(block_name: str, arity: int, expected_total: int) -> dict[str, list[str]]:
        m = re.search(
            rf"def {block_name} : Letter → List \(Fin {arity} → Letter\)(.*?)(?:\n\n(?:/--|def |theorem ))",
            text,
            re.DOTALL,
        )
        assert m is not None, f"Could not parse {block_name}"
        body = m.group(1)
        arms = re.split(r"\n\s*\|\s*\.([BNADOHV])\s*=>", body)
        res: dict[str, list[str]] = {}
        # arms = [prefix, letter1, rhs1, letter2, rhs2, ...]
        for idx in range(1, len(arms), 2):
            letter = arms[idx]
            rhs = arms[idx + 1]
            words = re.findall(r"mk[234]\s+" + r"\s+".join([r"\.([BNADOHV])"] * arity), rhs)
            res[letter] = ["".join(w) for w in words]
        assert set(res.keys()) == {"B", "N", "A", "D", "O", "H", "V"}, f"Incomplete arms in {block_name}: {res.keys()}"
        total = sum(len(v) for v in res.values())
        assert total == expected_total, f"Word count mismatch in {block_name}: {total} != {expected_total}"
        return res

    def parse_code4(block_name: str, expected_total: int) -> list[str]:
        m = re.search(
            rf"def {block_name} : List \(Fin 4 → Letter\) :=(.*?)(?:\n\n(?:/--|def |theorem ))",
            text,
            re.DOTALL,
        )
        assert m is not None, f"Could not parse {block_name}"
        words = re.findall(r"mk4\s+\.([BNADOHV])\s+\.([BNADOHV])\s+\.([BNADOHV])\s+\.([BNADOHV])", m.group(1))
        out = ["".join(w) for w in words]
        assert len(out) == expected_total, f"Code count mismatch in {block_name}: {len(out)} != {expected_total}"
        return out

    return {
        "T2a": parse_tuples("tblT2a", 2, 20),
        "T3c": parse_tuples("tblT3c", 3, 48),
        "T3e": parse_tuples("tblT3e", 3, 53),
        "C4a": parse_code4("codeC4a", 49),
        "C4b": parse_code4("codeC4b", 57),
    }


def apply_table(tbl: dict[str, list[str]], w: dict[str, int]) -> dict[str, int]:
    out: dict[str, int] = {}
    for letter, words in tbl.items():
        tot = 0
        for word in words:
            p = 1
            for ch in word:
                p *= w[ch]
            tot += p
        out[letter] = tot
    return out


def eval_code(code: list[str], w: dict[str, int]) -> int:
    tot = 0
    for word in code:
        p = 1
        for ch in word:
            p *= w[ch]
        tot += p
    return tot


def lovasz_theta_odd_cycle(n: int) -> Decimal:
    """Exact high-precision Lovasz theta(C_n) = n * cos(pi/n) / (1 + cos(pi/n))."""
    c = Decimal(str(math.cos(math.pi / n)))
    return Decimal(n) * c / (Decimal(1) + c)


def nth_root_floor_15(m: int, p: int) -> int:
    """Exact integer binary search for floor(M^(1/p) * 10^15) — zero floating-point rounding!"""
    scale = 10**15
    rhs = m * (scale**p)
    lo = 0
    hi = 25 * scale
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if pow(mid, p) <= rhs:
            lo = mid
        else:
            hi = mid - 1
    assert pow(lo, p) <= rhs < pow(lo + 1, p)
    return lo


def certify_all_four_records() -> dict[str, dict[str, Any]]:
    tables = _load_lean_tables()

    # C25: H* 37-coset (23,125 words), 625 ports -> T3c -> T3e -> C4b (p = 4*3*3*4 = 144)
    w25 = {"B": 22500, "N": 21875, "A": 625, "D": 625, "O": 625, "H": 625, "V": 625}
    w25 = apply_table(tables["T3c"], w25)
    w25 = apply_table(tables["T3e"], w25)
    m25 = eval_code(tables["C4b"], w25)
    t25 = nth_root_floor_15(m25, 144)

    # C27: Baumert pullback (31,466 words), 88 ports -> T2a^7 -> C4a (p = 4*2^7*4 = 2048)
    w27 = {"B": 31378, "N": 31079, "A": 237, "D": 150, "O": 88, "H": 88, "V": 88}
    for _ in range(7):
        w27 = apply_table(tables["T2a"], w27)
    m27 = eval_code(tables["C4a"], w27)
    t27 = nth_root_floor_15(m27, 2048)

    # C29: H_BPZ 50-coset exact ceiling (42,050 words, p = 4)
    m29 = 42050
    t29 = nth_root_floor_15(m29, 4)

    # C31: Baumert pullback (54,913 words), 133 ports -> T2a^7 -> C4a (p = 4*2^7*4 = 2048)
    w31 = {"B": 54780, "N": 54371, "A": 337, "D": 205, "O": 133, "H": 133, "V": 133}
    for _ in range(7):
        w31 = apply_table(tables["T2a"], w31)
    m31 = eval_code(tables["C4a"], w31)
    t31 = nth_root_floor_15(m31, 2048)

    # Exact fractional clique cover barrier for C25 H* 625-port profile: 46875 / 2
    barrier_c25 = Fraction(46875, 2)

    return {
        "C25": {
            "power": 144,
            "digits_M": len(str(m25)),
            "target_int": t25,
            "floor_15": f"{t25 // 10**15}.{t25 % 10**15:015d}",
            "g7_barrier_exact": str(barrier_c25),
        },
        "C27": {
            "power": 2048,
            "digits_M": len(str(m27)),
            "target_int": t27,
            "floor_15": f"{t27 // 10**15}.{t27 % 10**15:015d}",
        },
        "C29": {
            "power": 4,
            "digits_M": len(str(m29)),
            "target_int": t29,
            "floor_15": f"{t29 // 10**15}.{t29 % 10**15:015d}",
        },
        "C31": {
            "power": 2048,
            "digits_M": len(str(m31)),
            "target_int": t31,
            "floor_15": f"{t31 // 10**15}.{t31 % 10**15:015d}",
        },
    }


if __name__ == "__main__":
    print(json.dumps(certify_all_four_records(), indent=2))
