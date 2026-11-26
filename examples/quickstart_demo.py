# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Quickstart smoke demo verifying all 4 pillars and exact capacity records."""

from __future__ import annotations

import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "python"))
sys.path.insert(0, str(ROOT / "reference"))

from capacity_oracle import certify_all_four_records
from torus_frontier import verify_all_pillars


def main() -> None:
    pillars = verify_all_pillars(ROOT / "data" / "witnesses.json")
    records = certify_all_four_records()
    print("=== Pillar 1-4 Structural Audit ===")
    print(json.dumps(pillars, indent=2, sort_keys=True))
    print("\n=== Exact Arbitrary-Precision Integer Capacity Records ===")
    print(json.dumps(records, indent=2, sort_keys=True))
    assert pillars["all_ok"], "Structural audit failed"
    assert records["C25"]["target_int"] == 12344196091426841
    assert records["C27"]["target_int"] == 13319390984674515
    assert records["C29"]["target_int"] == 14319949949077991
    assert records["C31"]["target_int"] == 15308776193986504
    print("\nALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
