# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Anti-drift verification script auditing Lean axioms, sorry/native_decide bans, and number parity."""

from __future__ import annotations

import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_AXIOMS = {"sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"}

EXPECTED_RECORDS = {
    "C25": "12.344196091426841",
    "C27": "13.319390984674515",
    "C29": "14.319949949077991",
    "C31": "15.308776193986504",
}


def _strip_lean_comments(text: str) -> str:
    # Remove nested/block comments /- ... -/ and line comments -- ...
    no_block = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return re.sub(r"--[^\n]*", "", no_block)


def check_lean_sources() -> None:
    lean_dir = ROOT / "lean"
    for p in sorted(lean_dir.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        text = p.read_text(encoding="utf-8")
        first_line = text.splitlines()[0].strip() if text.splitlines() else ""
        assert first_line == "module", f"{p} missing `module` header on line 1"
        code = _strip_lean_comments(text)
        assert "native_decide" not in code, f"Forbidden native_decide found in {p}"
        assert not re.search(r"^\s*axiom\s+", code, re.MULTILINE), f"Custom axiom declared in {p}"
        if p.name != "PalomarChallenge.lean":
            assert not re.search(r"\bsorry\b", code), f"Forbidden sorry found in {p}"
            assert not re.search(r"\badmit\b", code), f"Forbidden admit found in {p}"
    pc = lean_dir / "PalomarChallenge.lean"
    pc_lines = len(pc.read_text(encoding="utf-8").splitlines())
    pc_bytes = pc.stat().st_size
    assert pc_lines <= 1000, f"PalomarChallenge.lean has {pc_lines} > 1000 lines"
    assert pc_bytes <= 102400, f"PalomarChallenge.lean is {pc_bytes} > 100 KiB"


def check_axiom_dump() -> None:
    ax_file = ROOT / "results" / "lean_axioms.txt"
    assert ax_file.exists(), "Missing results/lean_axioms.txt"
    text = ax_file.read_text(encoding="utf-8")
    # Rejoin multi-line axiom lists
    normalized = re.sub(r",\s*\n\s*", ", ", text)
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]", normalized)
    no_ax = re.findall(r"'([^']+)' does not depend on any axioms", normalized)
    total = len(entries) + len(no_ax)
    assert total == 32, f"Expected 32 audited declarations, found {total}"
    for name, raw in entries:
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        bad = axioms - ALLOWED_AXIOMS
        assert not bad, f"{name} uses disallowed axioms: {bad}"
        assert not (axioms & FORBIDDEN_AXIOMS), f"{name} uses forbidden axioms"


def check_identity_and_numbers() -> None:
    # Ensure ZERO stray '0thernes LLC' references in repo artifacts
    for rel in ("LICENSE", "CITATION.cff", "README.md", "CLAIMS.md", "lean/formalization.yaml"):
        p = ROOT / rel
        if p.exists():
            txt = p.read_text(encoding="utf-8")
            assert "0thernes LLC" not in txt, f"Disallowed affiliation '0thernes LLC' in {rel}"

    # Verify exact 15-decimal record parity across witnesses.json, CLAIMS.md, README.md, paper/main.tex
    w = json.loads((ROOT / "data" / "witnesses.json").read_text(encoding="utf-8"))
    for k, expected in EXPECTED_RECORDS.items():
        assert w["records"][k]["certified_15dec_floor"] == expected, f"witnesses.json mismatch for {k}"

    for rel in ("CLAIMS.md", "README.md", "paper/main.tex"):
        p = ROOT / rel
        if p.exists():
            txt = p.read_text(encoding="utf-8")
            for k, expected in EXPECTED_RECORDS.items():
                assert expected in txt, f"Missing exact 15-decimal floor {expected} ({k}) in {rel}"


def main() -> None:
    check_lean_sources()
    check_axiom_dump()
    check_identity_and_numbers()
    print("AXIOM, SOURCE, IDENTITY & RECORD-PARITY AUDIT: ALL PASSED (32/32 declarations)")


if __name__ == "__main__":
    main()
