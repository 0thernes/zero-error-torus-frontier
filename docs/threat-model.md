# Threat Model (`zero-error-torus-frontier` v1.0.0)

## Scope
This repository is a static formal-proof and deterministic computational-verification project with **no network servers, no user authentication, no database, and no untrusted code execution**. The primary security and integrity assets are:
1. **Mathematical soundness** of the formal Lean 4.35.0 proofs (`lean/`).
2. **Numerical & combinatorial integrity** of witness certificates (`data/witnesses.json`, `rust/`, `native/`, `python/`, `reference/`).
3. **Supply-chain & archival integrity** of the frozen manuscript PDF, arXiv tarball, and GitHub Release artifacts (`dist/`, `MANIFEST.sha256`).

## Threat Matrix & Mitigations

| Threat ID | Attack / Failure Vector | Impact | Control / Mitigation |
|---|---|---|---|
| **T-01** | Unproved `sorry` / `admit` or hidden custom `axiom` slips into Lean proofs | False theorem claimed proved | `VerifyAxioms.lean` asserts exact 32-declaration allowlist `⊆ {propext, Classical.choice, Quot.sound}`; `scripts/check_readme_axioms.py` scans all `.lean` files; CI fails on any discrepancy. |
| **T-02** | Lean compiler bug via `native_decide` (`Lean.ofReduceBool`) | Unsound proof bypassing kernel | Zero `native_decide` across the entire repo (enforced by static scanner and axiom allowlist). |
| **T-03** | Single proof-kernel implementation bug | Soundness escape | Every Palomar target replayed across **six independent kernels** (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) via `lake check --paranoid` and `lake comparator --paranoid`. |
| **T-04** | Statement-vacuity or definition mismatch (proving a trivially true statement) | Misleading claim | `Challenge.lean` / `PalomarChallenge.lean` human-auditable target signatures, `NonVacuity.lean` (7 witness theorems), `AdversarialTests.lean` (7 negative theorems), and `docs/statement-fidelity.md`. |
| **T-05** | Drift between Lean numbers, README, CLAIMS, witnesses.json, and LaTeX PDF | Inconsistent publication | `scripts/check_readme_axioms.py` enforces exact 15-decimal string parity across all four files; `reference/capacity_oracle.py` parses Lean tables directly. |
| **T-06** | Memory corruption or UB in ISO C11 verifier (`native/`) | Crash or wrong output | Compiled with `-std=c11 -Wall -Wextra -Wpedantic -Werror`, verified under ASan + UBSan (`make sanitize`), and exercised by a 25,000-iteration PRNG fuzz harness (`make fuzz`). |
| **T-07** | Fabricated or broken scholarly citations | Academic integrity breach | `scripts/check_citations.py --live` resolves every DOI / arXiv ID over HTTP (20/20 verified). |
| **T-08** | Post-release artifact tampering | Corrupted archive | `MANIFEST.sha256`, `data/MANIFEST.sha256`, GitHub Release SLSA build provenance attestation, Software Heritage snapshot, and pinned submodule in `0thernes-research-archive` (`0TH-2026-016`). |
