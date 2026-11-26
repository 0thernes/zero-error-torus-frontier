# Verification & Execution Run Log (`zero-error-torus-frontier` v1.0.0)

## Environment Summary
- **Lean 4:** `leanprover/lean4:v4.35.0` (zero external dependencies)
- **Rust:** `rustc 1.94.1` / `cargo 1.94.1` (zero external crates)
- **Python:** `Python 3.12.10` (`pytest 9.2.0`, `hypothesis 6.170.17`, `matplotlib 3.11.2`, `numpy 2.4.4`, `ruff 0.15.7`, `mypy 1.20.0`)
- **LaTeX:** `Tectonic 0.17.0`
- **CI (Ubuntu/macOS/Windows):** 6 independent proof kernels via `lake check --paranoid` + `lake comparator --config comparator.json --paranoid`; GCC ISO C11 `-Werror` + ASan/UBSan + fuzz harness.

## Local & CI Verification Milestones
1. **Lean 4.35.0 build (`lake build`, `lake build PalomarChallenge`):** 16/16 default targets + challenge interface compiled with exit code 0 (~30s cold build as originally recorded; 70.2 s in the 2026-11-26 audit rebuild; `WorldRecords.lean` ~20s, max kernel depth $\le 65$, zero `maxRecDepth` overrides).
2. **Axiom audit (`lake env lean VerifyAxioms.lean` -> `results/lean_axioms.txt`):** 32/32 audited declarations depend strictly on `⊆ {propext, Classical.choice, Quot.sound}`; zero `sorryAx`, zero `Lean.ofReduceBool`, zero `Lean.trustCompiler`.
3. **Standalone kernel checkers:** `lake env leanchecker --fresh Solution` (exit 0) and `lake env leanchecker-paranoid --fresh Solution` (exit 0).
4. **Rust differential verifier:** `cargo clippy --all-targets -- -D warnings` (0 warnings); `cargo test --release` (4/4 passed); `cargo run --release -- --verify-all` (`"all_ok":true`).
5. **Python exact oracle & test suite:** `pytest -v tests/test_all.py` (15/15 passed in 1.04s, including 400 Hypothesis property examples, metamorphic checks, Python↔Rust differential parity, 80-digit oracle verification, and deterministic mutation-kill checks); `ruff check` (0 issues); `mypy` (0 issues across 9 files).
6. **Live citation verification:** `python scripts/check_citations.py --live` — 20 bibliography entries parsed; the script can resolve at most 19, because `baumert1971combinatorial` has no DOI, arXiv id or URL (two guessed DOIs caught and corrected via Crossref API before freeze). The earlier entry "20/20 resolved" was wrong (corrected 2026-11-26).
7. **Manuscript & visual QA:** All 5 Okabe-Ito vector PDF/PNG figures visually inspected and refined until zero clipping/overlap; Tectonic compiled `paper/main.tex` to 13-page AMS-LaTeX PDF (`dist/Donahue_2026_zero_error_torus_frontier.pdf`) and clean-room `dist/arxiv_submission.tar.gz` verified.
