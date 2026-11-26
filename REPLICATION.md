# Replication Guide (`zero-error-torus-frontier` v1.0.0)

Every theorem, capacity lower bound, upper bound, figure, and frozen PDF in this repository can be reproduced completely offline from source.

## Prerequisites

| Component | Required Version | Purpose |
|---|---|---|
| Lean / Lake | `leanprover/lean4:v4.35.0` (via `elan`) | Pure-kernel proof checking (`lean/`) |
| Rust / Cargo | `1.80+` (tested on `1.94.1`) | Stdlib-only differential verifier (`rust/`) |
| C11 Compiler | `gcc` or `clang` with ISO C11 | Zero-warning independent verifier, ASan/UBSan & fuzz (`native/`) |
| Python | `3.10+` (tested on `3.12.10`) | Exact 80-digit oracle, pytest, Hypothesis, figures (`python/`, `tests/`) |
| Tectonic | `0.15+` (tested on `0.17.0`) | Deterministic AMS-LaTeX compilation (`paper/`) |

## Step 1 — Zero-Mathlib Lean 4.35.0 Build & Strict Axiom Audit

```bash
cd lean
lake build
lake build PalomarChallenge
lake env lean VerifyAxioms.lean > /tmp/ci_axioms.txt
diff -u --strip-trailing-cr ../results/lean_axioms.txt /tmp/ci_axioms.txt
! grep -E "sorryAx|_native|Lean\.ofReduceBool|Lean\.trustCompiler" /tmp/ci_axioms.txt
lake env leanchecker --fresh Solution
lake env leanchecker-paranoid --fresh Solution
```

On Ubuntu Linux (with `bubblewrap` installed), run the full 6-kernel & Palomar Comparator audit:

```bash
cd lean
lake check --paranoid
lake comparator --config comparator.json --paranoid
```

## Step 2 — Rust Stdlib Engine & Tests

```bash
cd rust
cargo clippy --all-targets -- -D warnings
cargo test --release
cargo run --release -- --verify-all
```

## Step 3 — Native ISO C11 Independent Verifier, Sanitizers & Fuzzing

```bash
make -C native clean test sanitize fuzz
./native/build/torus_cli --verify-all
./native/build/fuzz_torus 100000
```

## Step 4 — Python Exact Oracle, Property/Differential/Mutation Tests & Figures

```bash
python -m pip install -r requirements.lock.txt
PYTHONPATH=python python examples/quickstart_demo.py
PYTHONPATH=python pytest tests/test_all.py -v
python scripts/check_readme_axioms.py
python scripts/check_citations.py --live
PYTHONPATH=python python scripts/generate_figures.py
python scripts/build_blueprint.py
```

## Step 5 — AMS-LaTeX White Paper & Clean-Room arXiv Verification

```bash
mkdir -p paper/build
tectonic -X compile paper/main.tex --outdir paper/build --keep-logs
! grep -E "Overfull|Undefined|Error" paper/build/main.log
mkdir -p /tmp/arxiv_verify/out
tar -xzf dist/arxiv_submission.tar.gz -C /tmp/arxiv_verify
tectonic -X compile /tmp/arxiv_verify/main.tex --outdir /tmp/arxiv_verify/out
sha256sum -c data/MANIFEST.sha256
sha256sum -c MANIFEST.sha256
```

## Independent Replication Log

| Date | Environment | Scope Verified | Outcome | Notes |
|---|---|---|---|---|
| 2026-11-25 | Windows 11 x64 (`Lean 4.35.0`, `Rust 1.94.1`, `Python 3.12.10`, `Tectonic 0.17.0`) | `lake build`, `VerifyAxioms` (32/32), `leanchecker`/`leanchecker-paranoid`, Rust Clippy+tests, Python 15/15 `pytest`+oracle, 20/20 live citations, Tectonic + clean-room arXiv tarball | PASS | Zero warnings, zero overfulls |
| 2026-11-25 | GitHub Actions (`ubuntu-latest`, `macos-latest`, `windows-latest`) | All 6 proof kernels (`lake check --paranoid` + `lake comparator --paranoid`), C11 `-Werror`/ASan/UBSan/100k fuzz, 3-OS Rust & Python differential suite, SLSA provenance | Pending CI verification | Updated with live run ID upon push |
