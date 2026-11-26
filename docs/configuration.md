# Configuration Reference (`zero-error-torus-frontier` v1.0.0)

This repository requires **no secrets, API keys, or runtime environment variables**. All configuration is declarative and committed in version control:

| File | Purpose | Key Settings |
|---|---|---|
| `lean/lean-toolchain` | Pinned Lean 4 compiler version | `leanprover/lean4:v4.35.0` |
| `lean/lakefile.toml` | Zero-dependency Lake build manifest | 16 default targets; `PalomarChallenge` excluded from `defaultTargets` |
| `lean/comparator.json` | Palomar 6-kernel comparator target spec | 18 targets (`prove_t1a`..`prove_all_frontier_theorems`), `permitted_axioms: ["propext", "Quot.sound", "Classical.choice"]` |
| `lean/formalization.yaml` | Machine-readable formalization metadata | Archive ID `0TH-2026-014`, 6 kernels, zero Mathlib |
| `rust/Cargo.toml` | Zero-dependency Rust verifier config | Edition 2021, zero `[dependencies]` |
| `native/Makefile` | Strict ISO C11 build & sanitizer targets | `-std=c11 -O2 -Wall -Wextra -Wpedantic -Werror`, `test`, `sanitize`, `fuzz` |
| `pyproject.toml` | Python package, pytest, ruff, mypy config | Python `>=3.10`, strict ruff & mypy settings |
| `requirements.lock.txt` | Pinned reproducible Python test/plot versions | `pytest`, `hypothesis`, `matplotlib`, `numpy`, `ruff`, `mypy` |
| `REUSE.toml` | SPDX license annotations | `Apache-2.0` (code), `CC-BY-4.0` (docs/paper) |
| `repo.yaml` | Build Standard v1.2.0 metadata & audit overrides | Author, URLs, manual audit justifications |
| `justfile` | Unified local command runner | `lean`, `rust`, `c11`, `python`, `paper`, `audit`, `all` |
