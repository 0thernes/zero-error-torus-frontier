# Architecture (`zero-error-torus-frontier` v1.0.0)

## System Overview

The repository is organized as a **four-pillar mathematical proof stack** backed by **four independent verification languages** (Lean 4.35.0, Rust, ISO C11, Python) and a **reproducible AMS-LaTeX + GitHub Pages publishing pipeline**.

```
                   ┌──────────────────────────────────────────┐
                   │   Palomar Boundary (comparator.json)     │
                   │  PalomarChallenge.lean ↔ PalomarSolution │
                   │   6 Kernels: lean · leanchecker-paranoid │
                   │   lean4lean · nanoda · con-leche · con-ron│
                   └─────────────────────┬────────────────────┘
                                         │
                                  Solution.lean
                                         │
        ┌────────────────┬───────────────┴───────────────┬────────────────┐
        ▼                ▼                               ▼                ▼
  CosetQuotient    WorldRecords                 SeparationCalculus   HaemersParadox
  (T1a – T1f)      (T2a – T2d)                     (T3a – T3c)        (T4a – T4d)
  H_BPZ vs H*      Chunked 81-ball certs           G_7 C_5 core       SimpleField rank
  45 vs 49 ball    28-digit monotonic trunc.       T3b barrier        Z^8 Bessel handle
  Helical / H*     C25, C27, C29, C31              Hetero compose     Z[√5] M_5, G_27
  Baumert pull     15-decimal ULP floors           Pure-kernel tables 27 > 21 example
        └────────────────┴───────────────┬───────────────┴────────────────┘
                                         ▼
                                   GraphCore.lean
                        (FinGraph, strongProd, strongPow, cycDist)
```

## Proof-Kernel TCB Boundary
- **Zero external Lean dependencies:** Only Lean 4.35.0 `Init` is imported. Every `.lean` file begins with `module`.
- **Anti-tamper separation:** `Challenge.lean` defines abstract statement types (`T1aStmt`..`AllFrontierTheoremsStmt`); `PalomarChallenge.lean` (38 lines) states the 18 target signatures with `sorry`; `PalomarSolution.lean` (zero `sorry`) discharges all 18 targets from `Solution.lean`. `lake comparator --config comparator.json --paranoid` confirms exact definitional type matching and replays every proof term through all six kernels.
- **Anti-vacuity & negative testing:** `NonVacuity.lean` (7 theorems) and `AdversarialTests.lean` (7 theorems) guarantee hypotheses are satisfiable and invalid inputs fail.

## Independent Differential Engines
1. **Rust (`rust/src/main.rs`):** Zero external crates; cross-checks all witness packings, quotient ball sizes, Baumert counts, $G_7$, $\mathbb{Z}[\sqrt{5}]$ idempotence, and Schläfli $\mathbb{Z}^8/\mathbb{F}_2$ certificates; outputs deterministic JSON (`--verify-all`).
2. **ISO C11 (`native/`):** Strict `-std=c11 -Wall -Wextra -Wpedantic -Werror` static library + CLI + negative unit tests + deterministic 25,000-iteration PRNG fuzz harness under ASan+UBSan.
3. **Python (`python/`, `reference/`):** Exact integer & 80-digit `Decimal`/`Fraction` oracle parsing `SeparationCalculus.lean` directly to eliminate table drift, tested via `pytest`, `Hypothesis` property tests, metamorphic translation tests, cross-language differential checks, and deterministic mutation-kill checks.
4. **Publication & Blueprint (`paper/`, `dist/`, `docs/site/`):** Deterministic matplotlib vector PDF figures, Tectonic AMS-LaTeX manuscript, clean-room arXiv tarball, and zero-CDN interactive GitHub Pages explorer.
