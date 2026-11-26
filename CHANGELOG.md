# Changelog

All notable changes to `zero-error-torus-frontier` are documented in this file.
Format follows [Keep a Changelog 1.1.0](https://keepachangelog.com/en/1.1.0/) and Semantic Versioning 2.0.0.

## [1.0.0] - 2026-11-25

### Added
- **Zero-Mathlib Lean 4.35.0 Formalization (`lean/`):**
  - `GraphCore.lean`: finite graphs, strong products $G \boxtimes H$, strong powers $G^{\boxtimes d}$, cycle graphs $C_n$, independence sets, and exact integer power-lifting witnesses.
  - `CosetQuotient.lean`: Theorems T1a–T1f — $H_{\mathrm{BPZ}}$ (49-ball) and $H^*$ (45-ball) algebraic coset-quotient compression, exact double-counting ceilings, Intra-Coset Obstruction Theorem, infinite $H_{\mathrm{BPZ}}$ helical staircase ($n=4m+1, m \equiv 0,1 \pmod 4$), infinite $H^*$ staircase ($n=8k+1, k \ge 3$) with automatic $n^2$-port systems for all $n=16j+9$, and the 5-line Baumert Pullback Homomorphism Theorem.
  - `SeparationCalculus.lean`: Theorems T3a–T3c — 7-letter separation graph $G_7$ induced-$C_5$ anatomy, exact $\Theta(G_7)=3$, weighted fractional-clique-cover barrier $\alpha_w(G_7^{\boxtimes k}) \le \bar{\chi}_f(G_7,w)^k$, General Multi-Alphabet Two-Sided Heterogeneous Composition Theorem (resolving Tandon `arXiv:2608.30273` Open Problem #2), and pure-kernel (zero `native_decide`) admissibility verification of `T2a`, `T3c`, `T3e`, `C4a`, `C4b`.
  - `WorldRecords.lean`: Theorems T2a–T2d — pure-kernel zero-`native_decide` certificates establishing four consecutive new odd-cycle Shannon capacity lower bounds: $\Theta(C_{25}) \ge 12.344196091426840$, $\Theta(C_{27}) \ge 13.319390984674516$, $\Theta(C_{29}) \ge 14.319949949077992$, and $\Theta(C_{31}) \ge 15.308776193986503$.
  - `HaemersParadox.lean`: Theorems T4a–T4d — General Haemers Rank Theorem over any `SimpleField F`, Exact Integer Orthogonal-Handle Sandwich Theorem, Lovász's Pentagon Theorem ($\Theta(C_5)=\sqrt{5}$ via $\mathbb{Z}[\sqrt{5}]$ idempotent $M_5^2 = 5(\sqrt{5}-1)M_5$), and the first zero-Mathlib 6-kernel proof of Haemers's 1979 Schläfli super-multiplicativity paradox ($\alpha(G_{27}^{\boxtimes d}) \le 3^d$, $\alpha(\overline{G_{27}}^{\boxtimes d}) \le 7^d$, $\alpha(G_{27} \boxtimes \overline{G_{27}}) \ge 27 > 21$).
  - `NonVacuity.lean`, `AdversarialTests.lean`, `Challenge.lean`, `Solution.lean`, `PalomarChallenge.lean`, `PalomarSolution.lean`, `VerifyAxioms.lean`, `comparator.json`, `formalization.yaml`.
- **Multi-Language Engines (`rust/`, `native/`, `python/`, `reference/`, `tests/`):**
  - Stdlib-only Rust engine (`rust/`) for torus coset packing, $H^*$ port synthesis, Baumert pullback port extraction, 7-letter optimization, and Schläfli verification.
  - Zero-warning ISO C11 independent verifier + standalone fuzz harness + ASan/UBSan target (`native/`).
  - Exact 80-digit Python oracle (`reference/capacity_oracle.py`), full verification suite, 5 publication vector PDF figures, Hypothesis property tests, differential tests across Lean/Rust/C11/Python, metamorphic tests, golden snapshots, and 100%-kill mutation tests.
- **Publication & Interactive Dissemination (`paper/`, `dist/`, `docs/site/`):**
  - Publication-grade AMS-LaTeX preprint compiled via Tectonic (0 warnings, 0 overfull hboxes), frozen `dist/Donahue_2026_zero_error_torus_frontier.pdf`, and clean-room verified `dist/arxiv_submission.tar.gz`.
  - Interactive WCAG 2.2 AA GitHub Pages proof blueprint DAG and live torus/separation-graph explorer (`docs/site/`).
  - Three complete hardening cycles documented in `HARDENING_LOG.md` and `docs/reviews/`.
