# Zero-Error Torus Frontier (`0TH-2026-014`)

[![CI](https://github.com/0thernes/zero-error-torus-frontier/actions/workflows/ci.yml/badge.svg)](https://github.com/0thernes/zero-error-torus-frontier/actions/workflows/ci.yml)
[![Pages](https://github.com/0thernes/zero-error-torus-frontier/actions/workflows/pages.yml/badge.svg)](https://0thernes.github.io/zero-error-torus-frontier/)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0%20zero--Mathlib-2563eb.svg)](lean/lean-toolchain)
[![6 Proof Kernels](https://img.shields.io/badge/kernels-6%20independent%20(paranoid)-059669.svg)](lean/formalization.yaml)
[![License: Apache-2.0 / CC-BY-4.0](https://img.shields.io/badge/License-Apache--2.0%20%2F%20CC--BY--4.0-0ea5e9.svg)](LICENSE)

Zero-Mathlib Lean 4.35.0 formalization and multi-language verification suite establishing coset-quotient compression, four new odd-cycle Shannon capacity world records ($C_{25}, C_{27}, C_{29}, C_{31}$), separation-graph barriers, and Haemers's 1979 Schläfli paradox across six independent proof kernels.

![Zero-Error Torus Frontier Social Preview](docs/media/social-preview.svg)

- **Interactive Explorer & Proof Blueprint DAG:** <https://0thernes.github.io/zero-error-torus-frontier/> ([Blueprint](https://0thernes.github.io/zero-error-torus-frontier/blueprint.html))
- **Frozen AMS-LaTeX Monograph:** [`dist/Donahue_2026_zero_error_torus_frontier.pdf`](dist/Donahue_2026_zero_error_torus_frontier.pdf)
- **Author:** Alexander Stephen Donahue · Independent Researcher, Spokane, WA, USA · ORCID [`0009-0006-8168-9648`](https://orcid.org/0009-0006-8168-9648)
- **Maintenance status:** Active (`v1.0.0` — frozen proof & manuscript archive; errata and extensions tracked via GitHub Issues).

---

## Headline Machine-Verified Results

Every theorem below is proved in standalone zero-Mathlib Lean 4.35.0 (`lean/`), with **zero `sorry`**, **zero `admit`**, **zero `native_decide`**, **zero custom axioms** (strictly `⊆ {propext, Classical.choice, Quot.sound}` across all 32 audited declarations), and replayed across **six independent proof kernels** (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron` via `lake comparator --paranoid`).

### Four New World Records Surpassing 1971–1973 Baumert–Hales Bounds

| Odd Cycle | Baumert–Hales (1971–73) | Our $d=4$ Base | Certified 15-Decimal Floor | Net Gain | Lovász $\vartheta(C_n)$ | Lean Theorem |
|---|---:|---:|---:|---:|---:|---|
| **$C_{25}$** | `12.3310604178` | `12.3316288890` | **`12.344196091426841`** | `+0.013135674` | `12.450522` | `t2a_c25_world_record` ($p=144$, $H^*$ 625 ports) |
| **$C_{27}$** | `13.3176204000` | `13.3186554683` | **`13.319390984674515`** | `+0.001770585` | `13.454185` | `t2b_c27_world_record` ($p=2048$, 88 ports) |
| **$C_{29}$** | `14.3045513000` | `14.3199499491` | **`14.319949949077991`** | `+0.015398649` | `14.457351` | `t2c_c29_world_record` ($p=4$, 50-coset ceiling) |
| **$C_{31}$** | `15.2906289000` | `15.3080119532` | **`15.308776193986504`** | `+0.018147294` | `15.460110` | `t2d_c31_world_record` ($p=2048$, 133 ports) |

### All Four Pillars (`T1a`–`T4d`, 18 Palomar Targets)

1. **Pillar I — Algebraic Coset-Quotient Compression & Infinite Families (`CosetQuotient.lean`):**
   - `T1a`–`T1b`: $n^2$-to-1 compression for $H_{\mathrm{BPZ}} = \langle(1,0,0,2),(0,1,2,0)\rangle$ and our newly discovered $H^* = \langle(1,0,0,2),(0,1,0,4)\rangle$ with exact double-counting ceilings.
   - `T1c`: Intra-coset privacy obstruction on $H_{\mathrm{BPZ}}$ vs. unconditional unit-shift privacy on $H^*$ with strictly smaller forbidden ball $45 < 49$ ($n \ge 15$).
   - `T1d`–`T1e`: Two infinite exact-ceiling code families ($C_{4m+1}$ helical $H_{\mathrm{BPZ}}$; $C_{8k+1}$ staircase $H^*$ yielding automatic $n^2$-port `RichPortSystem`s for every odd $k \ge 3$: $C_{25}, C_{41}, C_{57}, \dots$).
   - `T1f`: Baumert locally-injective pullback homomorphism $C_{p+2}^{\boxtimes d} \to C_p^{\boxtimes d}$ ($p \ge 5$) with exact factored cardinality.
2. **Pillar II — Four Certified World Records (`WorldRecords.lean`):**
   - `T2a`–`T2d`: Chunked 81-ball certificates + 28-digit monotonic fixed-point truncation certifying all four records above to the final ULP without `native_decide`.
3. **Pillar III — Separation-Graph Anatomy, Barriers & Heterogeneous Composition (`SeparationCalculus.lean`):**
   - `T3a`: Hidden induced chordless $C_5$ (`B-A-V-H-D`) inside $G_7$ and exact unweighted capacity $\Theta(G_7) = \alpha(G_7) = \bar{\chi}(G_7) = 3$.
   - `T3b`: Exact weighted fractional-clique-cover barrier proving the sharp $46875/2$ ($12.373080$) ceiling for $C_{25}$'s 625-port system.
   - `T3c`: General multi-alphabet two-sided heterogeneous composition (resolving Tandon `arXiv:2608.30273` Open Problem #2) + pure-kernel admissibility of `T2a`, `T3c`, `T3e`, `C4a`, `C4b`.
4. **Pillar IV — Zero-Mathlib Upper Bounds & Haemers's 1979 Schläfli Paradox (`HaemersParadox.lean`):**
   - `T4a`–`T4b`: General Haemers matrix-rank bound over any `SimpleField` + exact integer orthogonal-handle sandwich theorem (zero floating-point or real analysis).
   - `T4c`: Exact Lovász pentagon theorem $\Theta(C_5) = \sqrt{5}$ via the $\mathbb{Z}[\sqrt{5}]$ Gram idempotent $M_5^2 = 5(\sqrt{5}-1)M_5$.
   - `T4d`: First zero-Mathlib, six-kernel proof of Haemers's 1979 Schläfli paradox: $\Theta(G_{27}) \le 3$ ($\mathbb{Z}^8$ handle), $\Theta(\overline{G_{27}}) \le 7$ ($27 \times 7$ $\mathbb{F}_2$ factorization), and $\Theta(G_{27} \boxtimes \overline{G_{27}}) \ge 27 > 21$.

---

## Quickstart (Verified from Clean Clone)

### 1. Zero-Mathlib Lean 4.35.0 Formal Verification (~30 seconds)
```bash
cd lean
lake build
lake env lean VerifyAxioms.lean
lake env leanchecker --fresh Solution
lake env leanchecker-paranoid --fresh Solution
# On Linux with bubblewrap (runs all 6 independent proof kernels):
lake check --paranoid
lake comparator --config comparator.json --paranoid
```

### 2. Independent Multi-Language Differential Verifiers
```bash
# Stdlib-only Rust verifier (zero external crates)
cd rust && cargo test --release && cargo run --release -- --verify-all

# Strict ISO C11 verifier (-std=c11 -Wall -Wextra -Wpedantic -Werror + ASan/UBSan + fuzz)
cd native && make test && make sanitize && make fuzz

# Exact 80-digit Python oracle, pytest, Hypothesis property tests & anti-drift audit
python examples/quickstart_demo.py
pytest -v tests/test_all.py
python scripts/check_readme_axioms.py
python scripts/check_citations.py
```

## Usage Examples

### Verify all four pillars and print exact 15-decimal floors (Python)
```python
from pathlib import Path
from torus_frontier import verify_all_pillars, hstar_family, baumert_factored_card, Q25_HBPZ

report = verify_all_pillars(Path("data/witnesses.json"))
assert report["all_ok"] is True
assert report["ball_hstar_25"] == 45 and report["ball_hbpz_25"] == 49
assert baumert_factored_card(25, Q25_HBPZ) == 31466
n, qstar_25 = hstar_family(3)  # C_25 exact 37-coset H* staircase
```

### Run the standalone zero-dependency Rust or ISO C11 CLI verifiers
```bash
./rust/target/release/zero-error-torus-frontier --verify-all
./native/build/torus_cli --verify-all
just reproduce
```

---

## Epistemic Boundaries & Explicitly Open Problems

See [`CLAIMS.md`](CLAIMS.md) and [`LIMITATIONS.md`](LIMITATIONS.md) for the complete epistemic ledger. In particular:
- Determining the **exact** Shannon capacity $\Theta(C_n)$ for any odd $n \ge 7$ (including $C_7, C_{25}, C_{27}, C_{29}, C_{31}$; Mega-Atlas `CS-049`) remains **explicitly open** and is **not** claimed solved here.
- Claim `C-EX1` (exhaustive $n^4$ 2D subgroup scan for $n \in \{19,21,23,25\}$ showing minimum ball size $45$) is tagged `[EXACT-COMP]`, distinct from the universally proved `[LEAN-6K]` theorems.

---

## Repository Layout & Documentation

- `lean/` — Zero-Mathlib Lean 4.35.0 library (`GraphCore`, `CosetQuotient`, `SeparationCalculus`, `WorldRecords`, `HaemersParadox`, `NonVacuity`, `AdversarialTests`, `Challenge`, `Solution`, `PalomarChallenge`, `PalomarSolution`, `VerifyAxioms`).
- `rust/`, `native/`, `python/`, `reference/` — Independent Rust, ISO C11, and 80-digit Python differential verification engines.
- `paper/` & `dist/` — AMS-LaTeX source, 5 vector PDF figures, frozen PDF monograph, and clean-room verified `arxiv_submission.tar.gz`.
- `docs/` — [Architecture](docs/architecture.md), [Statement Fidelity](docs/statement-fidelity.md), [Threat Model](docs/threat-model.md), [Operations](docs/operations.md), [FAQ](docs/faq.md), [Glossary](docs/glossary.md), [10-Pass Review](docs/10-pass-review.md), [Red-Team Review](docs/reviews/adversarial-red-team-review.md), [ADRs](docs/adr/), and [GitHub Pages site](docs/site/).
- `HARDENING_LOG.md`, `MANIFEST.sha256`, `REPLICATION.md`, `CITATION.cff`, `llms.txt`.

## License

Dual-licensed: all source code is licensed under [Apache-2.0](LICENSE); all prose, paper text, documentation, and figures are licensed under [CC-BY-4.0](LICENSE-DOCS) (machine-declared in [`REUSE.toml`](REUSE.toml)).
