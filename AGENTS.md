# AGENTS.md — Zero-Error Torus Frontier

Canonical agent instructions for `0thernes/zero-error-torus-frontier` (`v1.0.0`).
See also [docs/build-standard.md](docs/build-standard.md), [CLAIMS.md](CLAIMS.md), [LIMITATIONS.md](LIMITATIONS.md), and [REPLICATION.md](REPLICATION.md).

## Project Summary

**Zero-Error Torus Frontier** is a zero-Mathlib Lean 4.35.0 formalization, multi-language verification suite (Rust + C11 + Python), and AMS-LaTeX white paper advancing the zero-error Shannon capacity frontier of odd cycles and strong-product graphs:

1. **Pillar 1 (Algebraic Quotient-Torus Compression, Intra-Coset Obstruction & Infinite Families):**
   - Exact $n^2$-to-1 compression for both $H_{\mathrm{BPZ}} = \langle(1,0,0,2),(0,1,2,0)\rangle$ (49-ball) and the new 45-ball subgroup $H^* = \langle(1,0,0,2),(0,1,0,4)\rangle$.
   - Exact double-counting ceilings $\alpha((C_n^3)^{\boxtimes 2}) \le \lfloor n \lfloor n/4 \rfloor / 4 \rfloor$ and $\alpha(C_n \boxtimes C_n^7) \le \lfloor n \lfloor n/8 \rfloor / 2 \rfloor$.
   - **Intra-Coset Obstruction Theorem:** explains why $H_{\mathrm{BPZ}}$-coset codes forbid private ports on width-1 quotient gaps while $H^*$ admits unconditional intra-coset-private shifts $e = (0,0,\pm 1,0)$.
   - **Infinite Exact-Ceiling Families:** closed-form $H_{\mathrm{BPZ}}$ helical staircase for all $n = 4m+1$ ($m \equiv 0,1 \pmod 4$) and closed-form $H^*$ staircase for all $n = 8k+1$ ($k \ge 3$), automatically producing full $H^*$-invariant $n^2$-port `RichPortSystem`s for every $n = 16j+9$ ($C_{25}, C_{41}, C_{57}, \dots$).
   - **Baumert Pullback Homomorphism Theorem:** 5-line locally-injective homomorphism `pull^d : C_{p+2}^d -> C_p^d` with exact factored cardinality.
2. **Pillar 2 (Four Consecutive New Odd-Cycle Shannon Capacity Records — Zero `native_decide`):**
   - $\Theta(C_{25}) \ge 12.344196091426840$ (37-coset $H^*$ + 625-port system, `T3c -> T3e -> C4b`, $p = 144$, beating 55-year Baumert–Hales $12.3310604178$ by $+0.013135674$).
   - $\Theta(C_{27}) \ge 13.319390984674516$ (Baumert pullback of $Q_{25}$, $31{,}466$ words + 88 ports, beating Baumert–Hales $13.3176204000$).
   - $\Theta(C_{29}) \ge 14.319949949077992$ (50-coset $H_{\mathrm{BPZ}}$ exact ceiling, $42{,}050$ words, $p = 4$, beating Baumert–Hales $14.3045513000$ by $+0.015398649$).
   - $\Theta(C_{31}) \ge 15.308776193986503$ (Baumert pullback of $Q_{29}$, $54{,}913$ words + 133 ports, beating Baumert–Hales $15.2906289000$ by $+0.018147294$).
3. **Pillar 3 (7-Letter Separation Graph $G_7$ Anatomy, Fractional-Clique-Cover Barrier & Tandon Open Problem #2):**
   - Induced chordless $C_5$ (`B-A-V-H-D`) and exact unweighted capacity $\alpha(G_7) = \bar{\chi}(G_7) = \Theta(G_7) = 3$.
   - Exact weighted fractional-clique-cover upper barrier $\alpha_w(G_7^{\boxtimes k}) \le \bar{\chi}_f(G_7, w)^k$.
   - General Multi-Alphabet Two-Sided Heterogeneous Separation-System Composition Theorem resolving Tandon (`arXiv:2608.30273`) Open Problem #2, plus pure-kernel (zero `native_decide`) verification of substitution tables and terminal codes.
4. **Pillar 4 (First Zero-Mathlib 6-Kernel Proofs of Lovász's Pentagon Theorem & Haemers's 1979 Schläfli Paradox):**
   - General Haemers Rank Theorem over any `SimpleField F`.
   - Exact Integer Orthogonal-Handle Sandwich Theorem (zero reals, zero SDP).
   - Exact Lovász Pentagon Theorem $\Theta(C_5) = \sqrt{5}$ via the $\mathbb{Z}[\sqrt{5}]$ idempotent $M_5^2 = 5(\sqrt{5}-1)M_5$.
   - Exact Schläfli $G_{27}$ Paradox: 27 vectors in $\mathbb{Z}^8$ with entries in $\{-1,0,1,2\}$ and handle $h=(1,1,1,1,1,1,3,3)$ proving $\alpha(G_{27}^{\boxtimes d}) \le 3^d$, exact $27 \times 7$ $\mathbb{F}_2$ factorization proving $\alpha(\overline{G_{27}}^{\boxtimes d}) \le 7^d$, and diagonal independent set $\alpha(G_{27} \boxtimes \overline{G_{27}}) \ge 27 > 21 = 3 \times 7$.

## Non-Negotiable Standing Rules

- **Author Identity:** Alexander Stephen Donahue (`Alexander S. Donahue`), Independent Researcher, Spokane, WA, USA, ORCID `0009-0006-8168-9648`, `0_0@0thernes.art`. Never claim an unincorporated entity/LLC in copyright or affiliation fields.
- **Git & CI Hygiene:** Commit and push directly to `main`; no feature branches, no PRs, no commit/tag signing, no branch protection, no required status checks, no Dependabot/Renovate.
- **Lean 4.35.0 TCB:** Zero Mathlib, zero `sorry`, zero `admit`, zero `native_decide`, zero custom axioms; strict axiom allowlist `[propext, Classical.choice, Quot.sound]`; every `.lean` file begins with `module`; verified across all 6 independent proof kernels (`lean`, `leanchecker`, `leanchecker-paranoid`, `con-leche`, `con-ron`, `nanoda_bin` + `lake comparator --paranoid`).
- **PowerShell Safety:** Always use `-LiteralPath` on bracketed paths (e.g. `Z:\[Vibe Coded (AI)]\ANTIGRAVITY\zero-error-torus-frontier`).

## Verification Commands

```bash
# Lean 4.35.0 build & strict axiom check
cd lean && lake build && lake env lean VerifyAxioms.lean

# Rust engine build, clippy & tests
cd rust && cargo test --release && cargo clippy --all-targets -- -D warnings

# Native C11 zero-warning verifier & fuzz smoke
make -C native clean all test

# Python exact oracle, differential, property & mutation checks
PYTHONPATH=python pytest tests/test_all.py -v
python scripts/check_readme_axioms.py
python scripts/check_citations.py

# AMS-LaTeX manuscript build via Tectonic
cd paper && tectonic -X compile main.tex --outdir build --keep-logs --keep-intermediates
```
