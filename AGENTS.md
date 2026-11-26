# AGENTS.md — Zero-Error Torus Frontier

Canonical agent instructions for `0thernes/zero-error-torus-frontier` (`v1.0.0`).
See also [docs/build-standard.md](docs/build-standard.md), [CLAIMS.md](CLAIMS.md), [LIMITATIONS.md](LIMITATIONS.md), and [REPLICATION.md](REPLICATION.md).

## Project Summary

**Zero-Error Torus Frontier** is a zero-Mathlib Lean 4.35.0 formalization, multi-language verification suite (Rust + C11 + Python), and AMS-LaTeX white paper on lower and upper bounds for the zero-error Shannon capacity of odd cycles and strong-product graphs. Shannon capacity $\Theta$ is not defined in Lean; each capacity bound below follows, outside Lean, from a kernel-checked integer statement about independent sets in a strong power. No published open question is resolved (see [ERRATA.md](ERRATA.md)).

1. **Pillar 1 (Coset-Quotient Lifting and Two Families):**
   - For $n \ge 9$ (resp. $n \ge 15$), an independent set of size $M$ in the quotient graph for $H_{\mathrm{BPZ}} = \langle(1,0,0,2),(0,1,2,0)\rangle$ (49-ball) (resp. $H^* = \langle(1,0,0,2),(0,1,0,4)\rangle$, 45-ball) lifts to $M n^2$ points of $C_n^{\boxtimes 4}$. We did not find $H^*$ in the literature we read; this was not a systematic search.
   - Double-counting upper bounds $\lfloor n \lfloor n/4 \rfloor / 4 \rfloor$ and $\lfloor n \lfloor n/8 \rfloor / 2 \rfloor$ on these quotient graphs. These bound unions of cosets of one fixed subgroup, not $\alpha(C_n^{\boxtimes 4})$.
   - `T1c`: for $n \ge 9$, every $H_{\mathrm{BPZ}}$ shift with $e_3 - 2e_0 = \pm 1$ conflicts with another point of its own coset; for $n \ge 15$ the $H^*$ shift $(0,0,\pm 1,0)$ is private; quotient ball sizes 45 versus 49 evaluated at $n = 19, 21, 23, 25$.
   - `T1d`–`T1e`: two families of coset-union codes that meet the quotient ceiling, $n = 4m+1$ ($m \ge 5$, $m \equiv 0,1 \pmod 4$, $H_{\mathrm{BPZ}}$) and $n = 8k+1$ ($k \ge 3$, $H^*$). All `T1e` sizes equal published bounds (Codenotti–Gerace–Resta 2003, Theorem 1, for odd $k$; Baumert et al. 1971 for even $k$). The $n^2$-port `RichPortSystem` for odd $k$ is the separate declaration `WorldRecords.hstarOddRichPortSystem`, outside the 18-target contract.
   - `T1f`: the Baumert et al. (1971) expansion map $C_{p+2}^{\boxtimes d} \to C_p^{\boxtimes d}$ ($p \ge 5$) pulls independent sets back to independent sets. The cardinality formula is proved separately (`baumertExpandList_len`, `baumertExpandList_nodup_and_indep`), outside the contract.
2. **Pillar 2 (Four Kernel-Checked Lower Bounds — Zero `native_decide`):** compared with the largest published values we found, the $d=4$ entries of Codenotti, Gerace and Resta, Ars Combinatoria 66 (2003), Table 1.
   - $\Theta(C_{25}) \ge 12.344196091426841$ (37-coset $H^*$ + 625-port system, `T3c -> T3e -> C4b`, $p = 144$); $+0.012567519$ over $23125^{1/4}$. The base size 23125 equals the published value.
   - $\Theta(C_{27}) \ge 13.319390984674515$ (Baumert expansion of $Q_{25}$, $31{,}466$ words + 88 ports); **below** $31522^{1/4} = 13.324577316143$ ($-0.005186$); not best known.
   - $\Theta(C_{29}) \ge 14.319949949077991$ (50-coset $H_{\mathrm{BPZ}}$ code meeting the quotient ceiling, $42{,}050$ words, $p = 4$); $+0.002810330$ over $42017^{1/4}$.
   - $\Theta(C_{31}) \ge 15.308776193986504$ (Baumert expansion of $Q_{29}$, $54{,}913$ words + 133 ports); **below** $54934^{1/4} = 15.309475277725$ ($-0.000699$); not best known.
   - The Lean names `t2b_c27_world_record` and `t2d_c31_world_record` are historical and kept in `v1.0.0` because renaming would change the comparator contract.
3. **Pillar 3 (Separation Calculus):**
   - For the 7-vertex graph $G_7$: an induced 5-cycle (`B-A-V-H-D`), $\alpha(G_7) \ge 3$, and $\alpha(G_7^{\boxtimes d}) \le 3^d$ by a 3-clique cover (so $\Theta(G_7) = 3$, outside Lean).
   - Weighted fractional-clique-cover upper bound $\alpha_w(G_7^{\boxtimes k}) \le \bar{\chi}_f(G_7, w)^k$; optimality is not proved.
   - `T3c`: a two-alphabet, two-graph form of the BPZ combining rule (Tandon, `arXiv:2608.30273`, Proposition 1; Buys–Polak–Zuiddam, `Realisation.multiSubst`), plus pure-kernel (zero `native_decide`) admissibility of the five BPZ tables. It does not resolve any published open problem.
4. **Pillar 4 (Integer Forms of Known Upper Bounds):**
   - Haemers's (1979) matrix-rank bound over any `SimpleField F`.
   - Integer orthogonal-representation bound for vectors of equal squared norm $D$ (zero reals, zero SDP).
   - Lovász's (1979) pentagon bound in integer form: $\alpha(C_5^{\boxtimes 2}) \ge 5$ and $\alpha(C_5^{\boxtimes d})^2 \le 5^d$ via the $\mathbb{Z}[\sqrt{5}]$ idempotent $M_5^2 = 5(\sqrt{5}-1)M_5$; $\Theta(C_5) = \sqrt{5}$ follows outside Lean.
   - Haemers's 1979 Schläfli-graph example, zero-Mathlib and six-kernel-checked: 27 vectors in $\mathbb{Z}^8$ with entries in $\{-1,0,1,2\}$ and handle $h=(1,1,1,1,1,1,3,3)$ give $\alpha(G_{27}^{\boxtimes d}) \le 3^d$, a $27 \times 7$ $\mathbb{F}_2$ factorization gives $\alpha(\overline{G_{27}}^{\boxtimes d}) \le 7^d$, and a diagonal independent set gives $\alpha(G_{27} \boxtimes \overline{G_{27}}) \ge 27 > 21 = 3 \times 7$. No priority claim is made.

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
