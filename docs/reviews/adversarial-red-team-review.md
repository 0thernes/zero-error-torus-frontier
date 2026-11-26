# Adversarial Red-Team Review (`zero-error-torus-frontier` v1.0.0)

This adversarial review actively attempted to falsify, break, or find epistemic overclaims across every layer of `zero-error-torus-frontier` (`0TH-2026-016`).

## Attack Vectors Tested & Verdicts

### 1. Could any Lean theorem hide a vacuous definition or unsound axiom?
- **Attack:** Inspect `GraphCore.lean` definitions of `cycleGraph`, `strongProd`, `strongPow`, `HasIndepSetOfSize`, `AlphaLe`, and audit `#print axioms` across all 32 exported declarations.
- **Finding:** Definitions match standard graph-theoretic strong products verbatim; `NonVacuity.lean` instantiates every quantifier with concrete graphs and `AdversarialTests.lean` proves invalid packings are rejected; all 32 declarations depend strictly on `⊆ {propext, Classical.choice, Quot.sound}` with zero `sorryAx` and zero `Lean.ofReduceBool`.
- **Verdict:** **DISCHARGED.**

### 2. Could the 15-decimal floors for $C_{25}, C_{27}, C_{29}, C_{31}$ be rounded up by 1 ULP?
- **Attack:** Increment each certified 15-decimal integer target by `+1` and evaluate exact $p$-th powers in `reference/capacity_oracle.py` and `tests/test_all.py::test_mutation_kill_planted_faults`.
- **Finding:** During Cycle 1 hardening, `CLAIMS.md` had 1-ULP discrepancies vs. `WorldRecords.lean` (`...840` vs `...841`, `...516` vs `...515`, `...992` vs `...991`, `...503` vs `...504`). Fixed immediately and locked behind `scripts/check_readme_axioms.py`. Lean proves $t^p \le M \cdot (10^{15})^p$ only; the upper side $M \cdot (10^{15})^p < (t+1)^p$ is a computation outside Lean, and `tests/test_all.py` asserts it for $C_{29}$ only. The 2026-11-26 statement audit confirmed it independently for $C_{29}$ only. `AGENTS.md` and `llms-full.txt` still print the old digits (see `ERRATA.md`).
- **Verdict:** **CAUGHT & FIXED.**

### 3. Could the Rust/C11 verifiers silently diverge from Lean's mathematical definitions?
- **Attack:** Cross-check `hstar_family`, `M_5`, and Schläfli witnesses line-by-line against `CosetQuotient.lean` and `HaemersParadox.lean`.
- **Finding:** Caught two genuine implementation bugs early: (a) Rust/C11 initially used a linear slope for $H^*$ odd-$k$ instead of the 4-jump staircase; (b) Lovász $M_5$ initially omitted the $-2$ ($-J$) non-edge term. Both were fixed, regression-tested (`test_regression_hstar_four_jump_staircase_and_lovasz_j_term`), and verified identical across Lean, Rust, C11, and Python.
- **Verdict:** **CAUGHT & FIXED.**

### 4. Could the Python oracle drift from `SeparationCalculus.lean`?
- **Attack:** Check how `reference/capacity_oracle.py` loads `T2a, T3c, T3e, C4a, C4b`.
- **Finding:** Initial regex in `_load_lean_tables()` failed on multi-line Lean list arms (`tblT3c`, `tblT3e`), and dead hardcoded constants existed at the top of the file. Removed all dead constants, fixed the parser to split arms across newlines, and added exact word-count assertions (`20, 48, 53, 49, 57`).
- **Verdict:** **CAUGHT & FIXED.**

### 5. Could any bibliography entry be fabricated or broken?
- **Attack:** Run live HTTP resolution on all 20 citations via `scripts/check_citations.py --live`.
- **Finding:** Two DOIs (`hales1973numerical`, `bohman2005limit2`) returned HTTP 404. Verified exact Crossref DOIs (`10.1016/0095-8956(73)90014-2` and `10.1090/S0002-9939-04-07470-2`), and patched `references.bib`. The script can check at most 19 of the 20 entries: `baumert1971combinatorial` has no DOI, arXiv id or URL (corrected 2026-11-26 from "20/20"). The review did not check that the bibliography covers the relevant prior work: Codenotti, Gerace and Resta (Ars Combin. 66, 2003) and the Buys–Polak–Zuiddam Lean repository are missing (see `ERRATA.md`).
- **Verdict:** **CAUGHT & FIXED.**

### 6. Could the paper overclaim solving Mega-Atlas `CS-049` or misstate institutional affiliation?
- **Attack:** Scan all files for `0thernes LLC` and overclaiming phrases.
- **Finding:** Zero `0thernes LLC` occurrences across all repo files (enforced by `scripts/check_readme_axioms.py`). Open Problem `O-1` (`CS-049`: exact $\Theta(C_n)$ for odd $n \ge 7$) is explicitly marked `[OPEN]` in Abstract, Table 1, Section 7, `CLAIMS.md`, `LIMITATIONS.md`, and `README.md`.
- **Verdict (v1.0.0):** DISCHARGED. **Withdrawn on 2026-11-26:** an independent statement audit found overclaims this review missed: two of the four "world records" ($C_{27}$, $C_{31}$) are below 2003 published values, and the claimed resolution of a Tandon "Open Problem #2" has no basis in the cited preprint. See `ERRATA.md`.
