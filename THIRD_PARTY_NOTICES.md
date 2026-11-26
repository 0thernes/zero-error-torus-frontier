# Third-Party Notices and Attribution

All source code, formal Lean 4 proofs, Rust/C11/Python verification engines, and manuscript prose in `zero-error-torus-frontier` are original works by Alexander Stephen Donahue (ORCID `0009-0006-8168-9648`).

## Prior Research & Mathematical Attribution

This work builds directly upon, cites, and extends published mathematical constructions from the open scientific literature (no third-party source code or LaTeX files are redistributed):

1. **P. Buys, S. Polak, and J. Zuiddam (2026)**, *"Lean-verified lower bounds for the Shannon capacity of odd cycles"*, `arXiv:2607.29681` and companion Apache-2.0 repository `spectra-research/shannon-capacity-lean`. The 7-letter separation system (`Letter.sep`) and admissible substitution / terminal code tables (`T2a`, `T3c`, `T3e`, `C4a`, `C4b`) originate in their work and Gao (2026); here we independently re-verify their admissibility inside Lean 4.35.0's pure kernel with zero Mathlib and zero `native_decide`, prove the induced-$C_5$ anatomy and weighted fractional-clique-cover upper bound of $G_7$, and state a two-alphabet, two-graph form of their combining rule (`Realisation.multiSubst` in `ShannonBounds/Layered.lean`). The $C_{25}$/$C_{29}$ coset codes and the $C_{27}$/$C_{31}$ expansion-plus-ports steps follow their $C_{21} \to C_{23}$ construction.
2. **Y. Gao (2026)**, *"A Recursive Construction Improving the Lower Bound on the Shannon Capacity of $C_7$"*, `arXiv:2607.27869`.
3. **R. Tandon (2026)**, *"Strengthening Recursive Constructions for Zero-Error Shannon Capacity"*, `arXiv:2608.30273` (preprint). Our Theorem T3c is a two-alphabet form of the combining rule stated there as Definition 6 and Proposition 1. It does not resolve any open problem: the two-sided extension of Tandon's Theorem 1 mentioned in his concluding section is not addressed. (Corrected 2026-11-26; an earlier version of this file said T3c resolves an "Open Problem #2", which the preprint does not contain.)
4. **L. D. Baumert, R. J. McEliece, E. Rodemich, H. C. Rumsey Jr., R. Stanley, and H. Taylor (1971)**, *"A combinatorial packing problem"*, SIAM–AMS Proc. 4, 97–108, and **R. S. Hales (1973)**, *"Numerical invariants and the strong product of graphs"*, J. Combin. Theory Ser. B 15, 146–155.
5. **L. Lovász (1979)**, *"On the Shannon capacity of a graph"*, IEEE Trans. Inform. Theory 25(1), 1–7.
6. **W. Haemers (1979)**, *"On some problems of Lovász concerning the Shannon capacity of a graph"*, IEEE Trans. Inform. Theory 25(2), 231–232.
7. **B. Codenotti, I. Gerace, and S. Resta (2003)**, *"Some remarks on the Shannon capacity of odd cycles"*, Ars Combinatoria 66, 243–257. Table 1 gives the comparison values $23125, 31522, 42017, 54934$ for $\alpha(C_n^{\boxtimes 4})$, $n = 25, 27, 29, 31$; the $C_{27}$ and $C_{31}$ bounds of this work are below them. Theorem 1 gives the `T1e` sizes for odd $k$.

## Toolchain Dependencies (Build-Time Only)

- **Lean 4.35.0 & Lake 5.0.0** (Apache-2.0): <https://github.com/leanprover/lean4>
- **Rust / Cargo 1.94.1** (MIT/Apache-2.0): zero external crates required (stdlib-only Rust engine).
- **GCC / Clang C11** (GPL/Apache-2.0-with-LLVM-exception): zero external libraries beyond C11 stdlib.
- **Python 3.12 + Matplotlib / Pytest / Hypothesis** (PSF / BSD / MIT / MPL-2.0): verification, property tests, and figure generation.
- **Tectonic 0.17.0** (MIT): deterministic AMS-LaTeX PDF compilation.
