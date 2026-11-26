# Frequently Asked Questions (`zero-error-torus-frontier`)

### 1. Does this paper solve the exact Shannon capacity of $C_7$ or $C_{25}$ (Mega-Atlas `CS-049`)?
**No.** Exact $\Theta(C_n)$ for every odd $n \ge 7$ remains explicitly open (`O-1` in `CLAIMS.md`). We prove four machine-checked lower bounds for $C_{25}, C_{27}, C_{29}, C_{31}$. Those for $C_{25}$ and $C_{29}$ exceed the largest published values we found (Codenotti, Gerace and Resta, Ars Combin. 66, 2003, Table 1: $23125^{1/4}$ and $42017^{1/4}$); those for $C_{27}$ and $C_{31}$ are below the values in the same table ($31522^{1/4}$ and $54934^{1/4}$). We also prove two families of coset-union codes that meet a quotient ceiling (many of their sizes were published earlier), a weighted clique-cover upper bound, $\alpha(G_7^{\boxtimes d}) \le 3^d$ for the 7-label graph $G_7$, and zero-Mathlib six-kernel-checked integer forms of Lovász's pentagon bound and Haemers's 1979 Schläfli-graph example. No published open problem is resolved. See [`ERRATA.md`](../ERRATA.md) for corrections to the v1.0.0 wording.

### 2. Why zero-Mathlib Lean 4.35.0 instead of Mathlib?
Zero external dependencies shrink the trusted computing base dramatically, enable full clean builds in about a minute (70 s in the 2026-11-26 audit rebuild) without downloading gigabytes of `.olean` caches, and make it effortless to replay every theorem across all six independent proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`). See [ADR 0001](adr/0001-zero-mathlib-lean-435.md).

### 3. Why is `native_decide` forbidden?
`native_decide` adds the Lean compiler and C runtime (`Lean.ofReduceBool`, `Lean.trustCompiler`) to the trusted computing base. Every combinatorial check in our repository—including the 5-table separation calculus, the $27\times 7$ $\mathbb{F}_2$ Schläfli factorization, and the 88-port / 133-port Baumert 81-ball certificates—runs in pure kernel `decide` with zero `native_decide`.

### 4. Why does `PalomarChallenge.lean` contain `sorry`?
`PalomarChallenge.lean` is the 38-line machine-checkable problem interface consumed by `lake comparator --config comparator.json --paranoid`. It is excluded from `defaultTargets`, and every single one of its 18 target theorems is proved with zero `sorry` in `PalomarSolution.lean` / `Solution.lean`.

### 5. Why did you verify Haemers's Schläfli-graph example using $\mathbb{Z}^8$ vectors instead of real eigenvalues?
Working over $\mathbb{Z}^8$ via our exact Integer Orthogonal-Handle Sandwich Theorem (`T4b`) eliminates floating-point arithmetic, real-number axioms, and SDP solvers completely, proving $\alpha(G_{27}^{\boxtimes d}) \le 3^d$ for all $d \ge 1$ inside pure integer arithmetic.
