# Frequently Asked Questions (`zero-error-torus-frontier`)

### 1. Does this paper solve the exact Shannon capacity of $C_7$ or $C_{25}$ (Mega-Atlas `CS-049`)?
**No.** Exact $\Theta(C_n)$ for every odd $n \ge 7$ remains explicitly open (`O-1` in `CLAIMS.md`). We prove four new machine-checked lower-bound world records for $C_{25}, C_{27}, C_{29}, C_{31}$ surpassing the 1971–1973 Baumert–Hales bounds, establish two infinite exact-ceiling code families, characterize the $G_7$ separation graph and its fractional-clique-cover barrier, and give a zero-Mathlib six-kernel proof of Lovász's $\Theta(C_5)=\sqrt{5}$ and Haemers's 1979 Schläfli paradox.

### 2. Why zero-Mathlib Lean 4.35.0 instead of Mathlib?
Zero external dependencies shrink the trusted computing base dramatically, enable full clean builds in ~30 seconds without downloading gigabytes of `.olean` caches, and make it effortless to replay every theorem across all six independent proof kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`). See [ADR 0001](adr/0001-zero-mathlib-lean-435.md).

### 3. Why is `native_decide` forbidden?
`native_decide` adds the Lean compiler and C runtime (`Lean.ofReduceBool`, `Lean.trustCompiler`) to the trusted computing base. Every combinatorial check in our repository—including the 5-table separation calculus, the $27\times 7$ $\mathbb{F}_2$ Schläfli factorization, and the 88-port / 133-port Baumert 81-ball certificates—runs in pure kernel `decide` with zero `native_decide`.

### 4. Why does `PalomarChallenge.lean` contain `sorry`?
`PalomarChallenge.lean` is the 38-line machine-checkable problem interface consumed by `lake comparator --config comparator.json --paranoid`. It is excluded from `defaultTargets`, and every single one of its 18 target theorems is proved with zero `sorry` in `PalomarSolution.lean` / `Solution.lean`.

### 5. Why did you verify the Schläfli paradox using $\mathbb{Z}^8$ vectors instead of real eigenvalues?
Working over $\mathbb{Z}^8$ via our exact Integer Orthogonal-Handle Sandwich Theorem (`T4b`) eliminates floating-point arithmetic, real-number axioms, and SDP solvers completely, proving $\alpha(G_{27}^{\boxtimes d}) \le 3^d$ for all $d \ge 1$ inside pure integer arithmetic.
