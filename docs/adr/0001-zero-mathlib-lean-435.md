# ADR 0001: Zero-Mathlib Lean 4.35.0 Architecture & Six-Kernel Replay

- **Status:** Accepted
- **Date:** 2026-11-25
- **Archive ID:** `0TH-2026-016`

## Context
Large Mathlib-dependent formalizations introduce tens of thousands of transitive declarations, heavy build caches, frequent API drift, and often rely on `native_decide` (which adds `Lean.ofReduceBool` / `Lean.trustCompiler` to the trusted computing base).

## Decision
We build the entire `ZeroErrorFrontier` formal proof library directly on core Lean 4.35.0 (`Init` only) with `module` headers on line 1, zero external Lake dependencies, zero `native_decide`, zero custom axioms, and a `PalomarChallenge.lean` / `PalomarSolution.lean` / `comparator.json` boundary verified across six independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) via `lake check --paranoid` and `lake comparator --config comparator.json --paranoid`.

## Consequences
- Minimal trusted computing base (~30 seconds full build from scratch, zero Mathlib cache download).
- Every theorem from graph products and coset-quotient compression to Lovász $\Theta(C_5)=\sqrt{5}$ and Haemers's Schläfli paradox compiles cleanly through all six independent proof checkers.
- Trade-off: algebraic structures (`SimpleField`, `ZSqrt5`, exact integer Bessel/Gaussian elimination) are implemented directly in ~400 lines rather than imported from Mathlib.
