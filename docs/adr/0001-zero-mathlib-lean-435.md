# ADR 0001: Zero-Mathlib Lean 4.35.0 Architecture & Six-Kernel Replay

- **Status:** Accepted
- **Date:** 2026-11-25
- **Archive ID:** `0TH-2026-016`

## Context
Large Mathlib-dependent formalizations introduce tens of thousands of transitive declarations, heavy build caches, frequent API drift, and often rely on `native_decide` (which adds `Lean.ofReduceBool` / `Lean.trustCompiler` to the trusted computing base).

## Decision
We build the entire `ZeroErrorFrontier` formal proof library directly on core Lean 4.35.0 (`Init` only) with `module` headers on line 1, zero external Lake dependencies, zero `native_decide`, zero custom axioms, and a `PalomarChallenge.lean` / `PalomarSolution.lean` / `comparator.json` boundary verified across six independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`) via `lake check --paranoid` and `lake comparator --config comparator.json --paranoid`.

## Consequences
- Minimal trusted computing base (about a minute for a full build from scratch, 70 s in the 2026-11-26 audit rebuild; zero Mathlib cache download).
- Every theorem from graph products and coset-quotient lifting to the integer form of Lovász's pentagon bound and Haemers's Schläfli-graph example compiles cleanly through all six independent proof checkers. Because $\Theta$ and real numbers are not defined, statements such as $\Theta(C_5)=\sqrt{5}$ are consequences outside Lean.
- Trade-off: algebraic structures (`SimpleField`, `ZSqrt5`, exact integer Bessel/Gaussian elimination) are implemented directly in ~400 lines rather than imported from Mathlib.
