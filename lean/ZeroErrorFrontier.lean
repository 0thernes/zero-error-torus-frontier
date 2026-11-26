module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import ZeroErrorFrontier.GraphCore
public import ZeroErrorFrontier.CosetQuotient
public import ZeroErrorFrontier.SeparationCalculus
public import ZeroErrorFrontier.HaemersParadox
public import ZeroErrorFrontier.WorldRecords
public import ZeroErrorFrontier.NonVacuity
public import ZeroErrorFrontier.AdversarialTests

/-!
# `ZeroErrorFrontier` Umbrella Library

Zero-Mathlib Lean 4.35.0 formalization of:
1. Algebraic coset-quotient compression (`H_BPZ`, `H*`), exact double-counting ceilings,
   intra-coset obstruction vs. `H*` flexibility, infinite exact-ceiling families, and
   Baumert pullback homomorphisms (`ZeroErrorFrontier.CosetQuotient`).
2. Four consecutive machine-checked odd-cycle Shannon-capacity world records (`C₂₅`, `C₂₇`,
   `C₂₉`, `C₃₁`) strictly improving 55-year Baumert–Hales bounds (`ZeroErrorFrontier.WorldRecords`).
3. The 7-letter separation graph `G₇`, its hidden induced `C₅` engine, weighted fractional-clique
   barriers, and general multi-alphabet heterogeneous composition (`ZeroErrorFrontier.SeparationCalculus`).
4. General Haemers rank theorem over any `SimpleField`, integer orthogonal-handle sandwich theorem,
   Lovász's `Θ(C₅) = √5`, and Haemers's 1979 Schläfli paradox (`ZeroErrorFrontier.HaemersParadox`).
5. Non-vacuity and adversarial boundary theorems (`NonVacuity`, `AdversarialTests`).
-/
