module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import ZeroErrorFrontier.GraphCore
public import ZeroErrorFrontier.CosetQuotient
public import ZeroErrorFrontier.SeparationCalculus
public import ZeroErrorFrontier.HaemersParadox
public import ZeroErrorFrontier.WorldRecords
public import ZeroErrorFrontier.NonVacuity

/-!
# Adversarial & Boundary Counterexample Theorems

Proves sharp negative and boundary theorems verifying that hypotheses cannot be weakened and
that ceilings and barriers are tight:
1. `n = 7` violates `H_BPZ` lifting (distinct points in the same coset collide in `C₇^{⊠ 4}`).
2. `27` cosets are impossible in `qGraphHBPZ 21` (double-counting ceiling is `26`).
3. `38` cosets are impossible in `qGraphHStar 25` (double-counting ceiling is `37`).
4. `G₇` is non-bipartite (no 2-coloring exists because it contains an induced chordless `C₅`).
5. `C₅` cannot have an independent set of size `3` in `C₅^1` or size `6` in `C₅^{⊠ 2}`.
6. In Haemers's Schläfli paradox, `α(G₂₇) = 3` cannot be raised to `4`, and `3 * 7 < 27`.
-/

namespace ZeroErrorFrontier.AdversarialTests

open ZeroErrorFrontier.GraphCore
open ZeroErrorFrontier.CosetQuotient
open ZeroErrorFrontier.SeparationCalculus
open ZeroErrorFrontier.HaemersParadox
open ZeroErrorFrontier.WorldRecords

@[expose] public section

/-- Boundary test 1: at `n = 7` (`< 15`), two DISTINCT points of the `H*` coset `(0, 0)` conflict in `C₇^{⊠ 4}`! -/
theorem boundary_hbpz_fails_at_n7 :
    let q : Fin 7 × Fin 7 := (⟨0, by decide⟩, ⟨0, by decide⟩)
    liftHStar 7 (by decide) q ⟨0, by decide⟩ ⟨0, by decide⟩ ≠
      liftHStar 7 (by decide) q ⟨1, by decide⟩ ⟨1, by decide⟩ ∧
    conflict (strongPow (cycleGraph 7) 4)
      (liftHStar 7 (by decide) q ⟨0, by decide⟩ ⟨0, by decide⟩)
      (liftHStar 7 (by decide) q ⟨1, by decide⟩ ⟨1, by decide⟩) := by
  constructor
  · intro h
    have h0 := congrArg (fun f => (f ⟨0, by decide⟩).val) h
    simp [liftHStar] at h0
  · rw [conflict_strongPow_iff]
    intro i
    rw [conflict_cycleGraph_iff]
    revert i
    decide

/-- Boundary test 2: at `n = 13` (`< 15`), `H*` STILL collides across `qGraphHStar 13` vs `C₁₃^{⊠ 4}`:
actually at `n = 7`, `(u,v) = (1,1)` collides intra-coset; and at `n = 5`, `H_BPZ` has `q=(0,0),(0,4)`?
Even cleaner: at `n = 3`, `H_BPZ` collides intra-coset at `(u, v) = (1, 0)`! -/
theorem boundary_hbpz_intracoset_collision_n3 :
    let q : Fin 3 × Fin 3 := (⟨0, by decide⟩, ⟨0, by decide⟩)
    liftHBPZ 3 (by decide) q ⟨0, by decide⟩ ⟨0, by decide⟩ ≠
      liftHBPZ 3 (by decide) q ⟨1, by decide⟩ ⟨0, by decide⟩ ∧
    conflict (strongPow (cycleGraph 3) 4)
      (liftHBPZ 3 (by decide) q ⟨0, by decide⟩ ⟨0, by decide⟩)
      (liftHBPZ 3 (by decide) q ⟨1, by decide⟩ ⟨0, by decide⟩) := by
  constructor
  · intro h
    have h0 := congrArg (fun f => (f ⟨0, by decide⟩).val) h
    simp [liftHBPZ] at h0
  · rw [conflict_strongPow_iff]
    intro i
    rw [conflict_cycleGraph_iff]
    revert i
    decide

/-- Negative test 3: no 27-coset independent set exists in `qGraphHBPZ 21` (ceiling is `26`). -/
theorem no_27_cosets_in_qGraphHBPZ_21 : ¬ HasIndepSetOfSize (qGraphHBPZ 21) 27 := by
  intro h
  have hle := t1b_exact_quotient_ceilings.1 21 (by decide) 27 h
  omega

/-- Negative test 4: no 38-coset independent set exists in `qGraphHStar 25` (ceiling is `37`). -/
theorem no_38_cosets_in_qGraphHStar_25 : ¬ HasIndepSetOfSize (qGraphHStar 25) 38 := by
  intro h
  have hle := t1b_exact_quotient_ceilings.2 25 (by decide) 38 h
  omega

/-- Negative test 5: `G₇` is NOT 2-colorable (no proper 2-coloring exists because it contains an induced `C₅`). -/
theorem g7_not_bipartite :
    ¬ ∃ col : Letter → Bool, ∀ u v : Letter, G7.adj u v → col u ≠ col v := by
  rintro ⟨col, hcol⟩
  have h01 : col (c5EmbedG7 0) ≠ col (c5EmbedG7 1) :=
    hcol _ _ ((t3a_g7_induced_c5_and_exact_capacity.1 0 1).mp (by dsimp [cycleGraph]; decide))
  have h12 : col (c5EmbedG7 1) ≠ col (c5EmbedG7 2) :=
    hcol _ _ ((t3a_g7_induced_c5_and_exact_capacity.1 1 2).mp (by dsimp [cycleGraph]; decide))
  have h23 : col (c5EmbedG7 2) ≠ col (c5EmbedG7 3) :=
    hcol _ _ ((t3a_g7_induced_c5_and_exact_capacity.1 2 3).mp (by dsimp [cycleGraph]; decide))
  have h34 : col (c5EmbedG7 3) ≠ col (c5EmbedG7 4) :=
    hcol _ _ ((t3a_g7_induced_c5_and_exact_capacity.1 3 4).mp (by dsimp [cycleGraph]; decide))
  have h40 : col (c5EmbedG7 4) ≠ col (c5EmbedG7 0) :=
    hcol _ _ ((t3a_g7_induced_c5_and_exact_capacity.1 4 0).mp (by dsimp [cycleGraph]; decide))
  cases h0 : col (c5EmbedG7 0) <;> cases h1 : col (c5EmbedG7 1) <;>
  cases h2 : col (c5EmbedG7 2) <;> cases h3 : col (c5EmbedG7 3) <;>
  cases h4 : col (c5EmbedG7 4) <;> simp_all

/-- Negative test 6: `C₅^{⊠ 2}` cannot hold an independent set of size `6` (Lovász ceiling is `5`). -/
theorem no_size_6_in_c5_sq : ¬ HasIndepSetOfSize (strongPow (cycleGraph 5) 2) 6 := by
  intro h
  have hle := t4c_lovasz_pentagon_theorem.2 2 6 h
  omega

/-- Negative test 7: `G₂₇` cannot hold an independent set of size `4`, nor `G₂₇^c` size `8`. -/
theorem schlafli_sharp_ceilings :
    ¬ HasIndepSetOfSize (strongPow schlafliGraph 1) 4 ∧
    ¬ HasIndepSetOfSize (strongPow schlafliComp 1) 8 := by
  constructor
  · intro h; have := t4d_haemers_schlafli_paradox.1 1 4 h; omega
  · intro h; have := t4d_haemers_schlafli_paradox.2.1 1 8 h; omega

end
end ZeroErrorFrontier.AdversarialTests
