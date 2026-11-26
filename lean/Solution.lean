module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import Challenge
public import ZeroErrorFrontier

/-!
# Complete Zero-`sorry` Solution (`Solution.lean`)

Discharges all 17 headline statements (`T1a`–`T4d`) and their master conjunction
`prove_all_frontier_theorems` from `ZeroErrorFrontier`, using strictly standard axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Solution

open Challenge
open ZeroErrorFrontier.CosetQuotient
open ZeroErrorFrontier.WorldRecords
open ZeroErrorFrontier.SeparationCalculus
open ZeroErrorFrontier.HaemersParadox

@[expose] public section

theorem prove_t1a : T1aStmt := t1a_coset_quotient_compression
theorem prove_t1b : T1bStmt := t1b_exact_quotient_ceilings
theorem prove_t1c : T1cStmt := t1c_intracoset_obstruction_and_hstar_flexibility
theorem prove_t1d : T1dStmt := fun m hm hmod => t1d_infinite_helical_hbpz_family m hm hmod
theorem prove_t1e : T1eStmt := fun k hk => t1e_infinite_hstar_family_and_ports k hk
theorem prove_t1f : T1fStmt := fun p d hp => t1f_baumert_pullback_homomorphism p d hp
theorem prove_t2a : T2aStmt := t2a_c25_world_record
theorem prove_t2b : T2bStmt := t2b_c27_world_record
theorem prove_t2c : T2cStmt := t2c_c29_world_record
theorem prove_t2d : T2dStmt := t2d_c31_world_record
theorem prove_t3a : T3aStmt := t3a_g7_induced_c5_and_exact_capacity
theorem prove_t3b : T3bStmt := fun G w m D hm inC y hcl hcov k N f hf =>
  t3b_weighted_fractional_clique_barrier G w m D hm inC y hcl hcov k N f hf
theorem prove_t3c : T3cStmt := t3c_heterogeneous_composition_and_tables
theorem prove_t4a : T4aStmt := fun G r hr L R hdiag hnon d =>
  t4a_haemers_rank_theorem G r hr L R hdiag hnon d
theorem prove_t4b : T4bStmt := fun G m hm w h D H s hD hs hnorm hh hdot horth d N hI =>
  t4b_integer_orthogonal_handle_sandwich G m hm w h D H s hD hs hnorm hh hdot horth d N hI
theorem prove_t4c : T4cStmt := t4c_lovasz_pentagon_theorem
theorem prove_t4d : T4dStmt := t4d_haemers_schlafli_paradox

theorem prove_all_frontier_theorems : AllFrontierTheoremsStmt :=
  ⟨prove_t1a, prove_t1b, prove_t1c, prove_t1d, prove_t1e, prove_t1f,
   prove_t2a, prove_t2b, prove_t2c, prove_t2d,
   prove_t3a, prove_t3b, prove_t3c,
   prove_t4a, prove_t4b, prove_t4c, prove_t4d⟩

end
end Solution
