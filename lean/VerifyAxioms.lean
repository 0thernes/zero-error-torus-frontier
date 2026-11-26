module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

import PalomarSolution
import ZeroErrorFrontier.NonVacuity
import ZeroErrorFrontier.AdversarialTests

/-!
# Strict Kernel Axiom Audit (`VerifyAxioms.lean`)

Prints exact transitive axiom footprints for all 18 Palomar headline targets,
all 7 non-vacuity witnesses, and all 7 adversarial boundary counterexamples (32 declarations total).
Every single declaration must depend ONLY on a subset of `{propext, Classical.choice, Quot.sound}`.
-/

#print axioms ZeroErrorFrontier.Palomar.prove_t1a
#print axioms ZeroErrorFrontier.Palomar.prove_t1b
#print axioms ZeroErrorFrontier.Palomar.prove_t1c
#print axioms ZeroErrorFrontier.Palomar.prove_t1d
#print axioms ZeroErrorFrontier.Palomar.prove_t1e
#print axioms ZeroErrorFrontier.Palomar.prove_t1f
#print axioms ZeroErrorFrontier.Palomar.prove_t2a
#print axioms ZeroErrorFrontier.Palomar.prove_t2b
#print axioms ZeroErrorFrontier.Palomar.prove_t2c
#print axioms ZeroErrorFrontier.Palomar.prove_t2d
#print axioms ZeroErrorFrontier.Palomar.prove_t3a
#print axioms ZeroErrorFrontier.Palomar.prove_t3b
#print axioms ZeroErrorFrontier.Palomar.prove_t3c
#print axioms ZeroErrorFrontier.Palomar.prove_t4a
#print axioms ZeroErrorFrontier.Palomar.prove_t4b
#print axioms ZeroErrorFrontier.Palomar.prove_t4c
#print axioms ZeroErrorFrontier.Palomar.prove_t4d
#print axioms ZeroErrorFrontier.Palomar.prove_all_frontier_theorems

#print axioms ZeroErrorFrontier.NonVacuity.nonvacuity_t1a
#print axioms ZeroErrorFrontier.NonVacuity.nonvacuity_t1b
#print axioms ZeroErrorFrontier.NonVacuity.nonvacuity_t1d_t1e
#print axioms ZeroErrorFrontier.NonVacuity.nonvacuity_t1f
#print axioms ZeroErrorFrontier.NonVacuity.nonvacuity_t3b
#print axioms ZeroErrorFrontier.NonVacuity.nonvacuity_t3c
#print axioms ZeroErrorFrontier.NonVacuity.nonvacuity_t4a_t4b

#print axioms ZeroErrorFrontier.AdversarialTests.boundary_hbpz_fails_at_n7
#print axioms ZeroErrorFrontier.AdversarialTests.boundary_hbpz_intracoset_collision_n3
#print axioms ZeroErrorFrontier.AdversarialTests.no_27_cosets_in_qGraphHBPZ_21
#print axioms ZeroErrorFrontier.AdversarialTests.no_38_cosets_in_qGraphHStar_25
#print axioms ZeroErrorFrontier.AdversarialTests.g7_not_bipartite
#print axioms ZeroErrorFrontier.AdversarialTests.no_size_6_in_c5_sq
#print axioms ZeroErrorFrontier.AdversarialTests.schlafli_sharp_ceilings
