module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import ZeroErrorFrontier.GraphCore
public import ZeroErrorFrontier.CosetQuotient
public import ZeroErrorFrontier.SeparationCalculus
public import ZeroErrorFrontier.HaemersParadox

/-!
# Statement-Only Challenge Definitions (`Challenge.lean`)

Defines the 17 headline theorem statement abbreviations (`T1aStmt`–`T4dStmt`) and their
master conjunction (`AllFrontierTheoremsStmt`) against the core mathematical definitions
in `GraphCore`, `CosetQuotient`, `SeparationCalculus`, and `HaemersParadox`, without
importing `WorldRecords` proof implementations.
-/

namespace Challenge

open ZeroErrorFrontier.GraphCore
open ZeroErrorFrontier.CosetQuotient
open ZeroErrorFrontier.SeparationCalculus
open ZeroErrorFrontier.HaemersParadox

@[expose] public section

abbrev T1aStmt : Prop :=
  (∀ (n M : Nat), 9 ≤ n →
    HasIndepSetOfSize (qGraphHBPZ n) M →
    HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n))) ∧
  (∀ (n M : Nat), 15 ≤ n →
    HasIndepSetOfSize (qGraphHStar n) M →
    HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n)))

abbrev T1bStmt : Prop :=
  (∀ n : Nat, 4 ≤ n → AlphaLe (qGraphHBPZ n) ((n * (n / 4)) / 4)) ∧
  (∀ n : Nat, 8 ≤ n → AlphaLe (qGraphHStar n) ((n * (n / 8)) / 2))

abbrev T1cStmt : Prop :=
  (∀ (n : Nat) (hn : 9 ≤ n) (q : Fin n × Fin n) (u v : Fin n) (e0 e1 e2 e3 : Int),
    -1 ≤ e0 → e0 ≤ 1 → -1 ≤ e1 → e1 ≤ 1 → -1 ≤ e2 → e2 ≤ 1 → -1 ≤ e3 → e3 ≤ 1 →
    (e3 - 2 * e0 = 1 ∨ e3 - 2 * e0 = -1) →
    let p0 := liftHBPZ n (by omega) q u v
    let p1 : Fin 4 → Fin n := fun i =>
      let ev : Int := match i with | ⟨0,_⟩ => e0 | ⟨1,_⟩ => e1 | ⟨2,_⟩ => e2 | ⟨3,_⟩ => e3
      ⟨(((p0 i).val : Int) + ev + n).toNat % n, Nat.mod_lt _ (by omega)⟩
    ∃ u' : Fin n, u' ≠ u ∧
      conflict (strongPow (cycleGraph n) 4) p1 (liftHBPZ n (by omega) q u' v)) ∧
  (∀ (n : Nat) (hn : 15 ≤ n) (q : Fin n × Fin n) (u v u' v' : Fin n) (s : Int),
    (s = 1 ∨ s = -1) →
    let p1 : Fin 4 → Fin n := fun i =>
      match i with
      | ⟨0,_⟩ => u
      | ⟨1,_⟩ => v
      | ⟨2,_⟩ => ⟨((q.1.val : Int) + s + n).toNat % n, Nat.mod_lt _ (by omega)⟩
      | ⟨3,_⟩ => ⟨(2 * u.val + 4 * v.val + q.2.val) % n, Nat.mod_lt _ (by omega)⟩
    conflict (strongPow (cycleGraph n) 4) p1 (liftHStar n (by omega) q u' v') →
    u' = u ∧ v' = v) ∧
  (ballSizeHStar 19 = 45 ∧ ballSizeHBPZ 19 = 49 ∧
   ballSizeHStar 21 = 45 ∧ ballSizeHBPZ 21 = 49 ∧
   ballSizeHStar 23 = 45 ∧ ballSizeHBPZ 23 = 49 ∧
   ballSizeHStar 25 = 45 ∧ ballSizeHBPZ 25 = 49)

abbrev T1dStmt : Prop :=
  ∀ (m : Nat), 5 ≤ m → (m % 4 = 0 ∨ m % 4 = 1) →
    let n := 4 * m + 1
    let M := helicalM m
    M = (n * (n / 4)) / 4 ∧
    HasIndepSetOfSize (qGraphHBPZ n) M ∧
    HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n))

abbrev T1eStmt : Prop :=
  ∀ (k : Nat) (hk : 3 ≤ k),
    let n := 8 * k + 1
    let M := hstarM k
    M = (n * (n / 8)) / 2 ∧
    HasIndepSetOfSize (qGraphHStar n) M ∧
    HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n)) ∧
    (k % 2 = 1 →
      let p0 : Fin n × Fin n := (⟨0, by omega⟩, ⟨0, by omega⟩)
      let p1 : Fin n × Fin n := (⟨n - 1, by omega⟩, ⟨0, by omega⟩)
      let Xq : Fin M → Fin n × Fin n := fun t =>
        let pt := hstarPt k hk t
        (⟨(pt.1.val + 1) % n, Nat.mod_lt _ (by omega)⟩,
         ⟨(pt.2.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩)
      hstarPt k hk ⟨0, by dsimp [M, hstarM]; omega⟩ = p0 ∧
      (∀ t : Fin M, conflict (qGraphHStar n) p1 (hstarPt k hk t) ↔ t.val = 0) ∧
      (∀ t : Fin M, conflict (qGraphHStar n) p0 (Xq t) ↔ t.val = 0) ∧
      (∀ t : Fin M, conflict (qGraphHStar n) p1 (Xq t) ↔ t.val = 4 * k * k - (k / 2 + 1)) ∧
      (0 ≠ 4 * k * k - (k / 2 + 1)))

abbrev T1fStmt : Prop :=
  ∀ (p d : Nat) (hp : 5 ≤ p),
    (∀ u v : Fin d → Fin (p + 2),
      conflict (strongPow (cycleGraph (p + 2)) d) u v →
      conflict (strongPow (cycleGraph p) d) (pullVec p d (by omega) u) (pullVec p d (by omega) v) ∧
      (pullVec p d (by omega) u = pullVec p d (by omega) v → u = v)) ∧
    (∀ (P : (Fin d → Fin p) → Prop),
      (∀ a b, P a → P b → conflict (strongPow (cycleGraph p) d) a b → a = b) →
      (∀ u v, P (pullVec p d (by omega) u) → P (pullVec p d (by omega) v) →
        conflict (strongPow (cycleGraph (p + 2)) d) u v → u = v))

abbrev T2aStmt : Prop :=
  ∃ M : Nat, HasIndepSetOfSize (strongPow (cycleGraph 25) 144) M ∧
    12344196091426841 ^ 144 ≤ M * (10 ^ 15) ^ 144

abbrev T2bStmt : Prop :=
  ∃ M : Nat, HasIndepSetOfSize (strongPow (cycleGraph 27) 2048) M ∧
    13319390984674515 ^ 2048 ≤ M * (10 ^ 15) ^ 2048

abbrev T2cStmt : Prop :=
  HasIndepSetOfSize (strongPow (cycleGraph 29) 4) 42050 ∧
  14319949949077991 ^ 4 ≤ 42050 * (10 ^ 15) ^ 4

abbrev T2dStmt : Prop :=
  ∃ M : Nat, HasIndepSetOfSize (strongPow (cycleGraph 31) 2048) M ∧
    15308776193986504 ^ 2048 ≤ M * (10 ^ 15) ^ 2048

abbrev T3aStmt : Prop :=
  (∀ i j : Fin 5, (cycleGraph 5).adj i j ↔ G7.adj (c5EmbedG7 i) (c5EmbedG7 j)) ∧
  HasIndepSetOfSize G7 3 ∧
  (∀ d : Nat, AlphaLe (strongPow G7 d) (3 ^ d))

abbrev T3bStmt : Prop :=
  ∀ {V : Type} (G : FinGraph V) (w : V → Nat) (m D : Nat), 0 < m →
    ∀ (inC : Nat → V → Bool) (y : Nat → Nat),
      (∀ j, j < m → ∀ u v : V, inC j u = true → inC j v = true → conflict G u v) →
      (∀ v : V, D * w v ≤ sumNat m (fun j => if inC j v then y j else 0)) →
      ∀ (k N : Nat) (f : Fin N → (Fin k → V)),
        (∀ i j : Fin N, i ≠ j → ¬ conflict (strongPow G k) (f i) (f j)) →
        D ^ k * sumNat N (fun i => if hi : i < N then prodNat k (fun t => w (f ⟨i, hi⟩ t)) else 0) ≤
        (sumNat m y) ^ k

abbrev T3cStmt : Prop :=
  (∀ (c : Letter), checkPairwiseB sep2B (tblT2a c) = true ∧
                   checkPairwiseB sep3B (tblT3c c) = true ∧
                   checkPairwiseB sep3B (tblT3e c) = true) ∧
  (∀ (c₁ c₂ : Letter), Letter.sep c₁ c₂ = true →
    checkCrossB sep2B (tblT2a c₁) (tblT2a c₂) = true ∧
    checkCrossB sep3B (tblT3c c₁) (tblT3c c₂) = true ∧
    checkCrossB sep3B (tblT3e c₁) (tblT3e c₂) = true) ∧
  (checkPairwiseB sep4B codeC4a = true ∧ checkPairwiseB sep4B codeC4b = true) ∧
  (∀ (Sym1 Sym2 SymP V₁ V₂ : Type)
     (sep₁ : Sym1 → Sym1 → Bool) (sep₂ : Sym2 → Sym2 → Bool) (sep' : SymP → SymP → Bool)
     (G₁ : FinGraph V₁) (G₂ : FinGraph V₂)
     (R₁ : SepRealisation Sym1 sep₁ G₁) (R₂ : SepRealisation Sym2 sep₂ G₂)
     (T : SymP → List (Sym1 × Sym2)),
     (∀ c, (T c).Pairwise (fun p q => sep₁ p.1 q.1 = true ∨ sep₂ p.2 q.2 = true)) →
     (∀ c₁ c₂, sep' c₁ c₂ = true → ∀ p ∈ T c₁, ∀ q ∈ T c₂, sep₁ p.1 q.1 = true ∨ sep₂ p.2 q.2 = true) →
     ∃ R' : SepRealisation SymP sep' (strongProd G₁ G₂),
       ∀ c, R'.sz c = sumListSizes (T c) (fun p => R₁.sz p.1 * R₂.sz p.2))

abbrev T4aStmt : Prop :=
  ∀ {F : Type} [SimpleField F] {V : Type} (G : FinGraph V) (r : Nat), 0 < r →
    ∀ (L : V → Nat → F) (R : Nat → V → F),
      (∀ v : V, sumF r (fun k => SimpleField.mul (L v k) (R k v)) ≠ SimpleField.zero) →
      (∀ u v : V, ¬ conflict G u v → sumF r (fun k => SimpleField.mul (L u k) (R k v)) = SimpleField.zero) →
      ∀ d : Nat, AlphaLe (strongPow G d) (r ^ d)

abbrev T4bStmt : Prop :=
  ∀ {V : Type} (G : FinGraph V) (m : Nat), 0 < m →
    ∀ (w : V → Nat → Int) (h : Nat → Int) (D H s : Int), 0 < D → 0 ≤ s →
      (∀ v : V, sumInt m (fun k => w v k * w v k) = D) →
      (sumInt m (fun k => h k * h k) = H) →
      (∀ v : V, s ≤ (sumInt m (fun k => h k * w v k)) * (sumInt m (fun k => h k * w v k))) →
      (∀ u v : V, ¬ conflict G u v → sumInt m (fun k => w u k * w v k) = 0) →
      ∀ (d N : Nat), HasIndepSetOfSize (strongPow G d) N → (N : Int) * s ^ d ≤ (H * D) ^ d

abbrev T4cStmt : Prop :=
  HasIndepSetOfSize (strongPow (cycleGraph 5) 2) 5 ∧
  ∀ (d N : Nat), HasIndepSetOfSize (strongPow (cycleGraph 5) d) N → N * N ≤ 5 ^ d

abbrev T4dStmt : Prop :=
  (∀ d : Nat, AlphaLe (strongPow schlafliGraph d) (3 ^ d)) ∧
  (∀ d : Nat, AlphaLe (strongPow schlafliComp d) (7 ^ d)) ∧
  HasIndepSetOfSize (strongProd schlafliGraph schlafliComp) 27 ∧
  3 * 7 < 27

abbrev AllFrontierTheoremsStmt : Prop :=
  T1aStmt ∧ T1bStmt ∧ T1cStmt ∧ T1dStmt ∧ T1eStmt ∧ T1fStmt ∧
  T2aStmt ∧ T2bStmt ∧ T2cStmt ∧ T2dStmt ∧
  T3aStmt ∧ T3bStmt ∧ T3cStmt ∧
  T4aStmt ∧ T4bStmt ∧ T4cStmt ∧ T4dStmt

end
end Challenge
