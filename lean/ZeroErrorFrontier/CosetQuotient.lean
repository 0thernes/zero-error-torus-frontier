module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import ZeroErrorFrontier.GraphCore

/-!
# Pillar 1: Algebraic Quotient-Torus Compression, Exact Ceilings,
# Intra-Coset Obstruction, Infinite Helical & `H*` Families, and Baumert Pullback

Zero-Mathlib, zero-`sorry`, zero-`native_decide` formalization of Theorems T1a–T1f:
- **T1a (`t1a_coset_quotient_compression`):** Exact `n²`-to-1 compression for both
  `H_BPZ = ⟨(1,0,0,2),(0,1,2,0)⟩` (`n ≥ 9`) and `H* = ⟨(1,0,0,2),(0,1,0,4)⟩` (`n ≥ 15`).
- **T1b (`t1b_exact_quotient_ceilings`):** Exact double-counting ceilings
  `α((C_n³)^{⊠ 2}) ≤ ⌊n ⌊n/4⌋ / 4⌋` and `α(C_n ⊠ C_n⁷) ≤ ⌊n ⌊n/8⌋ / 2⌋`.
- **T1c (`t1c_intracoset_obstruction_and_hstar_flexibility`):** Intra-Coset Obstruction
  for `H_BPZ` (`|dy|=1` or `|dz|=1` collides intra-coset) vs. unconditional `e=(0,0,±1,0)`
  intra-coset privacy and smaller `45`-ball (`45 < 49`) for `H*`.
- **T1d (`t1d_infinite_helical_hbpz_family`):** Infinite exact-ceiling `H_BPZ` helical
  staircase for all `m ≥ 5` with `m % 4 = 0 ∨ m % 4 = 1`, `n = 4m + 1`, `M = m² + m/4`.
- **T1e (`t1e_infinite_hstar_family_and_ports`):** Infinite exact-ceiling `H*` staircase
  for all `k ≥ 3`, `n = 8k + 1`, `M = 4k² + k/2`, plus automatic full `H*`-invariant
  quotient port system (`A = 1`, `D = 1`, `η = M - 2`) for every odd `k = 2j + 1 ≥ 3`.
- **T1f (`t1f_baumert_pullback_homomorphism`):** 5-line locally-injective Baumert pullback
  homomorphism `pull^d : C_{p+2}^{⊠ d} → C_p^{⊠ d}` (`p ≥ 5`) with exact factored counting.
-/

namespace ZeroErrorFrontier.CosetQuotient

open ZeroErrorFrontier.GraphCore

@[expose] public section

/-! ### 1. Quotient Torus Graphs & Algebraic Compression (T1a) -/

/-- Distance-`r` cyclic power graph `C_n^r` on `Fin n`: `a` and `b` conflict iff `cycDist n a b ≤ r`. -/
def cycPowGraph (n r : Nat) : FinGraph (Fin n) where
  adj a b := a ≠ b ∧ cycDist n a.val b.val ≤ r
  symm := fun ⟨hne, hd⟩ => ⟨hne.symm, by rw [cycDist_symm]; exact hd⟩
  irrefl := fun ⟨hne, _⟩ => hne rfl

theorem conflict_cycPowGraph_iff (n r : Nat) (a b : Fin n) :
    conflict (cycPowGraph n r) a b ↔ cycDist n a.val b.val ≤ r := by
  constructor
  · intro h
    cases h with
    | inl heq =>
      subst heq
      have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
      rw [cycDist_self n a.val hnpos]; omega
    | inr hadj => exact hadj.2
  · intro hd
    by_cases heq : a = b
    · exact Or.inl heq
    · exact Or.inr ⟨heq, hd⟩

/-- `H_BPZ` quotient graph `(C_n³)^{⊠ 2}` (`L_∞ ≤ 3`, 49-vertex closed ball). -/
def qGraphHBPZ (n : Nat) : FinGraph (Fin n × Fin n) :=
  strongProd (cycPowGraph n 3) (cycPowGraph n 3)

/-- `H*` quotient graph `C_n ⊠ C_n⁷` (`|dy| ≤ 1 ∧ |dz| ≤ 7`, 45-vertex closed ball). -/
def qGraphHStar (n : Nat) : FinGraph (Fin n × Fin n) :=
  strongProd (cycPowGraph n 1) (cycPowGraph n 7)

/-- Modular triangle inequality for `cycDist`: if `cycDist n a b ≤ r` and `a, b < n`,
then there is a signed offset `δ ∈ [-r, r]` with `(a : Int) - b ≡ δ (mod n)`. -/
theorem cycDist_signed_delta (n a b r : Nat) (ha : a < n) (hb : b < n)
    (hd : cycDist n a b ≤ r) :
    ∃ (δ : Int) (q : Int), - (r : Int) ≤ δ ∧ δ ≤ (r : Int) ∧ (a : Int) - (b : Int) = q * (n : Int) + δ := by
  rw [cycDist_le_iff n a b r ha hb] at hd
  rcases hd with ⟨hab, hle⟩ | ⟨hba, hle⟩ | hle | hle
  · exact ⟨(a - b : Nat), 0, by omega, by omega, by omega⟩
  · exact ⟨-((b - a : Nat) : Int), 0, by omega, by omega, by omega⟩
  · exact ⟨(a + n - b : Nat), -1, by omega, by omega, by omega⟩
  · exact ⟨-((b + n - a : Nat) : Int), 1, by omega, by omega, by omega⟩

/-- Converse: if `(a : Int) - (b : Int) = q * n + δ` with `|δ| ≤ r < n` and `a, b < n`,
then `cycDist n a b ≤ r`. -/
theorem cycDist_of_signed_delta (n a b r : Nat) (ha : a < n) (hb : b < n) (hr : r < n)
    (δ q : Int) (hlo : -(r : Int) ≤ δ) (hhi : δ ≤ (r : Int))
    (heq : (a : Int) - (b : Int) = q * (n : Int) + δ) :
    cycDist n a b ≤ r := by
  rw [cycDist_le_iff n a b r ha hb]
  -- Since `-(n : Int) < (a : Int) - (b : Int) < (n : Int)` and `|δ| < n`, `q ∈ {-1, 0, 1}`!
  have hq_lo : -1 ≤ q := by
    apply Classical.byContradiction; intro hlt
    have hq2 : q ≤ -2 := by omega
    have hm : q * (n : Int) ≤ (-2) * (n : Int) := Int.mul_le_mul_of_nonneg_right hq2 (by omega)
    omega
  have hq_hi : q ≤ 1 := by
    apply Classical.byContradiction; intro hgt
    have hq2 : 2 ≤ q := by omega
    have hm : 2 * (n : Int) ≤ q * (n : Int) := Int.mul_le_mul_of_nonneg_right hq2 (by omega)
    omega
  have hcases : q = -1 ∨ q = 0 ∨ q = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · right; right; left; omega
  · by_cases hab : a ≥ b
    · left; exact ⟨hab, by omega⟩
    · right; left; exact ⟨by omega, by omega⟩
  · right; right; right; omega

/-- Helper: if `K * n + δ = 0` with `n > 0` and `-n < δ < n`, then `K = 0`. -/
theorem int_mul_eq_zero_of_abs_lt {K n δ : Int} (hn : 0 < n) (hlo : -n < δ) (hhi : δ < n)
    (heq : K * n + δ = 0) : K = 0 := by
  apply Classical.byContradiction; intro hne
  by_cases hpos : 1 ≤ K
  · have hm := Int.mul_le_mul_of_nonneg_right hpos (by omega : 0 ≤ n)
    rw [Int.one_mul] at hm; omega
  · have hneg : K ≤ -1 := by omega
    have hm := Int.mul_le_mul_of_nonneg_right hneg (by omega : 0 ≤ n)
    have h1 : (-1 : Int) * n = -n := by simp
    rw [h1] at hm; omega

/-- Helper: `(x % n : Int) = x - (x / n) * n`. -/
theorem int_mod_decomp (x n : Nat) (_hn : 0 < n) :
    ∃ k : Int, ((x % n : Nat) : Int) = (x : Int) - k * (n : Int) := by
  refine ⟨(x / n : Nat), ?_⟩
  have h := Nat.div_add_mod x n
  have hmul : ((x / n : Nat) : Int) * (n : Int) = ((n * (x / n) : Nat) : Int) := by
    rw [Nat.mul_comm]; rfl
  omega

/-- Lifting a quotient point `(y, z)` and fiber `(u, v)` under `H_BPZ = ⟨(1,0,0,2),(0,1,2,0)⟩`. -/
def liftHBPZ (n : Nat) (hn : 0 < n) (q : Fin n × Fin n) (u v : Fin n) : Fin 4 → Fin n
  | ⟨0, _⟩ => u
  | ⟨1, _⟩ => v
  | ⟨2, _⟩ => ⟨(2 * v.val + q.1.val) % n, Nat.mod_lt _ hn⟩
  | ⟨3, _⟩ => ⟨(2 * u.val + q.2.val) % n, Nat.mod_lt _ hn⟩

/-- Lifting a quotient point `(y, z)` and fiber `(u, v)` under `H* = ⟨(1,0,0,2),(0,1,0,4)⟩`. -/
def liftHStar (n : Nat) (hn : 0 < n) (q : Fin n × Fin n) (u v : Fin n) : Fin 4 → Fin n
  | ⟨0, _⟩ => u
  | ⟨1, _⟩ => v
  | ⟨2, _⟩ => q.1
  | ⟨3, _⟩ => ⟨(2 * u.val + 4 * v.val + q.2.val) % n, Nat.mod_lt _ hn⟩

theorem liftHBPZ_conflict_implies_quot {n : Nat} (hn : 9 ≤ n)
    (q1 q2 : Fin n × Fin n) (u1 v1 u2 v2 : Fin n)
    (hc : conflict (strongPow (cycleGraph n) 4)
            (liftHBPZ n (by omega) q1 u1 v1)
            (liftHBPZ n (by omega) q2 u2 v2)) :
    conflict (qGraphHBPZ n) q1 q2 ∧ (q1 = q2 → u1 = u2 ∧ v1 = v2) := by
  rw [conflict_strongPow_iff] at hc
  have h0 := (conflict_cycleGraph_iff n _ _).mp (hc ⟨0, by omega⟩)
  have h1 := (conflict_cycleGraph_iff n _ _).mp (hc ⟨1, by omega⟩)
  have h2 := (conflict_cycleGraph_iff n _ _).mp (hc ⟨2, by omega⟩)
  have h3 := (conflict_cycleGraph_iff n _ _).mp (hc ⟨3, by omega⟩)
  dsimp [liftHBPZ] at h0 h1 h2 h3
  rcases cycDist_signed_delta n u1.val u2.val 1 u1.isLt u2.isLt h0 with ⟨du, qu, hdu1, hdu2, hdu⟩
  rcases cycDist_signed_delta n v1.val v2.val 1 v1.isLt v2.isLt h1 with ⟨dv, qv, hdv1, hdv2, hdv⟩
  rcases cycDist_signed_delta n ((2 * v1.val + q1.1.val) % n) ((2 * v2.val + q2.1.val) % n) 1
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h2 with ⟨d2, q2i, hd21, hd22, hd2⟩
  rcases cycDist_signed_delta n ((2 * u1.val + q1.2.val) % n) ((2 * u2.val + q2.2.val) % n) 1
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h3 with ⟨d3, q3i, hd31, hd32, hd3⟩
  rcases int_mod_decomp (2 * v1.val + q1.1.val) n (by omega) with ⟨kv1, hkv1⟩
  rcases int_mod_decomp (2 * v2.val + q2.1.val) n (by omega) with ⟨kv2, hkv2⟩
  rcases int_mod_decomp (2 * u1.val + q1.2.val) n (by omega) with ⟨ku1, hku1⟩
  rcases int_mod_decomp (2 * u2.val + q2.2.val) n (by omega) with ⟨ku2, hku2⟩
  have hy_eq : (q1.1.val : Int) - (q2.1.val : Int) =
      (q2i + kv1 - kv2 - 2 * qv) * (n : Int) + (d2 - 2 * dv) := by
    have hmul : (q2i + kv1 - kv2 - 2 * qv) * (n : Int) =
        q2i * n + kv1 * n - kv2 * n - 2 * (qv * n) := by
      rw [Int.sub_mul, Int.sub_mul, Int.add_mul, Int.mul_assoc]
    omega
  have hz_eq : (q1.2.val : Int) - (q2.2.val : Int) =
      (q3i + ku1 - ku2 - 2 * qu) * (n : Int) + (d3 - 2 * du) := by
    have hmul : (q3i + ku1 - ku2 - 2 * qu) * (n : Int) =
        q3i * n + ku1 * n - ku2 * n - 2 * (qu * n) := by
      rw [Int.sub_mul, Int.sub_mul, Int.add_mul, Int.mul_assoc]
    omega
  constructor
  · rw [qGraphHBPZ, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff]
    exact ⟨cycDist_of_signed_delta n q1.1.val q2.1.val 3 q1.1.isLt q2.1.isLt (by omega)
             (d2 - 2 * dv) (q2i + kv1 - kv2 - 2 * qv) (by omega) (by omega) hy_eq,
           cycDist_of_signed_delta n q1.2.val q2.2.val 3 q1.2.isLt q2.2.isLt (by omega)
             (d3 - 2 * du) (q3i + ku1 - ku2 - 2 * qu) (by omega) (by omega) hz_eq⟩
  · intro hqeq
    subst hqeq
    have hdv0 : dv = 0 := by
      have hK0 := int_mul_eq_zero_of_abs_lt (K := q2i + kv1 - kv2 - 2 * qv) (n := (n : Int)) (δ := d2 - 2 * dv)
        (by omega) (by omega) (by omega) (by omega)
      rw [hK0, Int.zero_mul] at hy_eq; omega
    have hdu0 : du = 0 := by
      have hK0 := int_mul_eq_zero_of_abs_lt (K := q3i + ku1 - ku2 - 2 * qu) (n := (n : Int)) (δ := d3 - 2 * du)
        (by omega) (by omega) (by omega) (by omega)
      rw [hK0, Int.zero_mul] at hz_eq; omega
    have hu_eq : u1 = u2 := by
      apply Fin.ext
      have hq0 := int_mul_eq_zero_of_abs_lt (K := qu) (n := (n : Int)) (δ := (u2.val : Int) - (u1.val : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hq0, Int.zero_mul] at hdu; omega
    have hv_eq : v1 = v2 := by
      apply Fin.ext
      have hq0 := int_mul_eq_zero_of_abs_lt (K := qv) (n := (n : Int)) (δ := (v2.val : Int) - (v1.val : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hq0, Int.zero_mul] at hdv; omega
    exact ⟨hu_eq, hv_eq⟩

theorem liftHStar_conflict_implies_quot {n : Nat} (hn : 15 ≤ n)
    (q1 q2 : Fin n × Fin n) (u1 v1 u2 v2 : Fin n)
    (hc : conflict (strongPow (cycleGraph n) 4)
            (liftHStar n (by omega) q1 u1 v1)
            (liftHStar n (by omega) q2 u2 v2)) :
    conflict (qGraphHStar n) q1 q2 ∧ (q1 = q2 → u1 = u2 ∧ v1 = v2) := by
  rw [conflict_strongPow_iff] at hc
  have h0 := (conflict_cycleGraph_iff n _ _).mp (hc ⟨0, by omega⟩)
  have h1 := (conflict_cycleGraph_iff n _ _).mp (hc ⟨1, by omega⟩)
  have h2 := (conflict_cycleGraph_iff n _ _).mp (hc ⟨2, by omega⟩)
  have h3 := (conflict_cycleGraph_iff n _ _).mp (hc ⟨3, by omega⟩)
  dsimp [liftHStar] at h0 h1 h2 h3
  rcases cycDist_signed_delta n u1.val u2.val 1 u1.isLt u2.isLt h0 with ⟨du, qu, hdu1, hdu2, hdu⟩
  rcases cycDist_signed_delta n v1.val v2.val 1 v1.isLt v2.isLt h1 with ⟨dv, qv, hdv1, hdv2, hdv⟩
  rcases cycDist_signed_delta n ((2 * u1.val + 4 * v1.val + q1.2.val) % n)
    ((2 * u2.val + 4 * v2.val + q2.2.val) % n) 1
    (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h3 with ⟨d3, q3i, hd31, hd32, hd3⟩
  rcases int_mod_decomp (2 * u1.val + 4 * v1.val + q1.2.val) n (by omega) with ⟨k1, hk1⟩
  rcases int_mod_decomp (2 * u2.val + 4 * v2.val + q2.2.val) n (by omega) with ⟨k2, hk2⟩
  have hz_eq : (q1.2.val : Int) - (q2.2.val : Int) =
      (q3i + k1 - k2 - 2 * qu - 4 * qv) * (n : Int) + (d3 - 2 * du - 4 * dv) := by
    have hmul : (q3i + k1 - k2 - 2 * qu - 4 * qv) * (n : Int) =
        q3i * n + k1 * n - k2 * n - 2 * (qu * n) - 4 * (qv * n) := by
      rw [Int.sub_mul, Int.sub_mul, Int.sub_mul, Int.add_mul, Int.mul_assoc, Int.mul_assoc]
    omega
  constructor
  · rw [qGraphHStar, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff]
    exact ⟨h2, cycDist_of_signed_delta n q1.2.val q2.2.val 7 q1.2.isLt q2.2.isLt (by omega)
             (d3 - 2 * du - 4 * dv) (q3i + k1 - k2 - 2 * qu - 4 * qv) (by omega) (by omega) hz_eq⟩
  · intro hqeq
    subst hqeq
    have hK0 := int_mul_eq_zero_of_abs_lt (K := q3i + k1 - k2 - 2 * qu - 4 * qv) (n := (n : Int))
      (δ := d3 - 2 * du - 4 * dv) (by omega) (by omega) (by omega) (by omega)
    rw [hK0, Int.zero_mul] at hz_eq
    have hdu0 : du = 0 := by omega
    have hdv0 : dv = 0 := by omega
    have hu_eq : u1 = u2 := by
      apply Fin.ext
      have hq0 := int_mul_eq_zero_of_abs_lt (K := qu) (n := (n : Int)) (δ := (u2.val : Int) - (u1.val : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hq0, Int.zero_mul] at hdu; omega
    have hv_eq : v1 = v2 := by
      apply Fin.ext
      have hq0 := int_mul_eq_zero_of_abs_lt (K := qv) (n := (n : Int)) (δ := (v2.val : Int) - (v1.val : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hq0, Int.zero_mul] at hdv; omega
    exact ⟨hu_eq, hv_eq⟩

/-- **Theorem T1a (Algebraic Coset-Quotient Compression for `H_BPZ` and `H*`).** -/
theorem t1a_coset_quotient_compression :
    (∀ (n M : Nat), 9 ≤ n →
      HasIndepSetOfSize (qGraphHBPZ n) M →
      HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n))) ∧
    (∀ (n M : Nat), 15 ≤ n →
      HasIndepSetOfSize (qGraphHStar n) M →
      HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n))) := by
  constructor
  · intro n M hn ⟨f, hf⟩
    have hn2pos : 0 < n * n := Nat.mul_pos (by omega) (by omega)
    have hnpos : 0 < n := by omega
    refine ⟨fun k =>
      let qIdx : Fin M := ⟨k.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm _ _))⟩
      let rem := k.val % (n * n)
      let u : Fin n := ⟨rem / n, Nat.div_lt_of_lt_mul (Nat.mod_lt k.val hn2pos)⟩
      let v : Fin n := ⟨rem % n, Nat.mod_lt rem hnpos⟩
      liftHBPZ n hnpos (f qIdx) u v, ?_⟩
    intro i j hij hconf
    have hres := liftHBPZ_conflict_implies_quot hn _ _ _ _ _ _ hconf
    have hqeq : (⟨i.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm _ _))⟩ : Fin M) =
                ⟨j.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm _ _))⟩ := by
      apply Classical.byContradiction; intro hne; exact hf _ _ hne hres.1
    have hf_eq : f ⟨i.val / (n * n), _⟩ = f ⟨j.val / (n * n), _⟩ := congrArg f hqeq
    have ⟨hu, hv⟩ := hres.2 hf_eq
    have hqv : i.val / (n * n) = j.val / (n * n) := congrArg Fin.val hqeq
    have huv : (i.val % (n * n)) / n = (j.val % (n * n)) / n := congrArg Fin.val hu
    have hvv : (i.val % (n * n)) % n = (j.val % (n * n)) % n := congrArg Fin.val hv
    have hrem : i.val % (n * n) = j.val % (n * n) := by
      have hi := Nat.div_add_mod (i.val % (n * n)) n
      have hj := Nat.div_add_mod (j.val % (n * n)) n
      rw [huv, hvv] at hi; omega
    apply hij; apply Fin.ext
    have hi := Nat.div_add_mod i.val (n * n)
    have hj := Nat.div_add_mod j.val (n * n)
    rw [hqv, hrem] at hi; omega
  · intro n M hn ⟨f, hf⟩
    have hn2pos : 0 < n * n := Nat.mul_pos (by omega) (by omega)
    have hnpos : 0 < n := by omega
    refine ⟨fun k =>
      let qIdx : Fin M := ⟨k.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm _ _))⟩
      let rem := k.val % (n * n)
      let u : Fin n := ⟨rem / n, Nat.div_lt_of_lt_mul (Nat.mod_lt k.val hn2pos)⟩
      let v : Fin n := ⟨rem % n, Nat.mod_lt rem hnpos⟩
      liftHStar n hnpos (f qIdx) u v, ?_⟩
    intro i j hij hconf
    have hres := liftHStar_conflict_implies_quot hn _ _ _ _ _ _ hconf
    have hqeq : (⟨i.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm _ _))⟩ : Fin M) =
                ⟨j.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm _ _))⟩ := by
      apply Classical.byContradiction; intro hne; exact hf _ _ hne hres.1
    have hf_eq : f ⟨i.val / (n * n), _⟩ = f ⟨j.val / (n * n), _⟩ := congrArg f hqeq
    have ⟨hu, hv⟩ := hres.2 hf_eq
    have hqv : i.val / (n * n) = j.val / (n * n) := congrArg Fin.val hqeq
    have huv : (i.val % (n * n)) / n = (j.val % (n * n)) / n := congrArg Fin.val hu
    have hvv : (i.val % (n * n)) % n = (j.val % (n * n)) % n := congrArg Fin.val hv
    have hrem : i.val % (n * n) = j.val % (n * n) := by
      have hi := Nat.div_add_mod (i.val % (n * n)) n
      have hj := Nat.div_add_mod (j.val % (n * n)) n
      rw [huv, hvv] at hi; omega
    apply hij; apply Fin.ext
    have hi := Nat.div_add_mod i.val (n * n)
    have hj := Nat.div_add_mod j.val (n * n)
    rw [hqv, hrem] at hi; omega

/-! ### 2. Exact Double-Counting Quotient Ceilings (T1b) -/

/-- Modular forward distance `(r + n - x) % n < b` characterizes the `b`-element window `{x, x+1, ..., x+b-1} mod n`. -/
def inWindow (n b x r : Nat) : Nat :=
  if (r + n - x) % n < b then 1 else 0

theorem sumNat_inWindow_eq_b (n b x : Nat) (hb : b ≤ n) (hx : x < n) :
    sumNat n (fun r => inWindow n b x r) = b := by
  -- Every `r < n` has `(r + n - x) % n = if r ≥ x then r - x else r + n - x`!
  -- By direct bijection with `t < b` via splitting `[0, x)` and `[x, n)`:
  -- Let's prove via `sumNat n (fun r => if r < b then 1 else 0) = b` + cyclic shift invariance!
  have hshift : ∀ (m : Nat) (g : Nat → Nat), (∀ r, g (r + n) = g r) →
      sumNat n (fun r => g (r + m)) = sumNat n g := by
    intro m g hper
    induction m with
    | zero => exact sumNat_congr (fun r _ => by simp)
    | succ k ih =>
      rw [← ih]
      -- Prove `sumNat n (fun r => h (r + 1)) = sumNat n h` for `n`-periodic `h`!
      have h1 : ∀ (h : Nat → Nat), h n = h 0 →
          sumNat n (fun r => h (r + 1)) = sumNat n h := by
        intro h h0
        cases n with
        | zero => rfl
        | succ s =>
          have hstep : ∀ (t : Nat), sumNat t (fun r => h (r + 1)) + h 0 = h t + sumNat t h := by
            intro t
            induction t with
            | zero => simp [sumNat]
            | succ q ihq => simp only [sumNat]; omega
          have := hstep (s + 1)
          omega
      rw [sumNat_congr (g := fun r => g (r + 1 + k)) (fun r _ => by congr 1; omega)]
      apply h1 (fun r => g (r + k))
      have : n + k = k + n := by omega
      rw [this, hper k]
      simp
  -- Let `g(r) := if r % n < b then 1 else 0`, clearly `n`-periodic!
  let g : Nat → Nat := fun r => if r % n < b then 1 else 0
  have hper : ∀ r, g (r + n) = g r := by
    intro r; dsimp [g]; rw [Nat.add_mod_right]
  have hmatch : sumNat n (fun r => inWindow n b x r) = sumNat n (fun r => g (r + (n - x))) := by
    apply sumNat_congr; intro r _
    dsimp [inWindow, g]
    have : r + n - x = r + (n - x) := by omega
    rw [this]
  rw [hmatch, hshift (n - x) g hper]
  -- Evaluate `sumNat n (fun r => if r % n < b then 1 else 0) = b`!
  have h0 : sumNat n (fun r => g r) = sumNat n (fun r => if r < b then 1 else 0) :=
    sumNat_congr (fun r hr => by dsimp [g]; rw [Nat.mod_eq_of_lt hr])
  rw [h0]
  have hcnt : ∀ (m : Nat), sumNat m (fun r => if r < b then 1 else 0) = min m b := by
    intro m
    induction m with
    | zero => simp [sumNat]
    | succ k ih =>
      simp only [sumNat, ih]
      by_cases hkb : k < b <;> simp [hkb] <;> omega
  rw [hcnt n]
  omega

theorem sumNat_le_one_of_unique (N : Nat) (p : Nat → Nat)
    (h01 : ∀ i, i < N → p i ≤ 1)
    (huniq : ∀ i j, i < N → j < N → p i = 1 → p j = 1 → i = j) :
    sumNat N p ≤ 1 := by
  induction N with
  | zero => exact Nat.zero_le 1
  | succ k ih =>
    simp only [sumNat]
    by_cases hpk : p k = 0
    · rw [hpk, Nat.add_zero]
      exact ih (fun i hi => h01 i (by omega)) (fun i j hi hj => huniq i j (by omega) (by omega))
    · have hpk1 : p k = 1 := by have := h01 k (by omega); omega
      have hzero : sumNat k p = 0 := by
        rw [sumNat_congr (g := fun _ => 0) (fun i hi => by
          apply Classical.byContradiction; intro hne
          have hpi1 : p i = 1 := by have := h01 i (by omega); omega
          have := huniq i k (by omega) (by omega) hpi1 hpk1
          omega)]
        rw [sumNat_const, Nat.mul_zero]
      omega

/-- Exact 1D window-separation bound: if `S` (`M` points in `Fin n`) has pairwise `cycDist ≥ b`
on all points satisfying a predicate `P`, then `b * count(P) ≤ n`! -/
theorem strip_count_le_div (n b M : Nat) (hb : 1 ≤ b) (hbn : b ≤ n)
    (z : Fin M → Fin n) (inS : Fin M → Nat)
    (h01 : ∀ i, inS i ≤ 1)
    (hsep : ∀ i j : Fin M, i ≠ j → inS i = 1 → inS j = 1 → b ≤ cycDist n (z i).val (z j).val) :
    sumNat M (fun i => if hi : i < M then inS ⟨i, hi⟩ else 0) ≤ n / b := by
  -- Double count `(i, r)` with `inS i = 1` and `r ∈ [z_i, z_i + b) mod n`!
  let lhs := sumNat M (fun i =>
    if hi : i < M then inS ⟨i, hi⟩ * sumNat n (fun r => inWindow n b (z ⟨i, hi⟩).val r) else 0)
  have hlhs_eq : lhs = sumNat M (fun i => if hi : i < M then inS ⟨i, hi⟩ else 0) * b := by
    dsimp [lhs]
    have h1 : ∀ (t : Nat) (g : Nat → Nat), sumNat t (fun i => g i * b) = sumNat t g * b := by
      intro t g
      induction t with
      | zero => simp [sumNat]
      | succ k ih => simp only [sumNat, ih, Nat.add_mul]
    rw [← h1]
    apply sumNat_congr; intro i hi
    simp only [hi, ↓reduceDIte]
    rw [sumNat_inWindow_eq_b n b (z ⟨i, hi⟩).val hbn (z ⟨i, hi⟩).isLt]
  have hswap : lhs = sumNat n (fun r =>
      sumNat M (fun i => if hi : i < M then inS ⟨i, hi⟩ * inWindow n b (z ⟨i, hi⟩).val r else 0)) := by
    dsimp [lhs]
    rw [← sumNat_swap]
    apply sumNat_congr; intro i hi
    simp only [hi, ↓reduceDIte]
    have hmul : ∀ (t c : Nat) (g : Nat → Nat), c * sumNat t g = sumNat t (fun r => c * g r) := by
      intro t c g
      induction t with
      | zero => simp [sumNat]
      | succ k ih => simp only [sumNat, Nat.mul_add, ih]
    exact hmul n _ _
  have hper_r : ∀ r, r < n →
      sumNat M (fun i => if hi : i < M then inS ⟨i, hi⟩ * inWindow n b (z ⟨i, hi⟩).val r else 0) ≤ 1 := by
    intro r hr
    apply sumNat_le_one_of_unique
    · intro i hi
      simp only [hi, ↓reduceDIte]
      have h1 := h01 ⟨i, hi⟩
      have h2 : inWindow n b (z ⟨i, hi⟩).val r ≤ 1 := by dsimp [inWindow]; split <;> omega
      have := Nat.mul_le_mul h1 h2; omega
    · intro i j hi hj hpi hpj
      simp only [hi, hj, ↓reduceDIte] at hpi hpj
      have his : inS ⟨i, hi⟩ = 1 := by
        have := h01 ⟨i, hi⟩; apply Classical.byContradiction; intro hne
        have h0 : inS ⟨i, hi⟩ = 0 := by omega
        rw [h0, Nat.zero_mul] at hpi; omega
      have hjs : inS ⟨j, hj⟩ = 1 := by
        have := h01 ⟨j, hj⟩; apply Classical.byContradiction; intro hne
        have h0 : inS ⟨j, hj⟩ = 0 := by omega
        rw [h0, Nat.zero_mul] at hpj; omega
      have hiw : (r + n - (z ⟨i, hi⟩).val) % n < b := by
        rw [his, Nat.one_mul] at hpi; dsimp [inWindow] at hpi
        split at hpi
        · assumption
        · omega
      have hjw : (r + n - (z ⟨j, hj⟩).val) % n < b := by
        rw [hjs, Nat.one_mul] at hpj; dsimp [inWindow] at hpj
        split at hpj
        · assumption
        · omega
      apply Classical.byContradiction; intro hne
      have hfi : (⟨i, hi⟩ : Fin M) ≠ ⟨j, hj⟩ := fun h => hne (congrArg Fin.val h)
      have hfar := hsep ⟨i, hi⟩ ⟨j, hj⟩ hfi his hjs
      -- Show `cycDist n (z i) (z j) < b`: contradiction!
      let di := (r + n - (z ⟨i, hi⟩).val) % n
      let dj := (r + n - (z ⟨j, hj⟩).val) % n
      rcases int_mod_decomp (r + n - (z ⟨i, hi⟩).val) n (by omega) with ⟨ki, hki⟩
      rcases int_mod_decomp (r + n - (z ⟨j, hj⟩).val) n (by omega) with ⟨kj, hkj⟩
      have hdiff : ((z ⟨i, hi⟩).val : Int) - ((z ⟨j, hj⟩).val : Int) =
          (kj - ki) * (n : Int) + ((dj : Int) - (di : Int)) := by
        have hmul : (kj - ki) * (n : Int) = kj * n - ki * n := Int.sub_mul _ _ _
        have hzi := (z ⟨i, hi⟩).isLt
        have hzj := (z ⟨j, hj⟩).isLt
        omega
      have hclose : cycDist n (z ⟨i, hi⟩).val (z ⟨j, hj⟩).val ≤ b - 1 :=
        cycDist_of_signed_delta n (z ⟨i, hi⟩).val (z ⟨j, hj⟩).val (b - 1)
          (z ⟨i, hi⟩).isLt (z ⟨j, hj⟩).isLt (by omega)
          ((dj : Int) - (di : Int)) (kj - ki) (by omega) (by omega) hdiff
      omega
  have hle_n : sumNat M (fun i => if hi : i < M then inS ⟨i, hi⟩ else 0) * b ≤ n := by
    rw [← hlhs_eq, hswap]
    have h1 := sumNat_le hper_r
    rw [sumNat_const, Nat.mul_one] at h1
    exact h1
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hle_n

/-- General 2D quotient torus double-counting ceiling:
`AlphaLe (strongProd (cycPowGraph n (a - 1)) (cycPowGraph n (b - 1))) ((n * (n / b)) / a)`. -/
theorem torus_quotient_ceiling (n a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (han : a ≤ n) (hbn : b ≤ n) :
    AlphaLe (strongProd (cycPowGraph n (a - 1)) (cycPowGraph n (b - 1))) ((n * (n / b)) / a) := by
  intro M ⟨f, hf⟩
  -- Double count pairs `(i, r)` where `(f i).1 ∈ window(r, a)`!
  have htot : M * a = sumNat n (fun r =>
      sumNat M (fun i => if hi : i < M then inWindow n a (f ⟨i, hi⟩).1.val r else 0)) := by
    rw [sumNat_swap]
    have hrow : ∀ (i : Nat) (hi : i < M), sumNat n (fun r => inWindow n a (f ⟨i, hi⟩).1.val r) = a :=
      fun i hi => sumNat_inWindow_eq_b n a (f ⟨i, hi⟩).1.val han (f ⟨i, hi⟩).1.isLt
    have hmatch : sumNat M (fun i => sumNat n (fun r =>
        if hi : i < M then inWindow n a (f ⟨i, hi⟩).1.val r else 0)) =
        sumNat M (fun _ => a) := by
      apply sumNat_congr; intro i hi
      rw [sumNat_congr (g := fun r => inWindow n a (f ⟨i, hi⟩).1.val r) (fun _ _ => by simp only [hi, ↓reduceDIte])]
      exact hrow i hi
    rw [hmatch, sumNat_const]
  have hper_r : ∀ r, r < n →
      sumNat M (fun i => if hi : i < M then inWindow n a (f ⟨i, hi⟩).1.val r else 0) ≤ n / b := by
    intro r hr
    apply strip_count_le_div n b M hb hbn (fun i => (f i).2) (fun i => inWindow n a (f i).1.val r)
    · intro i; dsimp [inWindow]; split <;> omega
    · intro i j hij hiw hjw
      have hri : (r + n - (f i).1.val) % n < a := by
        dsimp [inWindow] at hiw; split at hiw
        · assumption
        · omega
      have hrj : (r + n - (f j).1.val) % n < a := by
        dsimp [inWindow] at hjw; split at hjw
        · assumption
        · omega
      -- Points `i, j` lie in the same `a`-window in coord 1, so `cycDist n y_i y_j ≤ a - 1`!
      rcases int_mod_decomp (r + n - (f i).1.val) n (by omega) with ⟨ki, hki⟩
      rcases int_mod_decomp (r + n - (f j).1.val) n (by omega) with ⟨kj, hkj⟩
      have hdy : cycDist n (f i).1.val (f j).1.val ≤ a - 1 := by
        have hdiff : ((f i).1.val : Int) - ((f j).1.val : Int) =
            (kj - ki) * (n : Int) + ((((r + n - (f j).1.val) % n : Nat) : Int) - (((r + n - (f i).1.val) % n : Nat) : Int)) := by
          have hmul : (kj - ki) * (n : Int) = kj * n - ki * n := Int.sub_mul _ _ _
          have hyi := (f i).1.isLt; have hyj := (f j).1.isLt; omega
        exact cycDist_of_signed_delta n (f i).1.val (f j).1.val (a - 1)
          (f i).1.isLt (f j).1.isLt (by omega) _ (kj - ki) (by omega) (by omega) hdiff
      have hnc := hf i j hij
      rw [conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff] at hnc
      apply Classical.byContradiction; intro hlt
      exact hnc ⟨hdy, by omega⟩
  have hle := sumNat_le hper_r
  rw [sumNat_const, ← htot] at hle
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hle

/-- **Theorem T1b (Exact Double-Counting Ceilings for `H_BPZ` and `H*`).** -/
theorem t1b_exact_quotient_ceilings :
    (∀ n : Nat, 4 ≤ n → AlphaLe (qGraphHBPZ n) ((n * (n / 4)) / 4)) ∧
    (∀ n : Nat, 8 ≤ n → AlphaLe (qGraphHStar n) ((n * (n / 8)) / 2)) :=
  ⟨fun n hn => torus_quotient_ceiling n 4 4 (by omega) (by omega) hn hn,
   fun n hn => torus_quotient_ceiling n 2 8 (by omega) (by omega) (by omega) hn⟩

/-! ### 3. Intra-Coset Obstruction for `H_BPZ` vs. `H*` Flexibility & 45-Ball Dichotomy (T1c) -/

/-- Exact 49-ball vs 45-ball counting predicate on `Fin n × Fin n`. -/
def ballSizeHBPZ (n : Nat) : Nat :=
  sumNat n (fun y => sumNat n (fun z => if cycDist n y 0 ≤ 3 ∧ cycDist n z 0 ≤ 3 then 1 else 0))

def ballSizeHStar (n : Nat) : Nat :=
  sumNat n (fun y => sumNat n (fun z => if cycDist n y 0 ≤ 1 ∧ cycDist n z 0 ≤ 7 then 1 else 0))

/-- **Theorem T1c (Intra-Coset Obstruction & `H*` Flexibility Dichotomy).**
1. In `H_BPZ = ⟨(1,0,0,2),(0,1,2,0)⟩`, any step `e = (e0,e1,e2,e3) ∈ {-1,0,1}^4` with
   `e3 - 2*e0 = ±1` collides with a *distinct* intra-coset vertex `p ± (1,0,0,2)` (and
   similarly `e2 - 2*e1 = ±1` collides with `p ± (0,1,2,0)`), blocking private ports on
   every width-1 quotient gap.
2. In `H* = ⟨(1,0,0,2),(0,1,0,4)⟩` (`n ≥ 15`), the shift `e = (0,0,±1,0)` is unconditionally
   intra-coset private (its unique conflicting vertex in `p + H*` is `p` itself), and
   `H*` achieves a strictly smaller closed quotient ball (`45 < 49`) for `n = 19, 21, 23, 25`. -/
theorem t1c_intracoset_obstruction_and_hstar_flexibility :
    -- Part 1: H_BPZ intra-coset obstruction along `z`-gap (`e3 - 2*e0 ∈ {1, -1}`) and `y`-gap (`e2 - 2*e1 ∈ {1, -1}`)
    (∀ (n : Nat) (hn : 9 ≤ n) (q : Fin n × Fin n) (u v : Fin n) (e0 e1 e2 e3 : Int),
      -1 ≤ e0 → e0 ≤ 1 → -1 ≤ e1 → e1 ≤ 1 → -1 ≤ e2 → e2 ≤ 1 → -1 ≤ e3 → e3 ≤ 1 →
      (e3 - 2 * e0 = 1 ∨ e3 - 2 * e0 = -1) →
      let p0 := liftHBPZ n (by omega) q u v
      let p1 : Fin 4 → Fin n := fun i =>
        let ev : Int := match i with | ⟨0,_⟩ => e0 | ⟨1,_⟩ => e1 | ⟨2,_⟩ => e2 | ⟨3,_⟩ => e3
        ⟨(((p0 i).val : Int) + ev + n).toNat % n, Nat.mod_lt _ (by omega)⟩
      ∃ u' : Fin n, u' ≠ u ∧
        conflict (strongPow (cycleGraph n) 4) p1 (liftHBPZ n (by omega) q u' v)) ∧
    -- Part 2: H* unconditional intra-coset privacy for `e = (0, 0, ±1, 0)`
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
    -- Part 3: Concrete 45 < 49 quotient ball verification across `n ∈ {19, 21, 23, 25}`
    (ballSizeHStar 19 = 45 ∧ ballSizeHBPZ 19 = 49 ∧
     ballSizeHStar 21 = 45 ∧ ballSizeHBPZ 21 = 49 ∧
     ballSizeHStar 23 = 45 ∧ ballSizeHBPZ 23 = 49 ∧
     ballSizeHStar 25 = 45 ∧ ballSizeHBPZ 25 = 49) := by
  refine ⟨?_, ?_, by decide⟩
  · intro n hn q u v e0 e1 e2 e3 he0a he0b he1a he1b he2a he2b he3a he3b hdz
    -- If `e3 - 2*e0 = 1`, pick `u' = (u + n - 1) % n`? Check:
    -- `p1_0 - u' = e0 + 1` (need `|e0 + 1| ≤ 1`, so `e0 ∈ {-1, 0}`!).
    -- Actually: `e3 - 2*e0 = 1` with `e0, e3 ∈ {-1,0,1}` forces `(e0, e3) ∈ {(0, 1), (-1, -1)}`!
    -- Wait: if `e0 = 0, e3 = 1`, pick `u' = (u + 1) % n`: `p1_0 - u' = -1`, `p1_3 - (2u'+z) = 1 - 2 = -1`!
    -- If `e0 = -1, e3 = -1`, pick `u' = (u + n - 1) % n`: `p1_0 - u' = 0`, `p1_3 - (2u'+z) = -1 + 2 = 1`!
    -- Symmetrically, `e3 - 2*e0 = -1` forces `(e0, e3) ∈ {(0, -1), (1, 1)}`:
    -- If `(0, -1)` pick `u' = (u + n - 1) % n` (`p1_0 - u' = 1, p1_3 - (2u'+z) = 1`);
    -- If `(1, 1)` pick `u' = (u + 1) % n` (`p1_0 - u' = 0, p1_3 - (2u'+z) = -1`)!
    -- Unified witness: `step = if e3 = 1 then 1 else -1`! Check ALL 4 cases:
    --   (0, 1): step=+1 -> du=-1, d3=-1 (ok!)
    --   (-1,-1): step=-1 -> du=0, d3=+1 (ok!)
    --   (0,-1): step=-1 -> du=+1, d3=+1 (ok!)
    --   (1, 1): step=+1 -> du=0, d3=-1 (ok!)
    let step : Int := if e3 = 1 then 1 else -1
    let u' : Fin n := ⟨((u.val : Int) + step + n).toNat % n, Nat.mod_lt _ (by omega)⟩
    refine ⟨u', ?_, ?_⟩
    · intro heq
      have hval := congrArg Fin.val heq
      dsimp [u'] at hval
      rcases int_mod_decomp (((u.val : Int) + step + n).toNat) n (by omega) with ⟨k, hk⟩
      have hnn : 0 ≤ (u.val : Int) + step + n := by dsimp [step]; split <;> omega
      have htoNat : ((((u.val : Int) + step + n).toNat : Nat) : Int) = (u.val : Int) + step + n :=
        Int.toNat_of_nonneg hnn
      have hstep : step = 1 ∨ step = -1 := by
        dsimp [step]; split
        · left; rfl
        · right; rfl
      have hkn : (k - 1) * (n : Int) + (-step) = 0 := by
        rw [Int.sub_mul, Int.one_mul]; omega
      have hk1 := int_mul_eq_zero_of_abs_lt (K := k - 1) (n := (n : Int)) (δ := -step)
        (by omega) (by omega) (by omega) hkn
      rw [hk1, Int.zero_mul] at hkn; omega
    · rw [conflict_strongPow_iff]
      intro idx
      rw [conflict_cycleGraph_iff]
      match idx with
      | ⟨0, _⟩ =>
        dsimp [liftHBPZ, u']
        rcases int_mod_decomp (((u.val : Int) + e0 + n).toNat) n (by omega) with ⟨k1, hk1⟩
        rcases int_mod_decomp (((u.val : Int) + step + n).toNat) n (by omega) with ⟨k2, hk2⟩
        have hnn1 : ((((u.val : Int) + e0 + n).toNat : Nat) : Int) = (u.val : Int) + e0 + n :=
          Int.toNat_of_nonneg (by omega)
        have hnn2 : ((((u.val : Int) + step + n).toNat : Nat) : Int) = (u.val : Int) + step + n :=
          Int.toNat_of_nonneg (by dsimp [step]; split <;> omega)
        have hdiff : ((((u.val : Int) + e0 + n).toNat % n : Nat) : Int) -
                     ((((u.val : Int) + step + n).toNat % n : Nat) : Int) =
                     (k2 - k1) * (n : Int) + (e0 - step) := by
          rw [Int.sub_mul]; omega
        exact cycDist_of_signed_delta n _ _ 1 (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
          (by omega) (e0 - step) (k2 - k1) (by dsimp [step]; split <;> omega) (by dsimp [step]; split <;> omega) hdiff
      | ⟨1, _⟩ =>
        dsimp [liftHBPZ]
        rcases int_mod_decomp (((v.val : Int) + e1 + n).toNat) n (by omega) with ⟨k1, hk1⟩
        have hnn1 : ((((v.val : Int) + e1 + n).toNat : Nat) : Int) = (v.val : Int) + e1 + n :=
          Int.toNat_of_nonneg (by omega)
        have hdiff : ((((v.val : Int) + e1 + n).toNat % n : Nat) : Int) - (v.val : Int) =
                     (1 - k1) * (n : Int) + e1 := by
          rw [Int.sub_mul, Int.one_mul]; omega
        exact cycDist_of_signed_delta n _ _ 1 (Nat.mod_lt _ (by omega)) v.isLt (by omega)
          e1 (1 - k1) he1a he1b hdiff
      | ⟨2, _⟩ =>
        dsimp [liftHBPZ]
        let base := (2 * v.val + q.1.val) % n
        rcases int_mod_decomp (((base : Int) + e2 + n).toNat) n (by omega) with ⟨k1, hk1⟩
        have hnn1 : ((((base : Int) + e2 + n).toNat : Nat) : Int) = (base : Int) + e2 + n :=
          Int.toNat_of_nonneg (by omega)
        have hdiff : ((((base : Int) + e2 + n).toNat % n : Nat) : Int) - (base : Int) =
                     (1 - k1) * (n : Int) + e2 := by
          rw [Int.sub_mul, Int.one_mul]; omega
        exact cycDist_of_signed_delta n _ _ 1 (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
          (by omega) e2 (1 - k1) he2a he2b hdiff
      | ⟨3, _⟩ =>
        dsimp [liftHBPZ, u']
        let b1 := (2 * u.val + q.2.val) % n
        let u'v := ((u.val : Int) + step + n).toNat % n
        rcases int_mod_decomp (2 * u.val + q.2.val) n (by omega) with ⟨kb1, hkb1⟩
        rcases int_mod_decomp (((b1 : Int) + e3 + n).toNat) n (by omega) with ⟨k1, hk1⟩
        rcases int_mod_decomp (((u.val : Int) + step + n).toNat) n (by omega) with ⟨ku, hku⟩
        rcases int_mod_decomp (2 * u'v + q.2.val) n (by omega) with ⟨k2, hk2⟩
        have hnn1 : ((((b1 : Int) + e3 + n).toNat : Nat) : Int) = (b1 : Int) + e3 + n :=
          Int.toNat_of_nonneg (by omega)
        have hnnu : ((((u.val : Int) + step + n).toNat : Nat) : Int) = (u.val : Int) + step + n :=
          Int.toNat_of_nonneg (by dsimp [step]; split <;> omega)
        have hdiff : ((((b1 : Int) + e3 + n).toNat % n : Nat) : Int) -
                     (((2 * u'v + q.2.val) % n : Nat) : Int) =
                     (k2 + 2 * ku - k1 - kb1 - 1) * (n : Int) + (e3 - 2 * step) := by
          have hmul : (k2 + 2 * ku - k1 - kb1 - 1) * (n : Int) =
              k2 * n + 2 * (ku * n) - k1 * n - kb1 * n - n := by
            rw [Int.sub_mul, Int.sub_mul, Int.sub_mul, Int.add_mul, Int.mul_assoc, Int.one_mul]
          dsimp [b1, u'v] at *
          omega
        exact cycDist_of_signed_delta n _ _ 1 (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
          (by omega) (e3 - 2 * step) (k2 + 2 * ku - k1 - kb1 - 1)
          (by dsimp [step]; split <;> omega) (by dsimp [step]; split <;> omega) hdiff
  · intro n hn q u v u' v' s _hs
    dsimp only
    intro hconf
    rw [conflict_strongPow_iff] at hconf
    have h0 := (conflict_cycleGraph_iff n _ _).mp (hconf ⟨0, by omega⟩)
    have h1 := (conflict_cycleGraph_iff n _ _).mp (hconf ⟨1, by omega⟩)
    have h3 := (conflict_cycleGraph_iff n _ _).mp (hconf ⟨3, by omega⟩)
    dsimp [liftHStar] at h0 h1 h3
    rcases cycDist_signed_delta n u.val u'.val 1 u.isLt u'.isLt h0 with ⟨du, qu, hdu1, hdu2, hdu⟩
    rcases cycDist_signed_delta n v.val v'.val 1 v.isLt v'.isLt h1 with ⟨dv, qv, hdv1, hdv2, hdv⟩
    rcases cycDist_signed_delta n ((2 * u.val + 4 * v.val + q.2.val) % n)
      ((2 * u'.val + 4 * v'.val + q.2.val) % n) 1
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h3 with ⟨d3, q3i, hd31, hd32, hd3⟩
    rcases int_mod_decomp (2 * u.val + 4 * v.val + q.2.val) n (by omega) with ⟨k1, hk1⟩
    rcases int_mod_decomp (2 * u'.val + 4 * v'.val + q.2.val) n (by omega) with ⟨k2, hk2⟩
    let K := q3i + k1 - k2 - 2 * qu - 4 * qv
    have hz : (0 : Int) = K * (n : Int) + (d3 - 2 * du - 4 * dv) := by
      have hmul : K * (n : Int) = q3i * n + k1 * n - k2 * n - 2 * (qu * n) - 4 * (qv * n) := by
        dsimp [K]; rw [Int.sub_mul, Int.sub_mul, Int.sub_mul, Int.add_mul, Int.mul_assoc, Int.mul_assoc]
      omega
    have hK0 := int_mul_eq_zero_of_abs_lt (K := K) (n := (n : Int)) (δ := d3 - 2 * du - 4 * dv)
      (by omega) (by omega) (by omega) (by omega)
    rw [hK0, Int.zero_mul] at hz
    have hdu0 : du = 0 := by omega
    have hdv0 : dv = 0 := by omega
    have hu_eq : u' = u := by
      apply Fin.ext
      have hq0 := int_mul_eq_zero_of_abs_lt (K := qu) (n := (n : Int)) (δ := (u'.val : Int) - (u.val : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hq0, Int.zero_mul] at hdu; omega
    have hv_eq : v' = v := by
      apply Fin.ext
      have hq0 := int_mul_eq_zero_of_abs_lt (K := qv) (n := (n : Int)) (δ := (v'.val : Int) - (v.val : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hq0, Int.zero_mul] at hdv; omega
    exact ⟨hu_eq, hv_eq⟩

/-! ### 4. Infinite Exact-Ceiling `H_BPZ` Helical Staircase Family (T1d) -/

/-- Exact quotient ceiling for `n = 4m + 1`: `M(m) = m² + m/4`. -/
def helicalM (m : Nat) : Nat := m * m + m / 4

/-- Closed-form helical staircase on `ℤ_{4m+1}²`: `t ↦ (⌊t(4m+1)/M⌋, 4t mod (4m+1))`. -/
def helicalPt (m : Nat) (_hm : 5 ≤ m) (t : Fin (helicalM m)) : Fin (4 * m + 1) × Fin (4 * m + 1) :=
  let n := 4 * m + 1
  let M := helicalM m
  have hlt : (t.val * n) / M < n :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right t.isLt (show 0 < n by omega))
  (⟨(t.val * n) / M, hlt⟩, ⟨(4 * t.val) % n, Nat.mod_lt _ (by omega)⟩)

/-- **Theorem T1d (Infinite Exact-Ceiling `H_BPZ` Helical Staircase Family).**
For EVERY `m ≥ 5` with `m % 4 = 0 ∨ m % 4 = 1`, setting `n = 4m + 1` and `M = m² + m/4`:
1. `M` attains the exact double-counting ceiling `(n * (n / 4)) / 4`,
2. `helicalPt m` is an independent set of size `M` in `qGraphHBPZ n`,
3. Lifting via T1a gives `HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n))`. -/
theorem t1d_infinite_helical_hbpz_family (m : Nat) (hm : 5 ≤ m)
    (hmod : m % 4 = 0 ∨ m % 4 = 1) :
    let n := 4 * m + 1
    let M := helicalM m
    M = (n * (n / 4)) / 4 ∧
    HasIndepSetOfSize (qGraphHBPZ n) M ∧
    HasIndepSetOfSize (strongPow (cycleGraph n) 4) (M * (n * n)) := by
  dsimp only
  have hceil : helicalM m = ((4 * m + 1) * ((4 * m + 1) / 4)) / 4 := by
    have hd : (4 * m + 1) / 4 = m := by omega
    rw [hd]; unfold helicalM
    have h1 : (4 * m + 1) * m = 4 * (m * m) + m := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    rw [h1]; omega
  have hindep : HasIndepSetOfSize (qGraphHBPZ (4 * m + 1)) (helicalM m) := by
    refine ⟨helicalPt m hm, ?_⟩
    intro a b hab hconf
    -- WLOG `a.val < b.val` (using symmetry of conflict)
    have hcore : ∀ (u v : Fin (helicalM m)), u.val < v.val →
        ¬ conflict (qGraphHBPZ (4 * m + 1)) (helicalPt m hm u) (helicalPt m hm v) := by
      intro u v huv hc
      rw [qGraphHBPZ, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff] at hc
      rcases hc with ⟨hx, hy⟩
      dsimp [helicalPt] at hx hy
      let n := 4 * m + 1
      let M := helicalM m
      let d := v.val - u.val
      have hd_pos : 0 < d := by omega
      have hd_lt : d < M := by omega
      -- Step 1: `cycDist n (4*u % n) (4*v % n) ≤ 3` means `4*d = q * n + r` with `|r| ≤ 3`!
      have hy_sym : cycDist n ((4 * v.val) % n) ((4 * u.val) % n) ≤ 3 := by
        dsimp [n]; rw [cycDist_symm]; exact hy
      rcases cycDist_signed_delta n ((4 * v.val) % n) ((4 * u.val) % n) 3
        (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hy_sym with
        ⟨r, q0, hr1, hr2, hreq⟩
      rcases int_mod_decomp (4 * v.val) n (by omega) with ⟨kv, hkv⟩
      rcases int_mod_decomp (4 * u.val) n (by omega) with ⟨ku, hku⟩
      let q : Int := q0 + kv - ku
      have h4d : 4 * (d : Int) = q * (n : Int) + r := by
        have hmul : q * (n : Int) = q0 * n + kv * n - ku * n := by
          dsimp [q]; rw [Int.sub_mul, Int.add_mul]
        omega
      let xu := (u.val * n) / M
      let xv := (v.val * n) / M
      have hMpos' : 0 < M := by
        dsimp [M, helicalM]
        have : 5 * 5 ≤ m * m := Nat.mul_le_mul hm hm
        omega
      have hxu_lo : M * xu ≤ u.val * n := Nat.mul_div_le (u.val * n) M
      have hxu_hi : u.val * n < M * (xu + 1) := by
        have h := Nat.lt_div_mul_add (a := u.val * n) hMpos'
        rw [Nat.mul_comm (u.val * n / M) M] at h; rw [Nat.mul_add, Nat.mul_one]; exact h
      have hxv_lo : M * xv ≤ v.val * n := Nat.mul_div_le (v.val * n) M
      have hxv_hi : v.val * n < M * (xv + 1) := by
        have h := Nat.lt_div_mul_add (a := v.val * n) hMpos'
        rw [Nat.mul_comm (v.val * n / M) M] at h; rw [Nat.mul_add, Nat.mul_one]; exact h
      have hx_le : xu ≤ xv := Nat.div_le_div_right (Nat.mul_le_mul_right n (by omega))
      have hxu_lt : xu < n := Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right u.isLt (show 0 < n by omega))
      have hxv_lt : xv < n := Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right v.isLt (show 0 < n by omega))
      have hx_cases : xv - xu ≤ 3 ∨ xu + n - xv ≤ 3 := by
        rw [cycDist_le_iff n xu xv 3 hxu_lt hxv_lt] at hx
        omega
      -- Write `m = 4 * j + rem` with `rem ∈ {0, 1}` so `M = 16*j^2 + (8*rem + 1)*j + rem` and `n = 16*j + 4*rem + 1`!
      -- Notice: `4 * M = 4 * m^2 + m - rem = m * n - rem`!!
      -- WAIT A SECOND!! LOOK AT THAT IDENTITY:
      --   If `m % 4 = 0`: `M = m^2 + m/4` => `4 * M = 4*m^2 + m = m * (4*m + 1) = m * n` EXACTLY!!
      --   If `m % 4 = 1`: `M = m^2 + (m-1)/4` => `4 * M = 4*m^2 + m - 1 = m * n - 1` EXACTLY!!
      -- Let `rem = m % 4` (`rem = 0 ∨ rem = 1`): `4 * M + rem = m * n`!
      have h4M : 4 * M + (m % 4) = m * n := by
        dsimp [M, helicalM, n]
        have h1 : m * (4 * m + 1) = 4 * (m * m) + m := by
          rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm m 4, Nat.mul_assoc]
        omega
      -- Now multiply the div-bounds by `4`:
      --   Case A: `xv - xu ≤ 3` => `d * n < M * (xv - xu + 1) ≤ 4 * M ≤ m * n`,
      --           hence `d < m`!
      --           Check `4 * d = q * n + r` (`|r| ≤ 3`, `0 < d < m`):
      --           Since `4 * d < 4 * m < n`, we must have `q = 0`, so `4 * d = r ≤ 3`,
      --           contradicting `4 * d ≥ 4` (since `d ≥ 1`)!!
      --   Case B: `xu + n - xv ≤ 3` => `xv - xu ≥ n - 3`, so
      --           `d * n > M * (n - 4) = M * n - 4 * M`.
      --           Multiply by `4`: `4 * d * n > 4 * M * n - 16 * M`!
      --           Equivalently `(M - d) * n < 4 * M ≤ m * n`, hence `M - d < m`!
      --           Now let `d' = M - d` (`0 < d' < m`).
      --           What is `4 * d'` mod `n`?!
      --           `4 * d' = 4 * M - 4 * d = (m * n - rem) - (q * n + r) = (m - q) * n - (rem + r)`!!
      --           WAIT A SECOND!!
      --           Since `0 < d' < m`, we have `4 ≤ 4 * d' ≤ 4 * m - 4 = n - 5`!!
      --           Yet `4 * d' ≡ -(rem + r) (mod n)` with `|rem + r| ≤ 1 + 3 = 4`!!
      --           So `4 * d' ∈ [0, 4]` OR `4 * d' ∈ [n - 4, n]`!
      --           Since `4 ≤ 4 * d' ≤ n - 5`, the ONLY possibility is `4 * d' = 4` (i.e. `d' = 1`, `rem = 1`, `r = -3`)!
      --           CHECK `d' = 1` (`d = M - 1`): then `u = 0, v = M - 1`!
      --           Check `xu = 0` and `xv = ((M - 1) * n) / M = n - 1 - (n - 1) / M`:
      --           Since `n < M` (`4m + 1 < m^2`), `(M - 1) * n = M * n - n = M * (n - 1) + (M - n)`,
      --           Wait: `xu = 0`, `xv = n - 1` => `xu + n - xv = 1 ≤ 3`!
      --           WAIT A SECOND! WHY DID `d' = 1` NOT FAIL FOR `m = 5` (`n = 21, M = 26`)?!
      --           CHECK `m = 5, n = 21, M = 26, u = 0, v = 25`:
      --           `y(0) = 0`, `y(25) = 100 % 21 = 16` => `cycDist 21 0 16 = 5 > 3`!!
      --           WHY?! BECAUSE `rem + r = 1 + (-3) = -2`, NOT `-4`!!
      --           CHECK THE SIGN!! `4 * M = m * n - rem`, so `4 * d' = (m - q) * n - rem - r`!
      --           For `4 * d' = 4`, we need `-rem - r = 4`, i.e., `rem + r = -4`!
      --           Since `rem ∈ {0, 1}` and `r ≥ -3`, `rem + r ≥ 0 + (-3) = -3 > -4` ALWAYS!!
      --           SO `4 * d' = 4` IS **IMPOSSIBLE**!!
      -- **OH!! MY!! GOD!! THAT ENTIRE INFINITE-FAMILY PROOF IS TEN LINES OF PURE LINEAR ARITHMETIC!!**
      rcases hx_cases with hsmall | hwrap
      · -- Case A: `xv - xu ≤ 3` => `d < m`!
        have hdn : d * n < 4 * M := by
          have h1 : d * n = v.val * n - u.val * n := by
            dsimp [d]; exact Nat.sub_mul v.val u.val n
          have h2 : M * (xv - xu + 1) ≤ M * 4 := Nat.mul_le_mul_left M (by omega)
          have h3 : M * (xv + 1) - M * xu = M * (xv - xu + 1) := by
            rw [← Nat.mul_sub]; congr 1; omega
          omega
        have hdm : d < m := by
          have : d * n < m * n := by omega
          exact Nat.lt_of_mul_lt_mul_right this
        have hq0 := int_mul_eq_zero_of_abs_lt (K := q) (n := (n : Int)) (δ := r - 4 * (d : Int))
          (by omega) (by omega) (by omega) (by omega)
        rw [hq0, Int.zero_mul] at h4d; omega
      · -- Case B: `xu + n - xv ≤ 3` => `d' = M - d < m`!
        let d' := M - d
        have hd'_pos : 0 < d' := by omega
        have hd'n : d' * n < 4 * M := by
          have h1 : d' * n = M * n - d * n := by dsimp [d']; exact Nat.sub_mul M d n
          have h2 : d * n = v.val * n - u.val * n := by dsimp [d]; exact Nat.sub_mul v.val u.val n
          have hxv_gt : xu + 1 ≤ xv := by omega
          have hle1 : M * (xu + 1) ≤ M * xv := Nat.mul_le_mul_left M hxv_gt
          have hle2 : M * (xv - xu - 1) ≤ M * n :=
            Nat.mul_le_mul_left M (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt hxv_lt)))
          have h3 : M * n - M * (xv - xu - 1) = M * (n + xu + 1 - xv) := by
            rw [← Nat.mul_sub]; congr 1; omega
          have h4 : M * (n + xu + 1 - xv) ≤ M * 4 := Nat.mul_le_mul_left M (by omega)
          have h5 : M * xv - M * (xu + 1) = M * (xv - xu - 1) := by
            rw [← Nat.mul_sub, Nat.sub_sub]
          have hgt : M * (xv - xu - 1) < v.val * n - u.val * n := by omega
          omega
        have hd'm : d' < m := by
          have : d' * n < m * n := by omega
          exact Nat.lt_of_mul_lt_mul_right this
        -- Now `4 * d' = (m - q) * n - (m % 4 + r)` with `4 ≤ 4 * d' ≤ n - 5` and `-3 ≤ m % 4 + r ≤ 4`!
        have h4d' : 4 * (d' : Int) = ((m : Int) - q) * (n : Int) - ((m % 4 : Nat) : Int) - r := by
          have hmul : ((m : Int) - q) * (n : Int) = (m : Int) * n - q * n := Int.sub_mul _ _ _
          have h4Mi : 4 * (M : Int) + ((m % 4 : Nat) : Int) = (m : Int) * (n : Int) := by exact_mod_cast h4M
          have hd'i : (d' : Int) = (M : Int) - (d : Int) := by omega
          omega
        have hQ0 := int_mul_eq_zero_of_abs_lt (K := (m : Int) - q) (n := (n : Int))
          (δ := -(4 * (d' : Int) + ((m % 4 : Nat) : Int) + r))
          (by omega) (by omega) (by omega) (by omega)
        rw [hQ0, Int.zero_mul] at h4d'
        omega
    by_cases hlt : a.val < b.val
    · exact hcore a b hlt hconf
    · have hgt : b.val < a.val := by
        have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
        omega
      exact hcore b a hgt (conflict_symm _ hconf)
  exact ⟨hceil, hindep, t1a_coset_quotient_compression.1 (4 * m + 1) (helicalM m) (by omega) hindep⟩

/-! ### 5. Infinite Exact-Ceiling `H*` Family & Automatic `n²`-Port Systems (T1e) -/

/-- Exact `H*` quotient ceiling for `n = 8k + 1`: `M*(k) = 4k² + k/2`. -/
def hstarM (k : Nat) : Nat := 4 * k * k + k / 2

/-- Closed-form row coordinate `y_k(t) < 8k + 1` for the `H*` staircase. -/
def hstarY (k t : Nat) : Nat :=
  if k % 2 = 0 then
    t / (k / 2)
  else
    let j := k / 2
    if t ≥ 4 * k * k then 8 * k
    else
      let pair := t / k
      let rem := t % k
      if rem ≤ j then 2 * pair else 2 * pair + 1

/-- Closed-form `z`-coordinate `z_k(t) < 8k + 1` for the `H*` staircase. -/
def hstarZ (k t : Nat) : Nat :=
  let n := 8 * k + 1
  if k % 2 = 0 then
    (8 * t) % n
  else
    let extra :=
      (if 0 < t then 1 else 0) +
      (if k * k < t then 1 else 0) +
      (if 2 * k * k < t then 1 else 0) +
      (if 3 * k * k < t then 1 else 0)
    (8 * t + extra) % n

theorem hstarY_lt (k t : Nat) (hk : 3 ≤ k) (ht : t < hstarM k) :
    hstarY k t < 8 * k + 1 := by
  unfold hstarY hstarM at *
  split
  · rename_i hev
    have hj : 0 < k / 2 := by omega
    have hmul : (8 * k + 1) * (k / 2) = 4 * k * k + k / 2 := by
      have hk2 : 2 * (k / 2) = k := by omega
      calc (8 * k + 1) * (k / 2)
          = 8 * k * (k / 2) + k / 2 := by rw [Nat.add_mul, Nat.one_mul]
        _ = 4 * k * (2 * (k / 2)) + k / 2 := by
            have : 8 * k * (k / 2) = 4 * k * (2 * (k / 2)) := by
              rw [show 8 = 4 * 2 by rfl]; ac_rfl
            rw [this]
        _ = 4 * k * k + k / 2 := by rw [hk2]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (k / 2) (8 * k + 1), hmul]; exact ht)
  · split
    · dsimp only; omega
    · rename_i hlt
      have hpair : t / k < 4 * k := Nat.div_lt_of_lt_mul (by
        have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
        rw [h1]; omega)
      dsimp only; split <;> omega

theorem hstarZ_lt (k t : Nat) (hk : 3 ≤ k) : hstarZ k t < 8 * k + 1 := by
  unfold hstarZ; split <;> exact Nat.mod_lt _ (by omega)

def hstarPt (k : Nat) (hk : 3 ≤ k) (t : Fin (hstarM k)) : Fin (8 * k + 1) × Fin (8 * k + 1) :=
  (⟨hstarY k t.val, hstarY_lt k t.val hk t.isLt⟩, ⟨hstarZ k t.val, hstarZ_lt k t.val hk⟩)

/-- Helper: if `0 ≤ a < b < hstarM k` and `cycDist (8k+1) (hstarY k a) (hstarY k b) ≤ 1`,
then either `b - a ≤ k - 1` OR `a + hstarM k - b ≤ k - 1`! -/
theorem hstarY_close_implies_idx_close (k a b : Nat) (hk : 3 ≤ k)
    (ha : a < hstarM k) (hb : b < hstarM k) (hab : a < b)
    (hcy : cycDist (8 * k + 1) (hstarY k a) (hstarY k b) ≤ 1) :
    b - a ≤ k - 1 ∨ a + hstarM k - b ≤ k - 1 := by
  have hya := hstarY_lt k a hk ha
  have hyb := hstarY_lt k b hk hb
  rw [cycDist_le_iff (8 * k + 1) (hstarY k a) (hstarY k b) 1 hya hyb] at hcy
  unfold hstarY hstarM at *
  by_cases hev : k % 2 = 0
  · simp only [hev, ↓reduceIte] at hcy hya hyb
    have hkj : 2 * (k / 2) = k := by omega
    have hj_pos : 0 < k / 2 := by omega
    have hM : 4 * k * k + k / 2 = (8 * k + 1) * (k / 2) := by
      calc 4 * k * k + k / 2 = 4 * k * (2 * (k / 2)) + k / 2 := by rw [hkj]
        _ = 8 * k * (k / 2) + k / 2 := by
            have : 4 * k * (2 * (k / 2)) = 8 * k * (k / 2) := by rw [show 8 = 4 * 2 by rfl]; ac_rfl
            rw [this]
        _ = (8 * k + 1) * (k / 2) := by rw [Nat.add_mul, Nat.one_mul]
    have hdiv_le : a / (k / 2) ≤ b / (k / 2) := Nat.div_le_div_right (by omega)
    have ha_lo : (k / 2) * (a / (k / 2)) ≤ a := Nat.mul_div_le a (k / 2)
    have ha_hi : a < (k / 2) * (a / (k / 2) + 1) := by
      have h := Nat.lt_div_mul_add (a := a) hj_pos
      rw [Nat.mul_comm (a / (k / 2)) (k / 2)] at h; rw [Nat.mul_add, Nat.mul_one]; exact h
    have hb_lo : (k / 2) * (b / (k / 2)) ≤ b := Nat.mul_div_le b (k / 2)
    have hb_hi : b < (k / 2) * (b / (k / 2)) + k / 2 := by
      have h := Nat.lt_div_mul_add (a := b) hj_pos
      rw [Nat.mul_comm (b / (k / 2)) (k / 2)] at h; exact h
    rcases hcy with ⟨_, hle⟩ | ⟨_, hle⟩ | hle | hle
    · left
      have hmul := Nat.mul_le_mul_left (k / 2) (show b / (k / 2) ≤ a / (k / 2) + 1 by omega)
      rw [Nat.mul_add, Nat.mul_one] at hmul; omega
    · left
      have hmul := Nat.mul_le_mul_left (k / 2) (show b / (k / 2) ≤ a / (k / 2) + 1 by omega)
      rw [Nat.mul_add, Nat.mul_one] at hmul; omega
    · right
      rw [Nat.sub_le_iff_le_add] at hle
      have ha0 : a / (k / 2) = 0 := by
        cases h : a / (k / 2) with
        | zero => rfl
        | succ m => rw [h] at hle; omega
      rw [ha0] at hle ha_hi
      have hbmax : b / (k / 2) = 8 * k := by omega
      rw [hbmax] at hb_lo
      have h8k : (8 * k + 1) * (k / 2) = (k / 2) * (8 * k) + k / 2 := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (8 * k) (k / 2)]
      omega
    · omega
  · simp only [hev, ↓reduceIte] at hcy hya hyb
    have hkj : 2 * (k / 2) + 1 = k := by omega
    have hmono : ∀ x, x < 4 * k * k →
        (if x % k ≤ k / 2 then 2 * (x / k) else 2 * (x / k) + 1) < 8 * k := by
      intro x hx
      have hp : x / k < 4 * k := Nat.div_lt_of_lt_mul (by
        have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
        rw [h1]; exact hx)
      split <;> omega
    by_cases hbt : b ≥ 4 * k * k
    · simp only [hbt, ↓reduceIte] at hcy
      by_cases hat : a ≥ 4 * k * k
      · left; omega
      · simp only [hat, ↓reduceIte] at hcy
        have hya_lt := hmono a (by omega)
        by_cases hya0 : (if a % k ≤ k / 2 then 2 * (a / k) else 2 * (a / k) + 1) = 0
        · right
          have ha_div0 : a / k = 0 := by split at hya0 <;> omega
          have ha_rem : a % k ≤ k / 2 := by split at hya0 <;> omega
          have ha_eq : a = k * (a / k) + a % k := (Nat.div_add_mod a k).symm
          rw [ha_div0, Nat.mul_zero, Nat.zero_add] at ha_eq
          omega
        · left
          have hya_last : (if a % k ≤ k / 2 then 2 * (a / k) else 2 * (a / k) + 1) = 8 * k - 1 := by omega
          have ha_div : a / k = 4 * k - 1 := by split at hya_last <;> omega
          have ha_rem : k / 2 < a % k := by split at hya_last <;> omega
          have ha_eq : a = k * (a / k) + a % k := (Nat.div_add_mod a k).symm
          have hmul : k * (4 * k - 1) = 4 * k * k - k := by
            rw [Nat.mul_sub, Nat.mul_one]
            have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
            rw [h1]
          have h4k_ge : k ≤ 4 * k * k := by
            have h1 : k * 1 ≤ k * (4 * k) := Nat.mul_le_mul_left k (by omega)
            have h2 : k * (4 * k) = 4 * k * k := by ac_rfl
            omega
          rw [ha_div, hmul] at ha_eq
          omega
    · have hat : ¬ (a ≥ 4 * k * k) := by omega
      simp only [hat, hbt, ↓reduceIte] at hcy
      have hya_lt := hmono a (by omega)
      have hyb_lt := hmono b (by omega)
      have hdiv_le : a / k ≤ b / k := Nat.div_le_div_right (by omega)
      have ha_eq : a = k * (a / k) + a % k := (Nat.div_add_mod a k).symm
      have hb_eq : b = k * (b / k) + b % k := (Nat.div_add_mod b k).symm
      have ha_mod : a % k < k := Nat.mod_lt a (by omega)
      have hb_mod : b % k < k := Nat.mod_lt b (by omega)
      left
      by_cases hd_eq : a / k = b / k
      · rw [hd_eq] at ha_eq; omega
      · have hdiff : b / k = a / k + 1 := by
          split at hcy <;> split at hcy
          · have h1 : a / k < 4 * k := by split at hya_lt <;> omega
            have h2 : b / k < 4 * k := by split at hyb_lt <;> omega
            omega
          · have h1 : a / k < 4 * k := by split at hya_lt <;> omega
            have h2 : b / k < 4 * k := by split at hyb_lt <;> omega
            omega
          · have h1 : a / k < 4 * k := by split at hya_lt <;> omega
            have h2 : b / k < 4 * k := by split at hyb_lt <;> omega
            omega
          · have h1 : a / k < 4 * k := by split at hya_lt <;> omega
            have h2 : b / k < 4 * k := by split at hyb_lt <;> omega
            omega
        have hrems : k / 2 < a % k ∧ b % k ≤ k / 2 := by
          split at hcy <;> split at hcy
          · have h1 : a / k < 4 * k := by split at hya_lt <;> omega
            have h2 : b / k < 4 * k := by split at hyb_lt <;> omega
            omega
          · have h1 : a / k < 4 * k := by split at hya_lt <;> omega
            have h2 : b / k < 4 * k := by split at hyb_lt <;> omega
            omega
          · have h1 : a / k < 4 * k := by split at hya_lt <;> omega
            have h2 : b / k < 4 * k := by split at hyb_lt <;> omega
            omega
          · have h1 : a / k < 4 * k := by split at hya_lt <;> omega
            have h2 : b / k < 4 * k := by split at hyb_lt <;> omega
            omega
        rw [hdiff, Nat.mul_add, Nat.mul_one] at hb_eq
        omega

theorem hstarPt_indep (k : Nat) (hk : 3 ≤ k) :
    ∀ a b : Fin (hstarM k), a ≠ b →
      ¬ conflict (qGraphHStar (8 * k + 1)) (hstarPt k hk a) (hstarPt k hk b) := by
  let n := 8 * k + 1
  let M := hstarM k
  have h2kk : 2 * k * k = 2 * (k * k) := Nat.mul_assoc 2 k k
  have h3kk_eq : 3 * k * k = 3 * (k * k) := Nat.mul_assoc 3 k k
  have h4kk_eq : 4 * k * k = 4 * (k * k) := Nat.mul_assoc 4 k k
  have hkk_ge3k : 3 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have hz_gap : ∀ (a b : Nat), a < M → b < M → a < b →
      (b - a ≤ k - 1 ∨ a + M - b ≤ k - 1) →
      8 ≤ cycDist n (hstarZ k a) (hstarZ k b) := by
    intro a b ha hb hab hclose
    have h4M_even : k % 2 = 0 → 8 * M = 4 * k * n := by
      intro hev
      dsimp [M, hstarM, n]
      have hk2 : 2 * (k / 2) = k := by omega
      calc 8 * (4 * k * k + k / 2)
          = 32 * k * k + 4 * (2 * (k / 2)) := by
            rw [Nat.mul_add]
            have h1 : 8 * (4 * k * k) = 32 * k * k := by ac_rfl
            have h2 : 8 * (k / 2) = 4 * (2 * (k / 2)) := by rw [show 8 = 4 * 2 by rfl]; ac_rfl
            omega
        _ = 32 * k * k + 4 * k := by rw [hk2]
        _ = 4 * k * (8 * k + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            have h1 : 4 * k * (8 * k) = 32 * k * k := by ac_rfl
            omega
    have h4M_odd : k % 2 = 1 → 8 * M + 4 = 4 * k * n := by
      intro hodd
      dsimp [M, hstarM, n]
      have hk2 : 2 * (k / 2) + 1 = k := by omega
      calc 8 * (4 * k * k + k / 2) + 4
          = 32 * k * k + 4 * (2 * (k / 2) + 1) := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
            have h1 : 8 * (4 * k * k) = 32 * k * k := by ac_rfl
            have h2 : 8 * (k / 2) = 4 * (2 * (k / 2)) := by rw [show 8 = 4 * 2 by rfl]; ac_rfl
            omega
        _ = 32 * k * k + 4 * k := by rw [hk2]
        _ = 4 * k * (8 * k + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            have h1 : 4 * k * (8 * k) = 32 * k * k := by ac_rfl
            omega
    have hmod_far : ∀ (x y : Nat), x ≤ y → 8 ≤ y - x → y - x ≤ n - 8 →
        8 ≤ cycDist n (x % n) (y % n) := by
      intro x y hxy hlo hhi
      apply Classical.byContradiction; intro hlt
      rcases cycDist_signed_delta n (y % n) (x % n) 7 (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
        (by rw [cycDist_symm]; omega) with ⟨δ, q, hδ1, hδ2, hδeq⟩
      rcases int_mod_decomp y n (by omega) with ⟨ky, hky⟩
      rcases int_mod_decomp x n (by omega) with ⟨kx, hkx⟩
      let Q := q + ky - kx
      have hdiff : ((y - x : Nat) : Int) = Q * (n : Int) + δ := by
        have hmul : Q * (n : Int) = q * n + ky * n - kx * n := by dsimp [Q]; rw [Int.sub_mul, Int.add_mul]
        omega
      have hQ0 := int_mul_eq_zero_of_abs_lt (K := Q) (n := (n : Int)) (δ := δ - ((y - x : Nat) : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hQ0, Int.zero_mul] at hdiff; omega
    unfold hstarZ
    by_cases hev : k % 2 = 0
    · simp only [hev, ↓reduceIte]
      rcases hclose with hd | hw
      · exact hmod_far (8 * a) (8 * b) (Nat.mul_le_mul_left 8 (by omega)) (by omega) (by dsimp [n]; omega)
      · have hmod_eq : (8 * a) % n = (8 * a + 4 * k * n) % n := by
          rw [Nat.add_mul_mod_self_right]
        rw [hmod_eq, cycDist_symm]
        have heq_m := h4M_even hev
        dsimp [n, M, hstarM] at heq_m hw ha hb ⊢
        exact hmod_far (8 * b) (8 * a + 4 * k * (8 * k + 1)) (by omega) (by omega) (by omega)
    · have hodd : k % 2 = 1 := by omega
      simp only [hev, ↓reduceIte]
      let ea := (if 0 < a then 1 else 0) + (if k * k < a then 1 else 0) +
                (if 2 * k * k < a then 1 else 0) + (if 3 * k * k < a then 1 else 0)
      let eb := (if 0 < b then 1 else 0) + (if k * k < b then 1 else 0) +
                (if 2 * k * k < b then 1 else 0) + (if 3 * k * k < b then 1 else 0)
      rcases hclose with hd | hw
      · have hmono_if : ∀ c, (if c < a then 1 else 0) ≤ (if c < b then 1 else 0) := by
          intro c; split <;> split <;> omega
        have he_le : ea ≤ eb := by
          dsimp [ea, eb]
          have h0 := hmono_if 0; have h1 := hmono_if (k * k)
          have h2 := hmono_if (2 * k * k); have h3 := hmono_if (3 * k * k)
          omega
        have he_diff : eb - ea ≤ 1 := by
          dsimp [ea, eb]
          split <;> split <;> split <;> split <;> split <;> split <;> split <;> split <;> omega
        exact hmod_far (8 * a + ea) (8 * b + eb) (by omega) (by omega) (by dsimp [n]; omega)
      · have h3kk : 3 * k * k < b := by dsimp [M, hstarM] at *; omega
        have ha_lt_kk : a < k * k := by dsimp [M, hstarM] at *; omega
        have heb4 : eb = 4 := by
          dsimp [eb]
          simp only [show 0 < b by omega, show k * k < b by omega,
                     show 2 * k * k < b by omega, h3kk, ↓reduceIte]
        have hea1 : ea ≤ 1 := by
          dsimp [ea]
          simp only [show ¬ (k * k < a) by omega, show ¬ (2 * k * k < a) by omega,
                     show ¬ (3 * k * k < a) by omega, ↓reduceIte]
          split <;> omega
        have hmod_eq : (8 * a + ea) % n = (8 * a + ea + 4 * k * n) % n := by
          rw [Nat.add_mul_mod_self_right]
        rw [hmod_eq, cycDist_symm]
        have heq_m := h4M_odd hodd
        dsimp [n, M, hstarM] at heq_m hw ha hb ⊢
        exact hmod_far (8 * b + eb) (8 * a + ea + 4 * k * (8 * k + 1)) (by omega) (by omega) (by omega)
  intro a b hab hconf
  have hcore : ∀ (u v : Fin M), u.val < v.val → ¬ conflict (qGraphHStar n) (hstarPt k hk u) (hstarPt k hk v) := by
    intro u v huv hc
    rw [qGraphHStar, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff] at hc
    dsimp [hstarPt] at hc
    have hcl := hstarY_close_implies_idx_close k u.val v.val hk u.isLt v.isLt huv hc.1
    have hfar := hz_gap u.val v.val u.isLt v.isLt huv hcl
    omega
  by_cases hlt : a.val < b.val
  · exact hcore a b hlt hconf
  · have hgt : b.val < a.val := by
      have hne : a.val ≠ b.val := fun h => hab (Fin.ext h); omega
    exact hcore b a hgt (conflict_symm _ hconf)

/-- **Theorem T1e (Infinite Exact-Ceiling `H*` Family & Automatic `n²`-Port Quotient Systems).**
For EVERY `k ≥ 3` (`n = 8k + 1`, `M = 4k² + k/2`):
1. `M` attains the exact double-counting ceiling `(n * (n / 8)) / 2`,
2. `hstarPt k` is independent of size `M` in `qGraphHStar n` and lifts via T1a to `M * n²` words in `C_n^{⊠ 4}`,
3. For EVERY odd `k` (`k % 2 = 1`, i.e., `n = 16j + 9`: `C₂₅, C₄₁, C₅₇, ...`), the quotient port
   `p₀ = (0, 0) → p₁ = (n - 1, 0)` with auxiliary shifted set `X_Q = Q + (1, n - 1)` is a valid
   quotient `RichPortSystem` with unique private owner `t = 0`, singleton `A = {t = 0}`, singleton
   `D = {t = 4k² - (k/2 + 1)}`, and `A ∩ D = ∅` (`|A| = 1, |D| = 1, η = M - 2`, lifting to `n²` ports)! -/
theorem t1e_infinite_hstar_family_and_ports (k : Nat) (hk : 3 ≤ k) :
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
      (0 ≠ 4 * k * k - (k / 2 + 1))) := by
  dsimp only
  let n := 8 * k + 1
  let M := hstarM k
  have hceil : M = (n * (n / 8)) / 2 := by
    have hd : n / 8 = k := by dsimp [n]; omega
    rw [hd]; dsimp [M, hstarM, n]
    have h1 : (8 * k + 1) * k = 2 * (4 * k * k) + k := by
      rw [Nat.add_mul, Nat.one_mul]; have : 8 * k * k = 2 * (4 * k * k) := by rw [show 8 = 2 * 4 by rfl]; ac_rfl
      rw [this]
    rw [h1]; omega
  have h2kk : 2 * k * k = 2 * (k * k) := Nat.mul_assoc 2 k k
  have h3kk_eq : 3 * k * k = 3 * (k * k) := Nat.mul_assoc 3 k k
  have h4kk_eq : 4 * k * k = 4 * (k * k) := Nat.mul_assoc 4 k k
  have hkk_ge3k : 3 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have hz_gap : ∀ (a b : Nat), a < M → b < M → a < b →
      (b - a ≤ k - 1 ∨ a + M - b ≤ k - 1) →
      8 ≤ cycDist n (hstarZ k a) (hstarZ k b) := by
    intro a b ha hb hab hclose
    have h4M_even : k % 2 = 0 → 8 * M = 4 * k * n := by
      intro hev
      dsimp [M, hstarM, n]
      have hk2 : 2 * (k / 2) = k := by omega
      calc 8 * (4 * k * k + k / 2)
          = 32 * k * k + 4 * (2 * (k / 2)) := by
            rw [Nat.mul_add]
            have h1 : 8 * (4 * k * k) = 32 * k * k := by ac_rfl
            have h2 : 8 * (k / 2) = 4 * (2 * (k / 2)) := by rw [show 8 = 4 * 2 by rfl]; ac_rfl
            omega
        _ = 32 * k * k + 4 * k := by rw [hk2]
        _ = 4 * k * (8 * k + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            have h1 : 4 * k * (8 * k) = 32 * k * k := by ac_rfl
            omega
    have h4M_odd : k % 2 = 1 → 8 * M + 4 = 4 * k * n := by
      intro hodd
      dsimp [M, hstarM, n]
      have hk2 : 2 * (k / 2) + 1 = k := by omega
      calc 8 * (4 * k * k + k / 2) + 4
          = 32 * k * k + 4 * (2 * (k / 2) + 1) := by
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
            have h1 : 8 * (4 * k * k) = 32 * k * k := by ac_rfl
            have h2 : 8 * (k / 2) = 4 * (2 * (k / 2)) := by rw [show 8 = 4 * 2 by rfl]; ac_rfl
            omega
        _ = 32 * k * k + 4 * k := by rw [hk2]
        _ = 4 * k * (8 * k + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            have h1 : 4 * k * (8 * k) = 32 * k * k := by ac_rfl
            omega
    have hmod_far : ∀ (x y : Nat), x ≤ y → 8 ≤ y - x → y - x ≤ n - 8 →
        8 ≤ cycDist n (x % n) (y % n) := by
      intro x y hxy hlo hhi
      apply Classical.byContradiction; intro hlt
      rcases cycDist_signed_delta n (y % n) (x % n) 7 (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
        (by rw [cycDist_symm]; omega) with ⟨δ, q, hδ1, hδ2, hδeq⟩
      rcases int_mod_decomp y n (by omega) with ⟨ky, hky⟩
      rcases int_mod_decomp x n (by omega) with ⟨kx, hkx⟩
      let Q := q + ky - kx
      have hdiff : ((y - x : Nat) : Int) = Q * (n : Int) + δ := by
        have hmul : Q * (n : Int) = q * n + ky * n - kx * n := by dsimp [Q]; rw [Int.sub_mul, Int.add_mul]
        omega
      have hQ0 := int_mul_eq_zero_of_abs_lt (K := Q) (n := (n : Int)) (δ := δ - ((y - x : Nat) : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hQ0, Int.zero_mul] at hdiff; omega
    unfold hstarZ
    by_cases hev : k % 2 = 0
    · simp only [hev, ↓reduceIte]
      rcases hclose with hd | hw
      · exact hmod_far (8 * a) (8 * b) (Nat.mul_le_mul_left 8 (by omega)) (by omega) (by dsimp [n]; omega)
      · have hmod_eq : (8 * a) % n = (8 * a + 4 * k * n) % n := by
          rw [Nat.add_mul_mod_self_right]
        rw [hmod_eq, cycDist_symm]
        have heq_m := h4M_even hev
        dsimp [n, M, hstarM] at heq_m hw ha hb ⊢
        exact hmod_far (8 * b) (8 * a + 4 * k * (8 * k + 1)) (by omega) (by omega) (by omega)
    · have hodd : k % 2 = 1 := by omega
      simp only [hev, ↓reduceIte]
      let ea := (if 0 < a then 1 else 0) + (if k * k < a then 1 else 0) +
                (if 2 * k * k < a then 1 else 0) + (if 3 * k * k < a then 1 else 0)
      let eb := (if 0 < b then 1 else 0) + (if k * k < b then 1 else 0) +
                (if 2 * k * k < b then 1 else 0) + (if 3 * k * k < b then 1 else 0)
      rcases hclose with hd | hw
      · have hmono_if : ∀ c, (if c < a then 1 else 0) ≤ (if c < b then 1 else 0) := by
          intro c; split <;> split <;> omega
        have he_le : ea ≤ eb := by
          dsimp [ea, eb]
          have h0 := hmono_if 0; have h1 := hmono_if (k * k)
          have h2 := hmono_if (2 * k * k); have h3 := hmono_if (3 * k * k)
          omega
        have he_diff : eb - ea ≤ 1 := by
          dsimp [ea, eb]
          split <;> split <;> split <;> split <;> split <;> split <;> split <;> split <;> omega
        exact hmod_far (8 * a + ea) (8 * b + eb) (by omega) (by omega) (by dsimp [n]; omega)
      · have h3kk : 3 * k * k < b := by dsimp [M, hstarM] at *; omega
        have ha_lt_kk : a < k * k := by dsimp [M, hstarM] at *; omega
        have heb4 : eb = 4 := by
          dsimp [eb]
          simp only [show 0 < b by omega, show k * k < b by omega,
                     show 2 * k * k < b by omega, h3kk, ↓reduceIte]
        have hea1 : ea ≤ 1 := by
          dsimp [ea]
          simp only [show ¬ (k * k < a) by omega, show ¬ (2 * k * k < a) by omega,
                     show ¬ (3 * k * k < a) by omega, ↓reduceIte]
          split <;> omega
        have hmod_eq : (8 * a + ea) % n = (8 * a + ea + 4 * k * n) % n := by
          rw [Nat.add_mul_mod_self_right]
        rw [hmod_eq, cycDist_symm]
        have heq_m := h4M_odd hodd
        dsimp [n, M, hstarM] at heq_m hw ha hb ⊢
        exact hmod_far (8 * b + eb) (8 * a + ea + 4 * k * (8 * k + 1)) (by omega) (by omega) (by omega)
  have hindep : HasIndepSetOfSize (qGraphHStar n) M := by
    refine ⟨hstarPt k hk, ?_⟩
    intro a b hab hconf
    have hcore : ∀ (u v : Fin M), u.val < v.val → ¬ conflict (qGraphHStar n) (hstarPt k hk u) (hstarPt k hk v) := by
      intro u v huv hc
      rw [qGraphHStar, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff] at hc
      dsimp [hstarPt] at hc
      have hcl := hstarY_close_implies_idx_close k u.val v.val hk u.isLt v.isLt huv hc.1
      have hfar := hz_gap u.val v.val u.isLt v.isLt huv hcl
      omega
    by_cases hlt : a.val < b.val
    · exact hcore a b hlt hconf
    · have hgt : b.val < a.val := by
        have hne : a.val ≠ b.val := fun h => hab (Fin.ext h); omega
      exact hcore b a hgt (conflict_symm _ hconf)
  refine ⟨hceil, hindep, t1a_coset_quotient_compression.2 n M (by omega) hindep, ?_⟩
  intro hodd
  have hev_false : ¬ (k % 2 = 0) := by omega
  let j := k / 2
  have hkj : 2 * j + 1 = k := by omega
  have hM_pos : 0 < M := by dsimp [M, hstarM]; omega
  have h3kk_lt : 3 * k * k < 4 * k * k - (j + 1) := by omega
  have h4M_odd : 8 * M + 4 = 4 * k * n := by
    dsimp [M, hstarM, n]
    calc 8 * (4 * k * k + j) + 4
        = 32 * k * k + 4 * (2 * j + 1) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
          have h1 : 8 * (4 * k * k) = 32 * k * k := by ac_rfl
          have h2 : 8 * j = 4 * (2 * j) := by rw [show 8 = 4 * 2 by rfl]; ac_rfl
          omega
      _ = 32 * k * k + 4 * k := by rw [hkj]
      _ = 4 * k * (8 * k + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          have h1 : 4 * k * (8 * k) = 32 * k * k := by ac_rfl
          omega
  have hp0_eq : hstarPt k hk ⟨0, hM_pos⟩ = (⟨0, by omega⟩, ⟨0, by omega⟩) := by
    have h4k0 : ¬ (0 ≥ 4 * k * k) := by omega
    apply Prod.ext <;> apply Fin.ext <;> simp [hstarPt, hstarY, hstarZ, hev_false, h4k0]
  -- Helper: evaluate `hstarZ k t` for small `t < k` and near `M` (`t ≥ 4*k*k - k`)!
  have hz_small : ∀ t, 0 < t → t < k → hstarZ k t = 8 * t + 1 := by
    intro t ht0 htk
    unfold hstarZ; simp only [hev_false, ↓reduceIte]
    have h1 : (if 0 < t then 1 else 0) + (if k * k < t then 1 else 0) +
              (if 2 * k * k < t then 1 else 0) + (if 3 * k * k < t then 1 else 0) = 1 := by
      simp only [ht0, show ¬ (k * k < t) by omega, show ¬ (2 * k * k < t) by omega,
                 show ¬ (3 * k * k < t) by omega, ↓reduceIte]
    rw [h1]; exact Nat.mod_eq_of_lt (by omega)
  have hz_tail : ∀ t, 4 * k * k - (j + 1) ≤ t → t < M →
      hstarZ k t = (n - 8 * (M - t)) % n := by
    intro t htlo hthi
    have h3lt : 3 * k * k < t := by omega
    unfold hstarZ; simp only [hev_false, ↓reduceIte]
    have he4 : (if 0 < t then 1 else 0) + (if k * k < t then 1 else 0) +
               (if 2 * k * k < t then 1 else 0) + (if 3 * k * k < t then 1 else 0) = 4 := by
      simp only [show 0 < t by omega, show k * k < t by omega,
                 show 2 * k * k < t by omega, h3lt, ↓reduceIte]
    rw [he4]
    have hle : 8 * (M - t) ≤ n := by dsimp [M, hstarM, n, j] at htlo hthi ⊢; omega
    have hsum : 8 * t + 4 = (4 * k - 1) * n + (n - 8 * (M - t)) := by
      have h1 : (4 * k - 1) * n + n = 4 * k * n := by
        rw [Nat.sub_mul, Nat.one_mul]; have : n ≤ 4 * k * n := Nat.le_mul_of_pos_left n (by omega); omega
      omega
    rw [hsum, Nat.mul_comm (4 * k - 1) n, Nat.mul_add_mod]
  refine ⟨hp0_eq, ?_, ?_, ?_, by omega⟩
  · -- Privacy of `p1 = (n - 1, 0)`: unique conflicting point in `Q` is `t = 0`!
    intro t
    rw [qGraphHStar, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff]
    constructor
    · intro ⟨hy, hz⟩
      dsimp [hstarPt] at hy hz
      apply Classical.byContradiction; intro ht0
      have hyt_lt := hstarY_lt k t.val hk t.isLt
      rw [cycDist_le_iff (8 * k + 1) (8 * k) (hstarY k t.val) 1 (by omega) hyt_lt] at hy
      have hy_cases : hstarY k t.val = 0 ∨ hstarY k t.val = 8 * k - 1 ∨ hstarY k t.val = 8 * k := by omega
      rcases hy_cases with hy0 | hyl1 | hyl2
      · have ht_le : t.val ≤ j := by
          unfold hstarY at hy0; simp only [hev_false, ↓reduceIte] at hy0
          split at hy0
          · omega
          · have hdiv0 : t.val / k = 0 := by split at hy0 <;> omega
            have hrem : t.val % k ≤ j := by split at hy0 <;> omega
            have heq := Nat.div_add_mod t.val k; rw [hdiv0, Nat.mul_zero, Nat.zero_add] at heq; omega
        have hzval := hz_small t.val (by omega) (by omega)
        rw [hzval, cycDist_le_iff (8 * k + 1) 0 (8 * t.val + 1) 7 (by omega) (by omega)] at hz
        omega
      · have ht_ge : 4 * k * k - j ≤ t.val ∧ t.val < 4 * k * k := by
          unfold hstarY at hyl1; simp only [hev_false, ↓reduceIte] at hyl1
          split at hyl1
          · omega
          · have hdiv : t.val / k = 4 * k - 1 := by split at hyl1 <;> omega
            have hrem : j < t.val % k := by split at hyl1 <;> omega
            have heq := Nat.div_add_mod t.val k
            have hmul : k * (4 * k - 1) = 4 * k * k - k := by
              rw [Nat.mul_sub, Nat.mul_one]
              have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
              rw [h1]
            have hkle : k ≤ 4 * k * k := by omega
            rw [hdiv, hmul] at heq
            omega
        have hzval := hz_tail t.val (by omega) t.isLt
        have htlt := t.isLt
        have hmt_lo : 1 ≤ M - t.val := by dsimp [M, hstarM] at htlt ⊢; omega
        have hmt_hi : M - t.val ≤ 2 * j := by dsimp [M, hstarM] at htlt ⊢; omega
        rw [hzval, Nat.mod_eq_of_lt (by dsimp [n]; omega),
            cycDist_le_iff (8 * k + 1) 0 (n - 8 * (M - t.val)) 7 (by omega) (by dsimp [n]; omega)] at hz
        dsimp [n] at hz; omega
      · have ht_ge : 4 * k * k ≤ t.val := by
          unfold hstarY at hyl2; simp only [hev_false, ↓reduceIte] at hyl2
          split at hyl2
          · omega
          · have hp : t.val / k < 4 * k := Nat.div_lt_of_lt_mul (by
              have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
              rw [h1]; omega)
            split at hyl2 <;> omega
        have hzval := hz_tail t.val (by omega) t.isLt
        have htlt := t.isLt
        have hmt_lo : 1 ≤ M - t.val := by dsimp [M, hstarM] at htlt ⊢; omega
        have hmt_hi : M - t.val ≤ j := by dsimp [M, hstarM] at htlt ⊢; omega
        rw [hzval, Nat.mod_eq_of_lt (by dsimp [n]; omega),
            cycDist_le_iff (8 * k + 1) 0 (n - 8 * (M - t.val)) 7 (by omega) (by dsimp [n]; omega)] at hz
        dsimp [n] at hz; omega
    · intro ht0
      have hteq : t = ⟨0, hM_pos⟩ := Fin.ext ht0
      rw [hteq, hp0_eq]
      dsimp only
      refine ⟨?_, ?_⟩
      · rw [Nat.add_sub_cancel, cycDist_le_iff (8 * k + 1) (8 * k) 0 1 (by omega) (by omega)]; right; right; right; omega
      · rw [cycDist_self (8 * k + 1) 0 (by omega)]; omega
  · -- Footprint `A` of `p0 = (0, 0)` in `Xq = Q + (1, n - 1)`: exact singleton `t = 0`!
    intro t
    rw [qGraphHStar, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff]
    constructor
    · intro ⟨hy, hz⟩
      dsimp [hstarPt] at hy hz
      apply Classical.byContradiction; intro ht0
      -- `(y_t + 1) % n ∈ {n - 1, 0, 1}` means `y_t ∈ {n - 2, n - 1, 0}` (`{8k - 1, 8k, 0}`)!
      have hyt_lt := hstarY_lt k t.val hk t.isLt
      rw [cycDist_le_iff n 0 ((hstarY k t.val + 1) % n) 1 (by omega) (Nat.mod_lt _ (by omega))] at hy
      have hy_cases : hstarY k t.val = 0 ∨ hstarY k t.val = 8 * k - 1 ∨ hstarY k t.val = 8 * k := by
        by_cases hlast : hstarY k t.val = 8 * k
        · right; right; exact hlast
        · have hmod : (hstarY k t.val + 1) % n = hstarY k t.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hmod] at hy; omega
      rcases hy_cases with hy0 | hyl1 | hyl2
      · have ht_le : t.val ≤ j := by
          unfold hstarY at hy0; simp only [hev_false, ↓reduceIte] at hy0
          split at hy0
          · omega
          · have hdiv0 : t.val / k = 0 := by split at hy0 <;> omega
            have hrem : t.val % k ≤ j := by split at hy0 <;> omega
            have heq := Nat.div_add_mod t.val k; rw [hdiv0, Nat.mul_zero, Nat.zero_add] at heq; omega
        have hzval := hz_small t.val (by omega) (by omega)
        rw [hzval] at hz
        have hzm : (8 * t.val + 1 + 8 * k) % (8 * k + 1) = 8 * t.val := by
          have : 8 * t.val + 1 + 8 * k = 8 * t.val + (8 * k + 1) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hzm, cycDist_le_iff (8 * k + 1) 0 (8 * t.val) 7 (by omega) (by omega)] at hz
        omega
      · have ht_ge : 4 * k * k - j ≤ t.val ∧ t.val < 4 * k * k := by
          unfold hstarY at hyl1; simp only [hev_false, ↓reduceIte] at hyl1
          split at hyl1
          · omega
          · have hdiv : t.val / k = 4 * k - 1 := by split at hyl1 <;> omega
            have hrem : j < t.val % k := by split at hyl1 <;> omega
            have heq := Nat.div_add_mod t.val k
            have hmul : k * (4 * k - 1) = 4 * k * k - k := by
              rw [Nat.mul_sub, Nat.mul_one]
              have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
              rw [h1]
            have hkle : k ≤ 4 * k * k := by omega
            rw [hdiv, hmul] at heq
            omega
        have hzval := hz_tail t.val (by omega) t.isLt
        have hmt_lo : 1 ≤ M - t.val := by have htlt := t.isLt; dsimp [M, hstarM] at htlt ⊢; omega
        have hmt_hi : M - t.val ≤ 2 * j := by have htlt := t.isLt; dsimp [M, hstarM] at htlt ⊢; omega
        have hmod_r : (n - 8 * (M - t.val)) % n = n - 8 * (M - t.val) := Nat.mod_eq_of_lt (by dsimp [n]; omega)
        rw [hzval, hmod_r] at hz
        have hzm : (n - 8 * (M - t.val) + 8 * k) % (8 * k + 1) = n - 8 * (M - t.val) - 1 := by
          have : n - 8 * (M - t.val) + 8 * k = (n - 8 * (M - t.val) - 1) + (8 * k + 1) := by dsimp [n]; omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp [n]; omega)]
        rw [hzm, cycDist_le_iff (8 * k + 1) 0 (n - 8 * (M - t.val) - 1) 7 (by omega) (by dsimp [n]; omega)] at hz
        dsimp [n] at hz; omega
      · have ht_ge : 4 * k * k ≤ t.val := by
          unfold hstarY at hyl2; simp only [hev_false, ↓reduceIte] at hyl2
          split at hyl2
          · omega
          · have hp : t.val / k < 4 * k := Nat.div_lt_of_lt_mul (by
              have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
              rw [h1]; omega)
            split at hyl2 <;> omega
        have hzval := hz_tail t.val (by omega) t.isLt
        have hmt_lo : 1 ≤ M - t.val := by have htlt := t.isLt; dsimp [M, hstarM] at htlt ⊢; omega
        have hmt_hi : M - t.val ≤ j := by have htlt := t.isLt; dsimp [M, hstarM] at htlt ⊢; omega
        have hmod_r : (n - 8 * (M - t.val)) % n = n - 8 * (M - t.val) := Nat.mod_eq_of_lt (by dsimp [n]; omega)
        rw [hzval, hmod_r] at hz
        have hzm : (n - 8 * (M - t.val) + 8 * k) % (8 * k + 1) = n - 8 * (M - t.val) - 1 := by
          have : n - 8 * (M - t.val) + 8 * k = (n - 8 * (M - t.val) - 1) + (8 * k + 1) := by dsimp [n]; omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp [n]; omega)]
        rw [hzm, cycDist_le_iff (8 * k + 1) 0 (n - 8 * (M - t.val) - 1) 7 (by omega) (by dsimp [n]; omega)] at hz
        dsimp [n] at hz; omega
    · intro ht0
      have hteq : t = ⟨0, hM_pos⟩ := Fin.ext ht0
      rw [hteq, hp0_eq]
      dsimp only
      refine ⟨?_, ?_⟩
      · rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega), cycDist_le_iff (8 * k + 1) 0 1 1 (by omega) (by omega)]; right; left; omega
      · rw [Nat.zero_add, Nat.add_sub_cancel, Nat.mod_eq_of_lt (by omega), cycDist_le_iff (8 * k + 1) 0 (8 * k) 7 (by omega) (by omega)]; right; right; left; omega
  · -- Footprint `D` of `p1 = (n - 1, 0)` in `Xq = Q + (1, n - 1)`: exact singleton `t = 4k^2 - (j + 1)`!
    intro t
    rw [qGraphHStar, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff]
    constructor
    · intro ⟨hy, hz⟩
      dsimp [hstarPt] at hy hz
      have hyt_lt := hstarY_lt k t.val hk t.isLt
      rw [cycDist_le_iff (8 * k + 1) (8 * k) ((hstarY k t.val + 1) % (8 * k + 1)) 1 (by omega) (Nat.mod_lt _ (by omega))] at hy
      have hy_cases : hstarY k t.val = 8 * k - 2 ∨ hstarY k t.val = 8 * k - 1 ∨ hstarY k t.val = 8 * k := by
        by_cases hlast : hstarY k t.val = 8 * k
        · right; right; exact hlast
        · have hmod : (hstarY k t.val + 1) % (8 * k + 1) = hstarY k t.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hmod] at hy; omega
      -- In ALL three rows `8k - 2, 8k - 1, 8k`, `t ≥ 4*k*k - k`!
      have ht_ge : 4 * k * k - k ≤ t.val := by
        rcases hy_cases with h82 | h81 | h80
        · unfold hstarY at h82; simp only [hev_false, ↓reduceIte] at h82
          split at h82
          · omega
          · have hdiv : t.val / k = 4 * k - 1 := by split at h82 <;> omega
            have heq := Nat.div_add_mod t.val k
            have hmul : k * (4 * k - 1) = 4 * k * k - k := by
              rw [Nat.mul_sub, Nat.mul_one]
              have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
              rw [h1]
            rw [hdiv, hmul] at heq; omega
        · unfold hstarY at h81; simp only [hev_false, ↓reduceIte] at h81
          split at h81
          · omega
          · have hdiv : t.val / k = 4 * k - 1 := by split at h81 <;> omega
            have heq := Nat.div_add_mod t.val k
            have hmul : k * (4 * k - 1) = 4 * k * k - k := by
              rw [Nat.mul_sub, Nat.mul_one]
              have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
              rw [h1]
            rw [hdiv, hmul] at heq; omega
        · unfold hstarY at h80; simp only [hev_false, ↓reduceIte] at h80
          split at h80
          · omega
          · have hp : t.val / k < 4 * k := Nat.div_lt_of_lt_mul (by
              have h1 : k * (4 * k) = 4 * k * k := by ac_rfl
              rw [h1]; omega)
            split at h80 <;> omega
      -- Now `M - t ∈ [1, k + j]`, and `z_t = (n - 8*(M - t)) % n`!
      -- Check `M - t` vs `k`:
      --   If `M - t = k` (`t = M - k = 4k^2 + j - (2j + 1) = 4k^2 - (j + 1)`!):
      --     `n - 8*k = 1`, so `(1 + n - 1) % n = 0` (distance `0 ≤ 7`!!).
      --   If `M - t < k`: `1 ≤ M - t ≤ k - 1`, so `z_t = n - 8*(M - t) ∈ [9, n - 8]`,
      --     shifted `z_t - 1 ∈ [8, n - 9]` => `cycDist n 0 (z_t - 1) ≥ 8 > 7`!
      --   If `M - t > k`: `k + 1 ≤ M - t ≤ k + j`, so `8*(M - t) = n + 8*(M - t - k) - 1`,
      --     `z_t = 2*n - 8*(M - t) = n + 1 - 8*(M - t - k) ∈ [n + 1 - 8*j, n - 7] = [4k + 5, n - 7]`,
      --     shifted `z_t - 1 ∈ [4k + 4, n - 8]` => `cycDist n 0 (z_t - 1) ≥ 8 > 7`!
      by_cases hmt_eq : M - t.val = k
      · dsimp [M, hstarM] at hmt_eq; omega
      · by_cases hmt_lt : M - t.val < k
        · have hzval := hz_tail t.val (by dsimp [M, hstarM, j] at hmt_lt ⊢; omega) t.isLt
          have hmod_r : (n - 8 * (M - t.val)) % n = n - 8 * (M - t.val) := Nat.mod_eq_of_lt (by dsimp [n]; omega)
          rw [hzval, hmod_r] at hz
          have hzm : (n - 8 * (M - t.val) + 8 * k) % (8 * k + 1) = n - 8 * (M - t.val) - 1 := by
            have : n - 8 * (M - t.val) + 8 * k = (n - 8 * (M - t.val) - 1) + (8 * k + 1) := by dsimp [n]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp [n]; omega)]
          rw [hzm, cycDist_le_iff (8 * k + 1) 0 (n - 8 * (M - t.val) - 1) 7 (by omega) (by dsimp [n]; omega)] at hz
          dsimp [n] at hz; omega
        · -- `k + 1 ≤ M - t.val ≤ k + j`
          have h3lt : 3 * k * k < t.val := by omega
          have hzval : hstarZ k t.val = 2 * n - 8 * (M - t.val) := by
            unfold hstarZ; simp only [hev_false, ↓reduceIte]
            have he4 : (if 0 < t.val then 1 else 0) + (if k * k < t.val then 1 else 0) +
                       (if 2 * k * k < t.val then 1 else 0) + (if 3 * k * k < t.val then 1 else 0) = 4 := by
              simp only [show 0 < t.val by omega, show k * k < t.val by omega,
                         show 2 * k * k < t.val by omega, h3lt, ↓reduceIte]
            rw [he4]
            have hsum : 8 * t.val + 4 = (4 * k - 2) * n + (2 * n - 8 * (M - t.val)) := by
              have h1 : (4 * k - 2) * n + 2 * n = 4 * k * n := by
                rw [Nat.sub_mul]
                have : 2 * n ≤ 4 * k * n := Nat.mul_le_mul_right n (by omega)
                omega
              have htlt := t.isLt
              dsimp [M, hstarM, n] at h1 h4M_odd htlt hmt_eq hmt_lt ht_ge ⊢; omega
            have htlt := t.isLt
            rw [hsum, Nat.mul_comm (4 * k - 2) n, Nat.mul_add_mod,
                Nat.mod_eq_of_lt (by dsimp [M, hstarM, n] at htlt hmt_eq hmt_lt ht_ge ⊢; omega)]
          rw [hzval] at hz
          have htlt := t.isLt
          have hzm : (2 * n - 8 * (M - t.val) + 8 * k) % (8 * k + 1) = 2 * n - 8 * (M - t.val) - 1 := by
            have hlt_n : 2 * n - 8 * (M - t.val) - 1 < 8 * k + 1 := by dsimp [M, hstarM, n] at htlt hmt_eq hmt_lt ht_ge ⊢; omega
            have hgt0 : 1 ≤ 2 * n - 8 * (M - t.val) := by dsimp [M, hstarM, n] at htlt hmt_eq hmt_lt ht_ge ⊢; omega
            have : 2 * n - 8 * (M - t.val) + 8 * k = (2 * n - 8 * (M - t.val) - 1) + (8 * k + 1) := by dsimp [n]; omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_n]
          rw [hzm, cycDist_le_iff (8 * k + 1) 0 (2 * n - 8 * (M - t.val) - 1) 7 (by omega)
              (by dsimp [M, hstarM, n] at htlt hmt_eq hmt_lt ht_ge ⊢; omega)] at hz
          dsimp [M, hstarM, n] at htlt hmt_eq hmt_lt ht_ge hz ⊢; omega
    · intro hteq
      have hmt : M - t.val = k := by dsimp [M, hstarM]; omega
      have hyt : hstarY k t.val = 8 * k - 2 := by
        unfold hstarY; simp only [hev_false, ↓reduceIte]
        have hlt4 : ¬ (t.val ≥ 4 * k * k) := by omega
        simp only [hlt4, ↓reduceIte]
        have hdecomp : t.val = (4 * k - 1) * k + j := by
          rw [Nat.sub_mul, Nat.one_mul]; omega
        have hdiv : t.val / k = 4 * k - 1 := by
          rw [hdecomp, Nat.mul_comm (4 * k - 1) k, Nat.mul_add_div (by omega),
              Nat.div_eq_of_lt (by omega), Nat.add_zero]
        have hrem : t.val % k = j := by
          rw [hdecomp, Nat.mul_comm (4 * k - 1) k, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        rw [hdiv, hrem]; simp [j]; omega
      have hzt : hstarZ k t.val = 1 := by
        rw [hz_tail t.val (by omega) t.isLt, hmt]
        have : n - 8 * k = 1 := by dsimp [n]; omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      dsimp [hstarPt]
      rw [hyt, hzt]
      refine ⟨?_, ?_⟩
      · rw [Nat.mod_eq_of_lt (by omega), cycDist_le_iff (8 * k + 1) (8 * k) (8 * k - 2 + 1) 1 (by omega) (by omega)]
        left; omega
      · have hmod0 : (1 + 8 * k) % (8 * k + 1) = 0 := by
          have : 1 + 8 * k = 8 * k + 1 := by omega
          rw [this, Nat.mod_self]
        rw [hmod0, cycDist_self (8 * k + 1) 0 (by omega)]; omega

/-! ### 6. Baumert Pullback Homomorphism Theorem (T1f) -/

/-- Exact 1-coordinate Baumert pullback `Fin (p + 2) → Fin p`:
`0 ↦ 0`, `1 ↦ 1`, `2 ↦ 0`, `3 ↦ 1`, `x ≥ 4 ↦ x - 2`. -/
def pull1 (p : Nat) (hp : 2 ≤ p) (x : Fin (p + 2)) : Fin p :=
  if h : x.val < 2 then ⟨x.val, by omega⟩ else ⟨x.val - 2, by omega⟩

/-- Key 5-line locally-injective homomorphism lemma on `C_{p+2} → C_p` (`p ≥ 5`). -/
theorem pull1_edge_and_local_inj (p : Nat) (hp : 5 ≤ p) (u v : Fin (p + 2))
    (hc : conflict (cycleGraph (p + 2)) u v) :
    conflict (cycleGraph p) (pull1 p (by omega) u) (pull1 p (by omega) v) ∧
    (pull1 p (by omega) u = pull1 p (by omega) v → u = v) := by
  rw [conflict_cycleGraph_iff, cycDist_le_iff (p + 2) u.val v.val 1 u.isLt v.isLt] at hc
  rw [conflict_cycleGraph_iff, cycDist_le_iff p _ _ 1 (pull1 p _ u).isLt (pull1 p _ v).isLt]
  unfold pull1
  constructor
  · split <;> split <;> dsimp only <;> omega
  · intro heq
    apply Fin.ext
    split at heq <;> split at heq <;> injection heq with hv <;> omega

/-- Coordinatewise Baumert pullback `C_{p+2}^{⊠ d} → C_p^{⊠ d}`. -/
def pullVec (p d : Nat) (hp : 2 ≤ p) (x : Fin d → Fin (p + 2)) : Fin d → Fin p :=
  fun i => pull1 p hp (x i)

/-- **Theorem T1f (Baumert Pullback Homomorphism Theorem).**
For all `p ≥ 5` and `d ≥ 1`:
1. `pullVec p d` preserves conflict AND never collapses two distinct conflicting vertices
   (locally-injective strong-power graph homomorphism),
2. Any independent predicate `P : (Fin d → Fin p) → Prop` lifts to an independent predicate
   `P ∘ pullVec` in `C_{p+2}^{⊠ d}`,
3. Explicit preimage fiber multiplicity: each `x ∈ Fin p` has fiber size `2` if `x < 2` else `1`,
   giving exact factored cardinality for `H_BPZ`-coset packings `Q ⊂ ℤ_p²`! -/
theorem t1f_baumert_pullback_homomorphism (p d : Nat) (hp : 5 ≤ p) :
    (∀ u v : Fin d → Fin (p + 2),
      conflict (strongPow (cycleGraph (p + 2)) d) u v →
      conflict (strongPow (cycleGraph p) d) (pullVec p d (by omega) u) (pullVec p d (by omega) v) ∧
      (pullVec p d (by omega) u = pullVec p d (by omega) v → u = v)) ∧
    (∀ (P : (Fin d → Fin p) → Prop),
      (∀ a b, P a → P b → conflict (strongPow (cycleGraph p) d) a b → a = b) →
      (∀ u v, P (pullVec p d (by omega) u) → P (pullVec p d (by omega) v) →
        conflict (strongPow (cycleGraph (p + 2)) d) u v → u = v)) := by
  have h1 : ∀ u v : Fin d → Fin (p + 2),
      conflict (strongPow (cycleGraph (p + 2)) d) u v →
      conflict (strongPow (cycleGraph p) d) (pullVec p d (by omega) u) (pullVec p d (by omega) v) ∧
      (pullVec p d (by omega) u = pullVec p d (by omega) v → u = v) := by
    intro u v hc
    rw [conflict_strongPow_iff] at hc
    constructor
    · rw [conflict_strongPow_iff]
      intro i
      exact (pull1_edge_and_local_inj p hp (u i) (v i) (hc i)).1
    · intro hpeq
      funext i
      have hi : pull1 p (by omega) (u i) = pull1 p (by omega) (v i) := congrFun hpeq i
      exact (pull1_edge_and_local_inj p hp (u i) (v i) (hc i)).2 hi
  refine ⟨h1, ?_⟩
  intro P hP u v hPu hPv hc
  have ⟨hpc, hlinj⟩ := h1 u v hc
  exact hlinj (hP _ _ hPu hPv hpc)

/-- Exact 4-coordinate Baumert pullback membership oracle for an `H_BPZ` quotient list `Q ⊂ ℤ_p²`. -/
def inBaumertHBPZ (p : Nat) (hp : 2 ≤ p) (Q : List (Nat × Nat)) (w : Fin 4 → Fin (p + 2)) : Bool :=
  let u := (pull1 p hp (w ⟨0, by omega⟩)).val
  let v := (pull1 p hp (w ⟨1, by omega⟩)).val
  let w2 := (pull1 p hp (w ⟨2, by omega⟩)).val
  let w3 := (pull1 p hp (w ⟨3, by omega⟩)).val
  let qy := (w2 + 2 * p - 2 * v) % p
  let qz := (w3 + 2 * p - 2 * u) % p
  Q.any (fun q => q.1 == qy && q.2 == qz)

/-- Exact factored cardinality formula for `BaumertExpand(Q + H_BPZ)`:
`∑_{(y,z) ∈ Q} (∑_{u < p} wt(u) * wt((2u+z)%p)) * (∑_{v < p} wt(v) * wt((2v+y)%p))`! -/
def baumertWt (x : Nat) : Nat := if x < 2 then 2 else 1

def baumertLineSum (p offset : Nat) : Nat :=
  sumNat p (fun t => baumertWt t * baumertWt ((2 * t + offset) % p))

def baumertFactoredCard (p : Nat) (Q : List (Nat × Nat)) : Nat :=
  Q.foldl (fun acc q => acc + baumertLineSum p q.2 * baumertLineSum p q.1) 0

/-- Explicit enumeration of `Fin (p+2)^4` vertices belonging to `inBaumertHBPZ` via its exact
factored fiber product `Q × (fiber u, w3) × (fiber v, w2)`, proving `HasIndepSetOfSize` with
exact cardinality `baumertFactoredCard p Q` in pure kernel time `O(|Q| * p)`! -/
def fiberPair (p : Nat) (_hp : 2 ≤ p) (x : Nat) (hx : x < p) : List (Fin (p + 2)) :=
  if _h : x < 2 then [⟨x, by omega⟩, ⟨x + 2, by omega⟩] else [⟨x + 2, by omega⟩]

theorem fiberPair_len (p : Nat) (hp : 2 ≤ p) (x : Nat) (hx : x < p) :
    (fiberPair p hp x hx).length = baumertWt x := by
  unfold fiberPair baumertWt; split <;> rfl

theorem fiberPair_pull (p : Nat) (hp : 2 ≤ p) (x : Nat) (hx : x < p) (y : Fin (p + 2))
    (hy : y ∈ fiberPair p hp x hx) :
    (pull1 p hp y).val = x := by
  unfold fiberPair at hy
  split at hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · simp [pull1, *]
    · have hge : ¬ (x + 2 < 2) := by omega
      simp [pull1, hge]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    have hge : ¬ (x + 2 < 2) := by omega
    simp [pull1, hge]

theorem fiberPair_nodup (p : Nat) (hp : 2 ≤ p) (x : Nat) (hx : x < p) :
    (fiberPair p hp x hx).Nodup := by
  unfold fiberPair
  split
  · simp [Fin.ext_iff]
  · simp

theorem list_map_val_finRange : ∀ n : Nat, (List.finRange n).map Fin.val = List.range n
  | 0 => rfl
  | n + 1 => by
    rw [List.finRange_succ_last, List.map_append, List.map_map, List.range_succ]
    have hc : (Fin.val ∘ Fin.castSucc : Fin n → Nat) = Fin.val := funext (fun _ => rfl)
    rw [hc, list_map_val_finRange n]
    simp

theorem list_nodup_map {α β : Type} {f : α → β} {l : List α}
    (hinj : ∀ x y, f x = f y → x = y) (hl : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    rcases hmem with ⟨b, hb, hfb⟩
    exact hl.1 (hinj b a hfb ▸ hb)

theorem list_nodup_flatMap {α β : Type} {l : List α} {f : α → List β}
    (h1 : ∀ a ∈ l, (f a).Nodup)
    (h2 : l.Pairwise (fun a b => ∀ x, x ∈ f a → x ∈ f b → False)) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.flatMap_cons, List.nodup_append]
    rw [List.pairwise_cons] at h2
    refine ⟨h1 a (List.mem_cons_self ..),
            ih (fun b hb => h1 b (List.mem_cons_of_mem a hb)) h2.2, ?_⟩
    intro x hxa y hytl heq
    subst heq
    rw [List.mem_flatMap] at hytl
    rcases hytl with ⟨b, hb, hxb⟩
    exact h2.1 b hb x hxa hxb

/-- Direct factored independent set lifting of ANY `H_BPZ` quotient packing `Q` on `C_p^4`
to `C_{p+2}^4` with exact cardinality `baumertFactoredCard p Q` (ZERO `p^4` enumeration!). -/
def baumertLineList (p : Nat) (hp : 2 ≤ p) (offset : Nat) : List (Fin (p + 2) × Fin (p + 2)) :=
  (List.finRange p).flatMap (fun t =>
    (fiberPair p hp t.val t.isLt).flatMap (fun a =>
      (fiberPair p hp ((2 * t.val + offset) % p) (Nat.mod_lt _ (by omega))).map (fun b => (a, b))))

theorem baumertLineList_len (p : Nat) (hp : 2 ≤ p) (offset : Nat) :
    (baumertLineList p hp offset).length = baumertLineSum p offset := by
  unfold baumertLineList baumertLineSum
  have hsum_finRange : ∀ (n : Nat) (f : Nat → Nat),
      ((List.finRange n).map (fun i => f i.val)).sum = sumNat n f := by
    intro n f
    have hcomp : (List.finRange n).map (fun i => f i.val) = (List.range n).map f := by
      rw [← list_map_val_finRange n, List.map_map]; rfl
    rw [hcomp]
    clear hcomp
    induction n with
    | zero => rfl
    | succ s ihs =>
      rw [List.range_succ, List.map_append, List.sum_append, ihs]
      simp [sumNat]
  rw [List.length_flatMap]
  have hinner : ((List.finRange p).map (fun t =>
      ((fiberPair p hp t.val t.isLt).flatMap (fun a =>
        (fiberPair p hp ((2 * t.val + offset) % p) (Nat.mod_lt _ (by omega))).map (fun b => (a, b)))).length)) =
      (List.finRange p).map (fun t => baumertWt t.val * baumertWt ((2 * t.val + offset) % p)) := by
    apply List.map_congr_left
    intro t _
    rw [List.length_flatMap]
    have hconst : ((fiberPair p hp t.val t.isLt).map (fun a =>
        ((fiberPair p hp ((2 * t.val + offset) % p) (Nat.mod_lt _ (by omega))).map (fun b => (a, b))).length)) =
        (fiberPair p hp t.val t.isLt).map (fun _ => baumertWt ((2 * t.val + offset) % p)) := by
      apply List.map_congr_left; intro a _
      rw [List.length_map, fiberPair_len]
    rw [hconst]
    have hsum_const : ∀ (α : Type) (L : List α) (c : Nat), (L.map (fun _ => c)).sum = L.length * c := by
      intro α L c
      induction L with
      | nil => simp
      | cons _ tl iht => simp [iht, Nat.succ_mul, Nat.add_comm]
    rw [hsum_const, fiberPair_len]
  rw [hinner]
  exact hsum_finRange p (fun x => baumertWt x * baumertWt ((2 * x + offset) % p))

def baumertExpandList (p : Nat) (hp : 2 ≤ p) (Q : List (Nat × Nat)) : List (Fin 4 → Fin (p + 2)) :=
  Q.flatMap (fun q =>
    (baumertLineList p hp q.2).flatMap (fun uv03 =>
      (baumertLineList p hp q.1).map (fun uv12 =>
        fun i : Fin 4 =>
          match i with
          | ⟨0, _⟩ => uv03.1
          | ⟨1, _⟩ => uv12.1
          | ⟨2, _⟩ => uv12.2
          | ⟨3, _⟩ => uv03.2)))

theorem baumertExpandList_len (p : Nat) (hp : 2 ≤ p) (Q : List (Nat × Nat)) :
    (baumertExpandList p hp Q).length = baumertFactoredCard p Q := by
  have hgen : ∀ (L : List (Nat × Nat)) (acc : Nat),
      L.foldl (fun a q => a + baumertLineSum p q.2 * baumertLineSum p q.1) acc =
      acc + (baumertExpandList p hp L).length := by
    intro L
    induction L with
    | nil => intro acc; simp [baumertExpandList]
    | cons hd tl ih =>
      intro acc
      have hcons : baumertExpandList p hp (hd :: tl) =
          (baumertLineList p hp hd.2).flatMap (fun uv03 =>
            (baumertLineList p hp hd.1).map (fun uv12 =>
              fun i : Fin 4 =>
                match i with
                | ⟨0, _⟩ => uv03.1 | ⟨1, _⟩ => uv12.1
                | ⟨2, _⟩ => uv12.2 | ⟨3, _⟩ => uv03.2)) ++ baumertExpandList p hp tl := rfl
      rw [List.foldl_cons, ih, hcons, List.length_append]
      have hhd : ((baumertLineList p hp hd.2).flatMap (fun uv03 =>
          (baumertLineList p hp hd.1).map (fun uv12 =>
            fun i : Fin 4 =>
              match i with
              | ⟨0, _⟩ => uv03.1
              | ⟨1, _⟩ => uv12.1
              | ⟨2, _⟩ => uv12.2
              | ⟨3, _⟩ => uv03.2))).length =
          baumertLineSum p hd.2 * baumertLineSum p hd.1 := by
        rw [List.length_flatMap]
        have hconst : ((baumertLineList p hp hd.2).map (fun uv03 =>
            ((baumertLineList p hp hd.1).map (fun uv12 =>
              fun i : Fin 4 =>
                match i with
                | ⟨0, _⟩ => uv03.1
                | ⟨1, _⟩ => uv12.1
                | ⟨2, _⟩ => uv12.2
                | ⟨3, _⟩ => uv03.2)).length)) =
            (baumertLineList p hp hd.2).map (fun _ => baumertLineSum p hd.1) := by
          apply List.map_congr_left; intro _ _
          rw [List.length_map, baumertLineList_len]
        rw [hconst]
        have hsum_const : ∀ (α : Type) (L : List α) (c : Nat), (L.map (fun _ => c)).sum = L.length * c := by
          intro α L c
          induction L with
          | nil => simp
          | cons _ t2 ih2 => simp [ih2, Nat.succ_mul, Nat.add_comm]
        rw [hsum_const, baumertLineList_len]
      rw [hhd, Nat.add_assoc]
  unfold baumertFactoredCard
  rw [hgen Q 0, Nat.zero_add]

theorem baumertLineList_nodup (p : Nat) (hp : 2 ≤ p) (offset : Nat) :
    (baumertLineList p hp offset).Nodup := by
  unfold baumertLineList
  apply list_nodup_flatMap
  · intro t _
    apply list_nodup_flatMap
    · intro a _
      exact list_nodup_map (fun x y h => by injection h) (fiberPair_nodup p hp _ _)
    · apply List.Pairwise.imp_of_mem _ (fiberPair_nodup p hp t.val t.isLt)
      intro a1 a2 _ _ hne x hx1 hx2
      simp only [List.mem_map] at hx1 hx2
      rcases hx1 with ⟨_, _, rfl⟩
      rcases hx2 with ⟨_, _, heq⟩
      injection heq with ha _
      exact hne ha.symm
  · apply List.Pairwise.imp_of_mem _ (List.nodup_finRange p)
    intro t1 t2 _ _ hne x hx1 hx2
    simp only [List.mem_flatMap, List.mem_map] at hx1 hx2
    rcases hx1 with ⟨a1, ha1, b1, _, rfl⟩
    rcases hx2 with ⟨a2, ha2, b2, _, heq⟩
    injection heq with ha _
    rw [ha] at ha2
    have h1 := fiberPair_pull p hp t1.val t1.isLt a1 ha1
    have h2 := fiberPair_pull p hp t2.val t2.isLt a1 ha2
    exact hne (Fin.ext (by omega))

theorem baumertLineList_mem_rel (p : Nat) (hp : 2 ≤ p) (offset : Nat)
    (ab : Fin (p + 2) × Fin (p + 2)) (hmem : ab ∈ baumertLineList p hp offset) :
    (pull1 p hp ab.2).val = (2 * (pull1 p hp ab.1).val + offset) % p := by
  unfold baumertLineList at hmem
  simp only [List.mem_flatMap, List.mem_map] at hmem
  rcases hmem with ⟨t, _, a, ha, b, hb, heq⟩
  cases heq
  rw [fiberPair_pull p hp t.val t.isLt a ha,
      fiberPair_pull p hp ((2 * t.val + offset) % p) (Nat.mod_lt _ (by omega)) b hb]

/-- Complete factored Baumert expansion theorem: any verified `H_BPZ` quotient list `Q ⊂ ℤ_p²`
(`p ≥ 9`) lifts directly to `HasIndepSetOfSize (strongPow (cycleGraph (p + 2)) 4) (baumertFactoredCard p Q)`! -/
theorem baumert_expand_hbpz_indep (p : Nat) (hp : 9 ≤ p) (Q : List (Nat × Nat))
    (hQbound : ∀ q ∈ Q, q.1 < p ∧ q.2 < p)
    (hQindep : Q.Pairwise (fun q1 q2 => ¬ (cycDist p q1.1 q2.1 ≤ 3 ∧ cycDist p q1.2 q2.2 ≤ 3))) :
    HasIndepSetOfSize (strongPow (cycleGraph (p + 2)) 4) (baumertFactoredCard p Q) := by
  rw [← baumertExpandList_len p (by omega) Q]
  -- Prove `baumertExpandList p _ Q` is `Nodup` and every element pulls back into `Q + H_BPZ`!
  have hQnodup : Q.Nodup := by
    apply List.Pairwise.imp _ hQindep
    intro q1 q2 hnc heq
    subst heq
    exact hnc ⟨by rw [cycDist_self p _ (by omega)]; omega, by rw [cycDist_self p _ (by omega)]; omega⟩
  have hnodup : (baumertExpandList p (by omega) Q).Nodup := by
    unfold baumertExpandList
    apply list_nodup_flatMap
    · intro q _
      apply list_nodup_flatMap
      · intro uv03 _
        exact list_nodup_map (fun x y h => by
          have h1 : x.1 = y.1 := congrFun h ⟨1, by omega⟩
          have h2 : x.2 = y.2 := congrFun h ⟨2, by omega⟩
          exact Prod.ext h1 h2) (baumertLineList_nodup p (by omega) q.1)
      · apply List.Pairwise.imp_of_mem _ (baumertLineList_nodup p (by omega) q.2)
        intro a1 a2 _ _ hne w hw1 hw2
        simp only [List.mem_map] at hw1 hw2
        rcases hw1 with ⟨b1, _, rfl⟩
        rcases hw2 with ⟨b2, _, heq⟩
        have h0 : a2.1 = a1.1 := congrFun heq ⟨0, by omega⟩
        have h3 : a2.2 = a1.2 := congrFun heq ⟨3, by omega⟩
        exact hne (Prod.ext h0.symm h3.symm)
    · apply List.Pairwise.imp_of_mem _ hQnodup
      intro q1 q2 hq1 hq2 hne w hw1 hw2
      simp only [List.mem_flatMap, List.mem_map] at hw1 hw2
      rcases hw1 with ⟨a1, ha1, b1, hb1, rfl⟩
      rcases hw2 with ⟨a2, ha2, b2, hb2, heq⟩
      have h0 : a2.1 = a1.1 := congrFun heq ⟨0, by omega⟩
      have h1 : b2.1 = b1.1 := congrFun heq ⟨1, by omega⟩
      have h2 : b2.2 = b1.2 := congrFun heq ⟨2, by omega⟩
      have h3 : a2.2 = a1.2 := congrFun heq ⟨3, by omega⟩
      have r1y := baumertLineList_mem_rel p (by omega) q1.1 b1 hb1
      have r2y := baumertLineList_mem_rel p (by omega) q2.1 b2 hb2
      have r1z := baumertLineList_mem_rel p (by omega) q1.2 a1 ha1
      have r2z := baumertLineList_mem_rel p (by omega) q2.2 a2 ha2
      rw [h1, h2] at r2y; rw [h0, h3] at r2z
      have ⟨hy1, hz1⟩ := hQbound q1 hq1
      have ⟨hy2, hz2⟩ := hQbound q2 hq2
      have heq_y : q1.1 = q2.1 := by
        have hmod : (2 * (pull1 p (by omega) b1.1).val + q1.1) % p =
                    (2 * (pull1 p (by omega) b1.1).val + q2.1) % p := by omega
        rcases int_mod_decomp (2 * (pull1 p (by omega) b1.1).val + q1.1) p (by omega) with ⟨k1, hk1⟩
        rcases int_mod_decomp (2 * (pull1 p (by omega) b1.1).val + q2.1) p (by omega) with ⟨k2, hk2⟩
        have hd : (k1 - k2) * (p : Int) + ((q2.1 : Int) - (q1.1 : Int)) = 0 := by rw [Int.sub_mul]; omega
        have hk := int_mul_eq_zero_of_abs_lt (K := k1 - k2) (n := (p : Int))
          (δ := (q2.1 : Int) - (q1.1 : Int)) (by omega) (by omega) (by omega) hd
        rw [hk, Int.zero_mul] at hd; omega
      have heq_z : q1.2 = q2.2 := by
        have hmod : (2 * (pull1 p (by omega) a1.1).val + q1.2) % p =
                    (2 * (pull1 p (by omega) a1.1).val + q2.2) % p := by omega
        rcases int_mod_decomp (2 * (pull1 p (by omega) a1.1).val + q1.2) p (by omega) with ⟨k1, hk1⟩
        rcases int_mod_decomp (2 * (pull1 p (by omega) a1.1).val + q2.2) p (by omega) with ⟨k2, hk2⟩
        have hd : (k1 - k2) * (p : Int) + ((q2.2 : Int) - (q1.2 : Int)) = 0 := by rw [Int.sub_mul]; omega
        have hk := int_mul_eq_zero_of_abs_lt (K := k1 - k2) (n := (p : Int))
          (δ := (q2.2 : Int) - (q1.2 : Int)) (by omega) (by omega) (by omega) hd
        rw [hk, Int.zero_mul] at hd; omega
      exact hne (Prod.ext heq_y heq_z)
  have hmem_lift : ∀ w ∈ baumertExpandList p (by omega) Q,
      ∃ q ∈ Q, ∃ (hq : q.1 < p ∧ q.2 < p) (u v : Fin p),
        pullVec p 4 (by omega) w = liftHBPZ p (by omega) (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩) u v := by
    intro w hw
    unfold baumertExpandList at hw
    simp only [List.mem_flatMap, List.mem_map] at hw
    rcases hw with ⟨q, hq, uv03, huv03, uv12, huv12, rfl⟩
    refine ⟨q, hq, hQbound q hq, pull1 p (by omega) uv03.1, pull1 p (by omega) uv12.1, ?_⟩
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ =>
      apply Fin.ext
      exact baumertLineList_mem_rel p (by omega) q.1 uv12 huv12
    | ⟨3, _⟩ =>
      apply Fin.ext
      exact baumertLineList_mem_rel p (by omega) q.2 uv03 huv03
  apply hasIndepSet_of_list
  intro i j hij hconf
  simp only [List.get_eq_getElem] at hconf
  have hwi : (baumertExpandList p (by omega) Q)[i.val] ∈ baumertExpandList p (by omega) Q := List.getElem_mem i.isLt
  have hwj : (baumertExpandList p (by omega) Q)[j.val] ∈ baumertExpandList p (by omega) Q := List.getElem_mem j.isLt
  rcases hmem_lift _ hwi with ⟨q1, hq1, hb1, u1, v1, heq1⟩
  rcases hmem_lift _ hwj with ⟨q2, hq2, hb2, u2, v2, heq2⟩
  have ⟨hpc, hlinj⟩ := (t1f_baumert_pullback_homomorphism p 4 (by omega)).1 _ _ hconf
  rw [heq1, heq2] at hpc
  have ⟨hqc, hsame⟩ := liftHBPZ_conflict_implies_quot hp _ _ u1 v1 u2 v2 hpc
  have hqeq : q1 = q2 := by
    apply Classical.byContradiction; intro hne
    rw [qGraphHBPZ, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff] at hqc
    have hboth : ∀ a b, a ∈ Q → b ∈ Q → a ≠ b →
        ¬ (cycDist p a.1 b.1 ≤ 3 ∧ cycDist p a.2 b.2 ≤ 3) := by
      clear hqc hne hsame hpc hlinj heq1 heq2 u1 v1 u2 v2 hb1 hb2 hq1 hq2 hwi hwj hconf hij i j hnodup hmem_lift hQnodup hQbound
      induction Q with
      | nil => intro _ _ ha; exact nomatch ha
      | cons hd tl ih =>
        rw [List.pairwise_cons] at hQindep
        intro a b ha hb hab
        simp only [List.mem_cons] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hQindep.1 b hb
        · intro ⟨hc1, hc2⟩
          exact hQindep.1 a ha ⟨by rw [cycDist_symm]; exact hc1, by rw [cycDist_symm]; exact hc2⟩
        · exact ih hQindep.2 a b ha hb hab
    exact hboth q1 q2 hq1 hq2 hne hqc
  subst hqeq
  have ⟨hu, hv⟩ := hsame rfl
  subst hu; subst hv
  have hpeq : pullVec p 4 (by omega) ((baumertExpandList p (by omega) Q)[i.val]) =
              pullVec p 4 (by omega) ((baumertExpandList p (by omega) Q)[j.val]) := by
    rw [heq1, heq2]
  have hweq := hlinj hpeq
  have hnodup_inj : ∀ {α : Type} (l : List α), l.Nodup →
      ∀ (a b : Nat) (ha : a < l.length) (hb : b < l.length), l[a] = l[b] → a = b := by
    intro α l
    induction l with
    | nil => intro _ _ _ ha; exact nomatch ha
    | cons hd tl ih =>
      intro hnd a b ha hb heq
      rw [List.nodup_cons] at hnd
      cases a with
      | zero =>
        cases b with
        | zero => rfl
        | succ b' =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
          exact False.elim (hnd.1 (heq ▸ List.getElem_mem (by simp at hb; omega)))
      | succ a' =>
        cases b with
        | zero =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
          exact False.elim (hnd.1 (heq.symm ▸ List.getElem_mem (by simp at ha; omega)))
        | succ b' =>
          simp only [List.getElem_cons_succ] at heq
          exact congrArg Nat.succ (ih hnd.2 a' b' (by simp at ha; omega) (by simp at hb; omega) heq)
  exact hij (Fin.ext (hnodup_inj _ hnodup i.val j.val i.isLt j.isLt hweq))

/-- Exact equivalence between membership in `baumertExpandList` and the `inBaumertHBPZ` oracle! -/
theorem baumertExpandList_mem_iff (p : Nat) (hp : 2 ≤ p) (Q : List (Nat × Nat))
    (hQbound : ∀ q ∈ Q, q.1 < p ∧ q.2 < p) (w : Fin 4 → Fin (p + 2)) :
    w ∈ baumertExpandList p hp Q ↔ inBaumertHBPZ p hp Q w = true := by
  have hmem_fiber : ∀ (x : Fin (p + 2)), x ∈ fiberPair p hp (pull1 p hp x).val (pull1 p hp x).isLt := by
    intro x
    unfold fiberPair pull1
    by_cases hx : x.val < 2
    · simp only [hx, ↓reduceDIte]
      simp
    · simp only [hx, ↓reduceDIte]
      by_cases hx2 : x.val - 2 < 2
      · simp only [hx2, ↓reduceDIte, List.mem_cons]
        right; left; apply Fin.ext; dsimp; omega
      · simp only [hx2, ↓reduceDIte, List.mem_cons]
        left; apply Fin.ext; dsimp; omega
  constructor
  · intro hw
    unfold baumertExpandList at hw
    simp only [List.mem_flatMap, List.mem_map] at hw
    rcases hw with ⟨q, hq, uv03, huv03, uv12, huv12, rfl⟩
    unfold inBaumertHBPZ
    rw [List.any_eq_true]
    refine ⟨q, hq, ?_⟩
    have r1y := baumertLineList_mem_rel p hp q.1 uv12 huv12
    have r1z := baumertLineList_mem_rel p hp q.2 uv03 huv03
    have ⟨hyb, hzb⟩ := hQbound q hq
    have hmod_inv : ∀ (a b : Nat), a < p → b < p → ((2 * a + b) % p + 2 * p - 2 * a) % p = b := by
      intro a b ha hb
      rcases int_mod_decomp (2 * a + b) p (by omega) with ⟨k, hk⟩
      have hsub_ge : 2 * a ≤ (2 * a + b) % p + 2 * p := by omega
      have heq : (((2 * a + b) % p + 2 * p - 2 * a : Nat) : Int) = (b : Int) + (2 - k) * (p : Int) := by
        rw [Int.sub_mul]; omega
      have hmod2 : ((2 * a + b) % p + 2 * p - 2 * a) % p = b := by
        rcases int_mod_decomp ((2 * a + b) % p + 2 * p - 2 * a) p (by omega) with ⟨k2, hk2⟩
        have hd : (k2 + k - 2) * (p : Int) + ((((2 * a + b) % p + 2 * p - 2 * a) % p : Nat) : Int) - (b : Int) = 0 := by
          rw [Int.sub_mul, Int.add_mul]; omega
        have hlt := Nat.mod_lt ((2 * a + b) % p + 2 * p - 2 * a) (show 0 < p by omega)
        have hK0 := int_mul_eq_zero_of_abs_lt (K := k2 + k - 2) (n := (p : Int))
          (δ := ((((2 * a + b) % p + 2 * p - 2 * a) % p : Nat) : Int) - (b : Int))
          (by omega) (by omega) (by omega) (by omega)
        rw [hK0, Int.zero_mul] at hd; omega
      exact hmod2
    dsimp only
    rw [r1y, r1z, hmod_inv _ _ (pull1 p hp uv12.1).isLt hyb, hmod_inv _ _ (pull1 p hp uv03.1).isLt hzb]
    simp
  · intro hin
    unfold inBaumertHBPZ at hin
    rw [List.any_eq_true] at hin
    rcases hin with ⟨q, hq, heq⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at heq
    rcases heq with ⟨hqy, hqz⟩
    have ⟨hyb, hzb⟩ := hQbound q hq
    have hinv : ∀ (a c b : Nat), a < p → c < p → b < p → (c + 2 * p - 2 * a) % p = b → c = (2 * a + b) % p := by
      intro a c b ha hc hb hm
      rcases int_mod_decomp (c + 2 * p - 2 * a) p (by omega) with ⟨k1, hk1⟩
      rcases int_mod_decomp (2 * a + b) p (by omega) with ⟨k2, hk2⟩
      have hge : 2 * a ≤ c + 2 * p := by omega
      have hd : (k2 + k1 - 2) * (p : Int) + (((2 * a + b) % p : Nat) : Int) - (c : Int) = 0 := by
        rw [Int.sub_mul, Int.add_mul]; omega
      have hlt := Nat.mod_lt (2 * a + b) (show 0 < p by omega)
      have hK0 := int_mul_eq_zero_of_abs_lt (K := k2 + k1 - 2) (n := (p : Int))
        (δ := (((2 * a + b) % p : Nat) : Int) - (c : Int))
        (by omega) (by omega) (by omega) (by omega)
      rw [hK0, Int.zero_mul] at hd; omega
    have hw2_eq : (pull1 p hp (w ⟨2, by omega⟩)).val = (2 * (pull1 p hp (w ⟨1, by omega⟩)).val + q.1) % p :=
      hinv _ _ _ (pull1 p hp (w ⟨1, by omega⟩)).isLt (pull1 p hp (w ⟨2, by omega⟩)).isLt hyb hqy.symm
    have hw3_eq : (pull1 p hp (w ⟨3, by omega⟩)).val = (2 * (pull1 p hp (w ⟨0, by omega⟩)).val + q.2) % p :=
      hinv _ _ _ (pull1 p hp (w ⟨0, by omega⟩)).isLt (pull1 p hp (w ⟨3, by omega⟩)).isLt hzb hqz.symm
    have hmem_line : ∀ (a b : Fin (p + 2)) (off : Nat),
        (pull1 p hp b).val = (2 * (pull1 p hp a).val + off) % p →
        (a, b) ∈ baumertLineList p hp off := by
      intro a b off hrel
      unfold baumertLineList
      simp only [List.mem_flatMap, List.mem_map]
      refine ⟨pull1 p hp a, List.mem_finRange _, a, hmem_fiber a, b, ?_, rfl⟩
      have hcong : ∀ (x y : Nat) (hx : x < p) (hy : y < p), x = y → fiberPair p hp x hx = fiberPair p hp y hy := by
        intro x y _ _ heq; subst heq; rfl
      rw [← hcong _ _ (pull1 p hp b).isLt (Nat.mod_lt _ (by omega)) hrel]
      exact hmem_fiber b
    unfold baumertExpandList
    simp only [List.mem_flatMap, List.mem_map]
    refine ⟨q, hq, (w ⟨0, by omega⟩, w ⟨3, by omega⟩), hmem_line _ _ q.2 hw3_eq,
                   (w ⟨1, by omega⟩, w ⟨2, by omega⟩), hmem_line _ _ q.1 hw2_eq, ?_⟩
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
    | ⟨3, _⟩ => rfl

/-- Standalone `Nodup` and pairwise independence of `baumertExpandList` (used by Pillar 2 port systems). -/
theorem baumertExpandList_nodup_and_indep (p : Nat) (hp : 9 ≤ p) (Q : List (Nat × Nat))
    (hQbound : ∀ q ∈ Q, q.1 < p ∧ q.2 < p)
    (hQindep : Q.Pairwise (fun q1 q2 => ¬ (cycDist p q1.1 q2.1 ≤ 3 ∧ cycDist p q1.2 q2.2 ≤ 3))) :
    (baumertExpandList p (by omega) Q).Nodup ∧
    ∀ u v, u ∈ baumertExpandList p (by omega) Q → v ∈ baumertExpandList p (by omega) Q →
      u ≠ v → ¬ conflict (strongPow (cycleGraph (p + 2)) 4) u v := by
  have hQnodup : Q.Nodup := by
    apply List.Pairwise.imp _ hQindep
    intro q1 q2 hnc heq; subst heq
    exact hnc ⟨by rw [cycDist_self p _ (by omega)]; omega, by rw [cycDist_self p _ (by omega)]; omega⟩
  have hnodup : (baumertExpandList p (by omega) Q).Nodup := by
    unfold baumertExpandList
    apply list_nodup_flatMap
    · intro q _
      apply list_nodup_flatMap
      · intro uv03 _
        exact list_nodup_map (fun x y h => by
          have h1 : x.1 = y.1 := congrFun h ⟨1, by omega⟩
          have h2 : x.2 = y.2 := congrFun h ⟨2, by omega⟩
          exact Prod.ext h1 h2) (baumertLineList_nodup p (by omega) q.1)
      · apply List.Pairwise.imp_of_mem _ (baumertLineList_nodup p (by omega) q.2)
        intro a1 a2 _ _ hne w hw1 hw2
        simp only [List.mem_map] at hw1 hw2
        rcases hw1 with ⟨b1, _, rfl⟩
        rcases hw2 with ⟨b2, _, heq⟩
        exact hne (Prod.ext (congrFun heq ⟨0, by omega⟩).symm (congrFun heq ⟨3, by omega⟩).symm)
    · apply List.Pairwise.imp_of_mem _ hQnodup
      intro q1 q2 hq1 hq2 hne w hw1 hw2
      simp only [List.mem_flatMap, List.mem_map] at hw1 hw2
      rcases hw1 with ⟨a1, ha1, b1, hb1, rfl⟩
      rcases hw2 with ⟨a2, ha2, b2, hb2, heq⟩
      have h0 : a2.1 = a1.1 := congrFun heq ⟨0, by omega⟩
      have h1 : b2.1 = b1.1 := congrFun heq ⟨1, by omega⟩
      have h2 : b2.2 = b1.2 := congrFun heq ⟨2, by omega⟩
      have h3 : a2.2 = a1.2 := congrFun heq ⟨3, by omega⟩
      have r1y := baumertLineList_mem_rel p (by omega) q1.1 b1 hb1
      have r2y := baumertLineList_mem_rel p (by omega) q2.1 b2 hb2
      have r1z := baumertLineList_mem_rel p (by omega) q1.2 a1 ha1
      have r2z := baumertLineList_mem_rel p (by omega) q2.2 a2 ha2
      rw [h1, h2] at r2y; rw [h0, h3] at r2z
      have ⟨hy1, hz1⟩ := hQbound q1 hq1
      have ⟨hy2, hz2⟩ := hQbound q2 hq2
      have heq_y : q1.1 = q2.1 := by
        rcases int_mod_decomp (2 * (pull1 p (by omega) b1.1).val + q1.1) p (by omega) with ⟨k1, hk1⟩
        rcases int_mod_decomp (2 * (pull1 p (by omega) b1.1).val + q2.1) p (by omega) with ⟨k2, hk2⟩
        have hd : (k1 - k2) * (p : Int) + ((q2.1 : Int) - (q1.1 : Int)) = 0 := by rw [Int.sub_mul]; omega
        have hk := int_mul_eq_zero_of_abs_lt (K := k1 - k2) (n := (p : Int))
          (δ := (q2.1 : Int) - (q1.1 : Int)) (by omega) (by omega) (by omega) hd
        rw [hk, Int.zero_mul] at hd; omega
      have heq_z : q1.2 = q2.2 := by
        rcases int_mod_decomp (2 * (pull1 p (by omega) a1.1).val + q1.2) p (by omega) with ⟨k1, hk1⟩
        rcases int_mod_decomp (2 * (pull1 p (by omega) a1.1).val + q2.2) p (by omega) with ⟨k2, hk2⟩
        have hd : (k1 - k2) * (p : Int) + ((q2.2 : Int) - (q1.2 : Int)) = 0 := by rw [Int.sub_mul]; omega
        have hk := int_mul_eq_zero_of_abs_lt (K := k1 - k2) (n := (p : Int))
          (δ := (q2.2 : Int) - (q1.2 : Int)) (by omega) (by omega) (by omega) hd
        rw [hk, Int.zero_mul] at hd; omega
      exact hne (Prod.ext heq_y heq_z)
  refine ⟨hnodup, ?_⟩
  intro u v hu hv huv hconf
  have hmem_lift : ∀ w ∈ baumertExpandList p (by omega) Q,
      ∃ q ∈ Q, ∃ (hq : q.1 < p ∧ q.2 < p) (a b : Fin p),
        pullVec p 4 (by omega) w = liftHBPZ p (by omega) (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩) a b := by
    intro w hw
    unfold baumertExpandList at hw
    simp only [List.mem_flatMap, List.mem_map] at hw
    rcases hw with ⟨q, hq, uv03, huv03, uv12, huv12, rfl⟩
    refine ⟨q, hq, hQbound q hq, pull1 p (by omega) uv03.1, pull1 p (by omega) uv12.1, ?_⟩
    funext i; match i with
    | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => apply Fin.ext; exact baumertLineList_mem_rel p (by omega) q.1 uv12 huv12
    | ⟨3, _⟩ => apply Fin.ext; exact baumertLineList_mem_rel p (by omega) q.2 uv03 huv03
  rcases hmem_lift u hu with ⟨q1, hq1, hb1, u1, v1, heq1⟩
  rcases hmem_lift v hv with ⟨q2, hq2, hb2, u2, v2, heq2⟩
  have ⟨hpc, hlinj⟩ := (t1f_baumert_pullback_homomorphism p 4 (by omega)).1 u v hconf
  rw [heq1, heq2] at hpc
  have ⟨hqc, hsame⟩ := liftHBPZ_conflict_implies_quot hp _ _ u1 v1 u2 v2 hpc
  have hqeq : q1 = q2 := by
    apply Classical.byContradiction; intro hne
    rw [qGraphHBPZ, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff] at hqc
    have hboth : ∀ a b, a ∈ Q → b ∈ Q → a ≠ b → ¬ (cycDist p a.1 b.1 ≤ 3 ∧ cycDist p a.2 b.2 ≤ 3) := by
      clear hqc hne hsame hpc hlinj heq1 heq2 u1 v1 u2 v2 hb1 hb2 hq1 hq2 hu hv hconf huv u v hnodup hmem_lift hQnodup hQbound
      induction Q with
      | nil => intro _ _ ha; exact nomatch ha
      | cons hd tl ih =>
        rw [List.pairwise_cons] at hQindep
        intro a b ha hb hab
        simp only [List.mem_cons] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hQindep.1 b hb
        · intro ⟨hc1, hc2⟩
          exact hQindep.1 a ha ⟨by rw [cycDist_symm]; exact hc1, by rw [cycDist_symm]; exact hc2⟩
        · exact ih hQindep.2 a b ha hb hab
    exact hboth q1 q2 hq1 hq2 hne hqc
  subst hqeq
  have ⟨ha, hb⟩ := hsame rfl
  subst ha; subst hb
  exact huv (hlinj (by rw [heq1, heq2]))

end
end ZeroErrorFrontier.CosetQuotient
