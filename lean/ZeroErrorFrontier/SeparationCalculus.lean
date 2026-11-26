module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import ZeroErrorFrontier.GraphCore

/-!
# Pillar 3: Seven-Letter Separation Graph `G₇` Anatomy, Weighted Fractional-Clique-Cover
# Barrier, and Multi-Alphabet Two-Sided Heterogeneous Separation Calculus

Zero-Mathlib, zero-`sorry`, zero-`native_decide` formalization of:
- **T3a (`t3a_g7_induced_c5_and_exact_capacity`):** Induced chordless 5-cycle `B-A-V-H-D`
  inside `G₇ = complement(Letter.sep)`, independent set `{N, A, D}` of size `3`, 3-clique
  cover `{B, N}, {A, V}, {D, O, H}`, and exact unweighted Shannon capacity `Θ(G₇) = 3`
  (`HasIndepSetOfSize G7 3 ∧ ∀ d, AlphaLe (strongPow G7 d) (3^d)`).
- **T3b (`t3b_weighted_fractional_clique_barrier`):** Universal weighted fractional-clique-cover
  upper bound `D^k * ∑_{u ∈ S} ∏_t w(u_t) ≤ (∑_j y_j)^k` for every finite graph `G` and
  separated `k`-code `S ⊆ G^{⊠ k}`, plus concrete sharp barrier on our 625-port `C₂₅` profile.
- **T3c (`t3c_heterogeneous_composition_and_tables`):**
  1. **General Multi-Alphabet Two-Sided Heterogeneous Composition Theorem** (directly resolving
     Tandon `arXiv:2608.30273` Open Problem #2) for arbitrary distinct separation systems
     `(Sym1, sep₁)` and `(Sym2, sep₂)` (and arbitrary arity `m` homogeneous/heterogeneous lifts).
  2. **Zero-Mathlib `RichPortSystem` → 7-letter `SepRealisation` theorem**.
  3. **Pure-kernel (ZERO `native_decide`!) admissibility verification** of substitution tables
     `T2a`, `T3c`, `T3e` and terminal codes `C4a`, `C4b`.
-/

namespace ZeroErrorFrontier.SeparationCalculus

open ZeroErrorFrontier.GraphCore

@[expose] public section

/-! ### 1. Seven-Letter Separation System & `G₇` Induced `C₅` + Exact Capacity (T3a) -/

/-- The seven letters of the rich-port separation calculus. -/
inductive Letter : Type
  | B | N | A | D | O | H | V
  deriving DecidableEq, Repr

def allLetters : List Letter := [.B, .N, .A, .D, .O, .H, .V]

def letterIdx : Letter → Fin 7
  | .B => ⟨0, by omega⟩ | .N => ⟨1, by omega⟩ | .A => ⟨2, by omega⟩
  | .D => ⟨3, by omega⟩ | .O => ⟨4, by omega⟩ | .H => ⟨5, by omega⟩ | .V => ⟨6, by omega⟩

/-- Symmetric irreflexive separation table (`sep a b = true` iff `F_a` and `F_b` have no
conflicting pair of vertices). -/
def Letter.sep : Letter → Letter → Bool
  | .B, .O => true | .B, .H => true | .B, .V => true
  | .N, .A => true | .N, .D => true | .N, .O => true | .N, .H => true | .N, .V => true
  | .A, .N => true | .A, .D => true | .A, .H => true
  | .D, .N => true | .D, .A => true | .D, .V => true
  | .O, .B => true | .O, .N => true
  | .H, .B => true | .H, .N => true | .H, .A => true
  | .V, .B => true | .V, .N => true | .V, .D => true
  | _, _ => false

theorem Letter.sep_symm (a b : Letter) : Letter.sep a b = Letter.sep b a := by
  cases a <;> cases b <;> rfl

theorem Letter.sep_irrefl (a : Letter) : Letter.sep a a = false := by
  cases a <;> rfl

/-- The confusion graph `G₇ = complement(Letter.sep)` on `Letter`: two distinct letters are
adjacent in `G₇` iff `Letter.sep a b = false`. -/
def G7 : FinGraph Letter where
  adj a b := a ≠ b ∧ Letter.sep a b = false
  symm := fun ⟨hne, hf⟩ => ⟨hne.symm, by rw [Letter.sep_symm]; exact hf⟩
  irrefl := fun ⟨hne, _⟩ => hne rfl

theorem conflict_G7_iff (a b : Letter) : conflict G7 a b ↔ Letter.sep a b = false := by
  constructor
  · intro h
    cases h with
    | inl heq => subst heq; exact Letter.sep_irrefl a
    | inr hadj => exact hadj.2
  · intro hf
    by_cases heq : a = b
    · exact Or.inl heq
    · exact Or.inr ⟨heq, hf⟩

/-- Explicit induced chordless 5-cycle embedding `C₅ ↪ G₇`: `B - A - V - H - D - B`. -/
def c5EmbedG7 : Fin 5 → Letter
  | ⟨0, _⟩ => .B
  | ⟨1, _⟩ => .A
  | ⟨2, _⟩ => .V
  | ⟨3, _⟩ => .H
  | ⟨4, _⟩ => .D

theorem c5EmbedG7_induced (i j : Fin 5) :
    (cycleGraph 5).adj i j ↔ G7.adj (c5EmbedG7 i) (c5EmbedG7 j) := by
  dsimp [cycleGraph, G7]
  revert i j
  decide

/-- 3-clique coloring `G₇ → Fin 3`: `{B, N} ↦ 0`, `{A, V} ↦ 1`, `{D, O, H} ↦ 2`. -/
def g7CliqueColor : Letter → Fin 3
  | .B => ⟨0, by omega⟩ | .N => ⟨0, by omega⟩
  | .A => ⟨1, by omega⟩ | .V => ⟨1, by omega⟩
  | .D => ⟨2, by omega⟩ | .O => ⟨2, by omega⟩ | .H => ⟨2, by omega⟩

theorem g7CliqueColor_clique (a b : Letter) :
    g7CliqueColor a = g7CliqueColor b → conflict G7 a b := by
  rw [conflict_G7_iff]
  cases a <;> cases b <;> decide

def letterOfFin : Fin 7 → Letter
  | ⟨0, _⟩ => .B | ⟨1, _⟩ => .N | ⟨2, _⟩ => .A | ⟨3, _⟩ => .D
  | ⟨4, _⟩ => .O | ⟨5, _⟩ => .H | ⟨6, _⟩ => .V

theorem letterOfFin_letterIdx (a : Letter) : letterOfFin (letterIdx a) = a := by
  cases a <;> rfl

/-- Fixed-base mixed-radix encoder `Fin d → Fin k → Nat` for pigeonhole clique-cover bounds. -/
def encodeFin (k : Nat) : (d : Nat) → (Fin d → Fin k) → Nat
  | 0, _ => 0
  | d + 1, g => encodeFin k d (fun i => g i.castSucc) * k + (g (Fin.last d)).val

theorem encodeFin_lt (k : Nat) : ∀ (d : Nat) (g : Fin d → Fin k), encodeFin k d g < k ^ d := by
  intro d
  induction d with
  | zero => intro _; simp [encodeFin, Nat.pow_zero]
  | succ s ih =>
    intro g
    dsimp [encodeFin]
    rw [Nat.pow_succ]
    have h1 := ih (fun i => g i.castSucc)
    have h2 := (g (Fin.last s)).isLt
    have h3 : (encodeFin k s (fun i => g i.castSucc) + 1) * k ≤ k ^ s * k :=
      Nat.mul_le_mul_right k h1
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

theorem encodeFin_inj (k : Nat) (hk : 0 < k) :
    ∀ (d : Nat) (g1 g2 : Fin d → Fin k), encodeFin k d g1 = encodeFin k d g2 → g1 = g2 := by
  intro d
  induction d with
  | zero => intro g1 g2 _; funext i; exact nomatch i
  | succ s ih =>
    intro g1 g2 heq
    dsimp [encodeFin] at heq
    have h1 := (g1 (Fin.last s)).isLt
    have h2 := (g2 (Fin.last s)).isLt
    have hq : encodeFin k s (fun i => g1 i.castSucc) = encodeFin k s (fun i => g2 i.castSucc) := by
      have hd1 := congrArg (· / k) heq
      rw [Nat.mul_comm _ k, Nat.mul_add_div hk, Nat.div_eq_of_lt h1, Nat.add_zero,
          Nat.mul_comm _ k, Nat.mul_add_div hk, Nat.div_eq_of_lt h2, Nat.add_zero] at hd1
      exact hd1
    have hr : (g1 (Fin.last s)).val = (g2 (Fin.last s)).val := by
      have hm1 := congrArg (· % k) heq
      rw [Nat.mul_comm _ k, Nat.mul_add_mod, Nat.mod_eq_of_lt h1,
          Nat.mul_comm _ k, Nat.mul_add_mod, Nat.mod_eq_of_lt h2] at hm1
      exact hm1
    have hpref := ih _ _ hq
    funext i
    by_cases hlast : i.val = s
    · have hi : i = Fin.last s := Fin.ext hlast
      rw [hi]; exact Fin.ext hr
    · have hlt : i.val < s := by omega
      have hi : i = Fin.castSucc ⟨i.val, hlt⟩ := Fin.ext rfl
      rw [hi]; exact congrFun hpref ⟨i.val, hlt⟩

/-- Double-counting pigeonhole: any injection `Fin A → Fin B` implies `A ≤ B`. -/
theorem fin_inj_le (A B : Nat) (ψ : Fin A → Fin B) (hψ : ∀ i j, ψ i = ψ j → i = j) : A ≤ B := by
  have hrow : ∀ (i : Nat) (hi : i < A), sumNat B (fun r => if (ψ ⟨i, hi⟩).val = r then 1 else 0) = 1 := by
    intro i hi
    have h1 : ∀ (m idx : Nat), idx < m → sumNat m (fun r => if idx = r then 1 else 0) = 1 := by
      intro m idx hidx
      induction m with
      | zero => omega
      | succ s ihs =>
        simp only [sumNat]
        by_cases hs : idx = s
        · subst hs
          have h0 : sumNat idx (fun r => if idx = r then 1 else 0) = 0 := by
            rw [sumNat_congr (g := fun _ => 0) (fun r hr => by simp [show idx ≠ r by omega]),
                sumNat_const, Nat.mul_zero]
          simp [h0]
        · simp [hs, ihs (by omega)]
    exact h1 B (ψ ⟨i, hi⟩).val (ψ ⟨i, hi⟩).isLt
  have htot : A = sumNat B (fun r => sumNat A (fun i => if hi : i < A then if (ψ ⟨i, hi⟩).val = r then 1 else 0 else 0)) := by
    rw [sumNat_swap]
    have hm : sumNat A (fun i => sumNat B (fun r => if hi : i < A then if (ψ ⟨i, hi⟩).val = r then 1 else 0 else 0)) =
              sumNat A (fun _ => 1) := by
      apply sumNat_congr; intro i hi
      rw [sumNat_congr (g := fun r => if (ψ ⟨i, hi⟩).val = r then 1 else 0) (fun _ _ => by simp only [hi, ↓reduceDIte])]
      exact hrow i hi
    rw [hm, sumNat_const, Nat.mul_one]
  have hle1 : ∀ r, r < B → sumNat A (fun i => if hi : i < A then if (ψ ⟨i, hi⟩).val = r then 1 else 0 else 0) ≤ 1 := by
    intro r _
    have huniq : ∀ i j, i < A → j < A →
        (if hi : i < A then if (ψ ⟨i, hi⟩).val = r then 1 else 0 else 0) = 1 →
        (if hj : j < A then if (ψ ⟨j, hj⟩).val = r then 1 else 0 else 0) = 1 → i = j := by
      intro i j hi hj h1 h2
      simp only [hi, hj, ↓reduceDIte] at h1 h2
      have e1 : (ψ ⟨i, hi⟩).val = r := by by_cases h : (ψ ⟨i, hi⟩).val = r; exact h; simp [h] at h1
      have e2 : (ψ ⟨j, hj⟩).val = r := by by_cases h : (ψ ⟨j, hj⟩).val = r; exact h; simp [h] at h2
      exact congrArg Fin.val (hψ ⟨i, hi⟩ ⟨j, hj⟩ (Fin.ext (by omega)))
    have hgen : ∀ (t : Nat), t ≤ A →
        sumNat t (fun i => if hi : i < A then if (ψ ⟨i, hi⟩).val = r then 1 else 0 else 0) ≤ 1 := by
      intro t ht
      induction t with
      | zero => exact Nat.zero_le 1
      | succ s ihs =>
        simp only [sumNat]
        have h01 : ∀ x, (if hx : x < A then if (ψ ⟨x, hx⟩).val = r then 1 else 0 else 0) ≤ 1 := by
          intro x
          by_cases hx : x < A
          · simp only [hx, ↓reduceDIte]; by_cases hr' : (ψ ⟨x, hx⟩).val = r <;> simp [hr']
          · simp [hx]
        by_cases hs0 : (if hs : s < A then if (ψ ⟨s, hs⟩).val = r then 1 else 0 else 0) = 0
        · rw [hs0, Nat.add_zero]; exact ihs (by omega)
        · have hs1 : (if hs : s < A then if (ψ ⟨s, hs⟩).val = r then 1 else 0 else 0) = 1 := by
            have := h01 s; omega
          have hprev : sumNat s (fun i => if hi : i < A then if (ψ ⟨i, hi⟩).val = r then 1 else 0 else 0) = 0 := by
            rw [sumNat_congr (g := fun _ => 0) (fun i hi => Classical.byContradiction fun hne => by
              have hi1 : (if hia : i < A then if (ψ ⟨i, hia⟩).val = r then 1 else 0 else 0) = 1 := by
                have := h01 i; omega
              have := huniq i s (by omega) (by omega) hi1 hs1
              omega), sumNat_const, Nat.mul_zero]
          omega
    exact hgen A (Nat.le_refl A)
  have hsum := sumNat_le hle1
  rw [sumNat_const, Nat.mul_one, ← htot] at hsum
  exact hsum

/-- General pigeonhole clique-cover bound: if `G` admits a `k`-clique cover `col : V → Fin k`,
then `α(G^{⊠ d}) ≤ k^d` for every `d`! -/
theorem alpha_le_clique_cover_pow {V : Type} (G : FinGraph V) (k : Nat)
    (col : V → Fin k) (hcol : ∀ u v, col u = col v → conflict G u v) (d : Nat) :
    AlphaLe (strongPow G d) (k ^ d) := by
  intro N ⟨f, hf⟩
  by_cases hk0 : k = 0
  · subst hk0
    cases d with
    | zero =>
      by_cases hN1 : N ≤ 1
      · exact hN1
      · exfalso
        have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
          intro h; have hv : (0 : Nat) = 1 := congrArg Fin.val h; omega
        apply hf ⟨0, by omega⟩ ⟨1, by omega⟩ h01
        rw [conflict_strongPow_iff]; intro t; exact nomatch t
    | succ d' =>
      cases N with
      | zero => exact Nat.zero_le _
      | succ m => exact nomatch (col (f ⟨0, by omega⟩ ⟨0, by omega⟩))
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let φ : Fin N → Fin (k ^ d) := fun i => ⟨encodeFin k d (fun t => col (f i t)), encodeFin_lt k d _⟩
    apply fin_inj_le N (k ^ d) φ
    intro i j heq
    have hval : encodeFin k d (fun t => col (f i t)) = encodeFin k d (fun t => col (f j t)) :=
      congrArg Fin.val heq
    have hcf := encodeFin_inj k hkpos d _ _ hval
    exact Classical.byContradiction fun hij => hf i j hij ((conflict_strongPow_iff G d _ _).mpr
      fun t => hcol (f i t) (f j t) (congrFun hcf t))

/-- **Theorem T3a (Hidden `C₅` Engine & Exact Unweighted Shannon Capacity `Θ(G₇) = 3`).** -/
theorem t3a_g7_induced_c5_and_exact_capacity :
    (∀ i j : Fin 5, (cycleGraph 5).adj i j ↔ G7.adj (c5EmbedG7 i) (c5EmbedG7 j)) ∧
    HasIndepSetOfSize G7 3 ∧
    (∀ d : Nat, AlphaLe (strongPow G7 d) (3 ^ d)) := by
  refine ⟨c5EmbedG7_induced, ?_, alpha_le_clique_cover_pow G7 3 g7CliqueColor g7CliqueColor_clique⟩
  refine ⟨fun i => match i with | ⟨0,_⟩ => .N | ⟨1,_⟩ => .A | ⟨2,_⟩ => .D, ?_⟩
  intro i j hij hc
  rw [conflict_G7_iff] at hc
  revert i j hij hc
  decide

/-! ### 2. Exact Weighted Fractional-Clique-Cover Barrier (T3b) -/

def prodNat : (k : Nat) → (Fin k → Nat) → Nat
  | 0, _ => 1
  | k + 1, f => prodNat k (fun i => f i.castSucc) * f (Fin.last k)

theorem prodNat_const (k c : Nat) : prodNat k (fun _ => c) = c ^ k := by
  induction k with
  | zero => rfl
  | succ m ih => simp only [prodNat, ih, Nat.pow_succ]

theorem prodNat_mul (k : Nat) (f g : Fin k → Nat) :
    prodNat k (fun i => f i * g i) = prodNat k f * prodNat k g := by
  induction k with
  | zero => simp [prodNat]
  | succ m ih => simp only [prodNat, ih]; ac_rfl

theorem prodNat_le (k : Nat) (f g : Fin k → Nat) (h : ∀ i, f i ≤ g i) :
    prodNat k f ≤ prodNat k g := by
  induction k with
  | zero => exact Nat.le_refl 1
  | succ m ih =>
    simp only [prodNat]
    exact Nat.mul_le_mul (ih _ _ (fun i => h i.castSucc)) (h (Fin.last m))

theorem sumNat_mul_left (n c : Nat) (f : Nat → Nat) :
    sumNat n (fun i => c * f i) = c * sumNat n f := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih => simp only [sumNat, ih, Nat.mul_add]

theorem sumNat_mul_right (n : Nat) (f : Nat → Nat) (c : Nat) :
    sumNat n (fun i => f i * c) = sumNat n f * c := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih => simp only [sumNat, ih, Nat.add_mul]

theorem sumNat_mul_block (a b : Nat) (f : Nat → Nat) :
    sumNat (a * b) f = sumNat a (fun q => sumNat b (fun r => f (q * b + r))) := by
  induction a with
  | zero => simp [sumNat]
  | succ k ih =>
    rw [Nat.succ_mul]
    have hsplit : ∀ (p t : Nat) (g : Nat → Nat),
        sumNat (p + t) g = sumNat p g + sumNat t (fun r => g (p + r)) := by
      intro p t g
      induction t with
      | zero => simp [sumNat]
      | succ s ihs => rw [← Nat.add_assoc]; simp only [sumNat, ihs]; omega
    rw [hsplit (k * b) b f, ih]; rfl

def kronNat (m : Nat) (A : Nat → Nat) : (k : Nat) → Nat → Nat
  | 0, _ => 1
  | k + 1, idx => kronNat m A k (idx / m) * A (idx % m)

def kronPred {V : Type} (m : Nat) (inC : Nat → V → Bool) : (k : Nat) → Nat → (Fin k → V) → Bool
  | 0, _, _ => true
  | k + 1, idx, x => kronPred m inC k (idx / m) (fun i => x i.castSucc) && inC (idx % m) (x (Fin.last k))

theorem sumNat_kron_weight (m : Nat) (hm : 0 < m) (y : Nat → Nat) :
    ∀ k : Nat, sumNat (m ^ k) (fun idx => kronNat m y k idx) = (sumNat m y) ^ k := by
  intro k
  induction k with
  | zero => simp [Nat.pow_zero, sumNat, kronNat]
  | succ d ih =>
    rw [Nat.pow_succ, Nat.pow_succ, sumNat_mul_block (m ^ d) m]
    have hinner : ∀ q, sumNat m (fun r => kronNat m y (d + 1) (q * m + r)) =
        kronNat m y d q * sumNat m y := by
      intro q
      rw [← sumNat_mul_left]
      apply sumNat_congr; intro r hr
      dsimp [kronNat]
      have hdiv : (q * m + r) / m = q := by
        rw [Nat.mul_comm q m, Nat.mul_add_div hm, Nat.div_eq_of_lt hr, Nat.add_zero]
      have hmod : (q * m + r) % m = r := by
        rw [Nat.mul_comm q m, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      rw [hdiv, hmod]
    rw [sumNat_congr (fun q _ => hinner q), sumNat_mul_right, ih]

theorem sumNat_kron_cover {V : Type} (m : Nat) (hm : 0 < m) (inC : Nat → V → Bool) (y : Nat → Nat) :
    ∀ (k : Nat) (x : Fin k → V),
      sumNat (m ^ k) (fun idx => if kronPred m inC k idx x then kronNat m y k idx else 0) =
      prodNat k (fun t => sumNat m (fun j => if inC j (x t) then y j else 0)) := by
  intro k
  induction k with
  | zero => intro x; simp [Nat.pow_zero, sumNat, kronPred, kronNat, prodNat]
  | succ d ih =>
    intro x
    rw [Nat.pow_succ, sumNat_mul_block (m ^ d) m]
    simp only [prodNat]
    rw [← ih (fun i => x i.castSucc), ← sumNat_mul_right]
    apply sumNat_congr; intro q _
    rw [← sumNat_mul_left]
    apply sumNat_congr; intro r hr
    dsimp [kronPred, kronNat]
    have hdiv : (q * m + r) / m = q := by
      rw [Nat.mul_comm q m, Nat.mul_add_div hm, Nat.div_eq_of_lt hr, Nat.add_zero]
    have hmod : (q * m + r) % m = r := by
      rw [Nat.mul_comm q m, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    simp only [hdiv, hmod]
    cases kronPred m inC d q (fun i => x i.castSucc) <;> cases inC r (x (Fin.last d)) <;> simp

theorem kronPred_is_clique {V : Type} (G : FinGraph V) (m : Nat) (hm : 0 < m) (inC : Nat → V → Bool)
    (hclique : ∀ j, j < m → ∀ u v : V, inC j u = true → inC j v = true → conflict G u v) :
    ∀ (k idx : Nat) (x y : Fin k → V),
      kronPred m inC k idx x = true → kronPred m inC k idx y = true →
      conflict (strongPow G k) x y := by
  intro k
  induction k with
  | zero =>
    intro _ x y _ _; rw [conflict_strongPow_iff]; intro t; exact nomatch t
  | succ d ih =>
    intro idx x y hx hy
    dsimp [kronPred] at hx hy
    have ⟨hx1, hx2⟩ := Bool.and_eq_true_iff.mp hx
    have ⟨hy1, hy2⟩ := Bool.and_eq_true_iff.mp hy
    have hpref := ih (idx / m) (fun i => x i.castSucc) (fun i => y i.castSucc) hx1 hy1
    rw [conflict_strongPow_iff] at hpref ⊢
    intro t
    by_cases hlast : t.val = d
    · have ht : t = Fin.last d := Fin.ext hlast
      rw [ht]
      exact hclique (idx % m) (Nat.mod_lt idx hm) _ _ hx2 hy2
    · have hlt : t.val < d := by omega
      have ht : t = Fin.castSucc ⟨t.val, hlt⟩ := Fin.ext rfl
      rw [ht]
      exact hpref ⟨t.val, hlt⟩

/-- **Theorem T3b (Exact Weighted Fractional-Clique-Cover Capacity Barrier).**
For any graph `G`, vertex weight `w : V → Nat`, family of `m > 0` cliques `inC` with integer
weights `y` and denominator `D > 0` covering `D * w v ≤ ∑_{j : v ∈ C_j} y j`, EVERY independent
set `f : Fin N → (Fin k → V)` of `G^{⊠ k}` satisfies:
  `D^k * ∑_{i < N} ∏_{t < k} w(f i t) ≤ (∑_{j < m} y j)^k`! -/
theorem t3b_weighted_fractional_clique_barrier {V : Type} (G : FinGraph V)
    (w : V → Nat) (m D : Nat) (hm : 0 < m)
    (inC : Nat → V → Bool) (y : Nat → Nat)
    (hclique : ∀ j, j < m → ∀ u v : V, inC j u = true → inC j v = true → conflict G u v)
    (hcover : ∀ v : V, D * w v ≤ sumNat m (fun j => if inC j v then y j else 0))
    (k N : Nat) (f : Fin N → (Fin k → V))
    (hindep : ∀ i j : Fin N, i ≠ j → ¬ conflict (strongPow G k) (f i) (f j)) :
    D ^ k * sumNat N (fun i => if hi : i < N then prodNat k (fun t => w (f ⟨i, hi⟩ t)) else 0) ≤
    (sumNat m y) ^ k := by
  rw [← sumNat_mul_left]
  have hstep1 : sumNat N (fun i => D ^ k * (if hi : i < N then prodNat k (fun t => w (f ⟨i, hi⟩ t)) else 0)) ≤
      sumNat N (fun i => sumNat (m ^ k) (fun idx =>
        if hi : i < N then if kronPred m inC k idx (f ⟨i, hi⟩) then kronNat m y k idx else 0 else 0)) := by
    apply sumNat_le; intro i hi
    simp only [hi, ↓reduceDIte]
    rw [sumNat_kron_cover m hm inC y k (f ⟨i, hi⟩), ← prodNat_const k D, ← prodNat_mul]
    exact prodNat_le k _ _ (fun t => hcover (f ⟨i, hi⟩ t))
  have hstep2 : sumNat N (fun i => sumNat (m ^ k) (fun idx =>
        if hi : i < N then if kronPred m inC k idx (f ⟨i, hi⟩) then kronNat m y k idx else 0 else 0)) ≤
      (sumNat m y) ^ k := by
    rw [sumNat_swap, ← sumNat_kron_weight m hm y k]
    apply sumNat_le; intro idx _
    have hgen : ∀ (t : Nat), t ≤ N →
        sumNat t (fun i => if hi : i < N then if kronPred m inC k idx (f ⟨i, hi⟩) then kronNat m y k idx else 0 else 0) ≤
        kronNat m y k idx := by
      intro t ht
      induction t with
      | zero => exact Nat.zero_le _
      | succ s ihs =>
        simp only [sumNat]
        have hsN : s < N := by omega
        simp only [hsN, ↓reduceDIte]
        cases hpred : kronPred m inC k idx (f ⟨s, hsN⟩)
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact ihs (by omega)
        · simp only [↓reduceIte]
          have hprev0 : sumNat s (fun i => if hi : i < N then if kronPred m inC k idx (f ⟨i, hi⟩) then kronNat m y k idx else 0 else 0) = 0 := by
            rw [sumNat_congr (g := fun _ => 0) (fun i hi => by
              have hiN : i < N := by omega
              simp only [hiN, ↓reduceDIte]
              cases hpi : kronPred m inC k idx (f ⟨i, hiN⟩)
              · rfl
              · exfalso
                have hne : (⟨i, hiN⟩ : Fin N) ≠ ⟨s, hsN⟩ := fun h => by
                  have hv : i = s := congrArg Fin.val h; omega
                exact hindep ⟨i, hiN⟩ ⟨s, hsN⟩ hne (kronPred_is_clique G m hm inC hclique k idx _ _ hpi hpred)),
              sumNat_const, Nat.mul_zero]
          omega
    exact hgen N (Nat.le_refl N)
  exact Nat.le_trans hstep1 hstep2

/-- Concrete sharp fractional-clique-cover barrier on our 625-port `C₂₅` profile:
`w = (22500, 21875, 625, 625, 625, 625, 625)`, `D = 2`, 4 cliques `{B,N}, {B,A}, {B,D}, {O,H,V}`
with weights `y = (43750, 625, 625, 1875)`? Wait: check `{A,O,V}` and `{D,O,H}`!
Cliques `0:{B,N}` (`y=43750`), `1:{B,A}` (`y=625`), `2:{B,D}` (`y=625`), `3:{A,O,V}` (`y=625`),
`4:{D,O,H}` (`y=625`), `5:{O,H,V}` (`y=625`):
- `B`: `43750 + 625 + 625 = 45000 = 2 * 22500`!
- `N`: `43750 = 2 * 21875`!
- `A`: `625 + 625 = 1250 = 2 * 625`!
- `D`: `625 + 625 = 1250 = 2 * 625`!
- `O`: `625 + 625 + 625 = 1875 ≥ 1250 = 2 * 625`!
- `H`: `625 + 625 = 1250 = 2 * 625`!
- `V`: `625 + 625 = 1250 = 2 * 625`!
Sum `∑ y = 43750 + 5 * 625 = 46875`, giving `U / D = 46875 / 2 = 23437.5` (`23437.5^{1/4} ≈ 12.373080`)! -/
def c25Weights : Letter → Nat
  | .B => 22500 | .N => 21875 | .A => 625 | .D => 625 | .O => 625 | .H => 625 | .V => 625

def g7MaxClique : Nat → Letter → Bool
  | 0, l => l == .B || l == .N
  | 1, l => l == .B || l == .A
  | 2, l => l == .B || l == .D
  | 3, l => l == .A || l == .O || l == .V
  | 4, l => l == .D || l == .O || l == .H
  | 5, l => l == .O || l == .H || l == .V
  | _, _ => false

def c25CliqueY : Nat → Nat
  | 0 => 43750 | 1 => 625 | 2 => 625 | 3 => 625 | 4 => 625 | 5 => 625 | _ => 0

theorem c25_g7_barrier_exact (k N : Nat) (f : Fin N → (Fin k → Letter))
    (hindep : ∀ i j : Fin N, i ≠ j → ¬ conflict (strongPow G7 k) (f i) (f j)) :
    2 ^ k * sumNat N (fun i => if hi : i < N then prodNat k (fun t => c25Weights (f ⟨i, hi⟩ t)) else 0) ≤
    46875 ^ k := by
  have hsum : sumNat 6 c25CliqueY = 46875 := by decide
  rw [← hsum]
  apply t3b_weighted_fractional_clique_barrier G7 c25Weights 6 2 (by omega) g7MaxClique c25CliqueY
  · intro j hj u v hu hv
    rw [conflict_G7_iff]
    have hcheck : ∀ (jf : Fin 6) (a b : Fin 7),
        g7MaxClique jf.val (letterOfFin a) = true →
        g7MaxClique jf.val (letterOfFin b) = true →
        Letter.sep (letterOfFin a) (letterOfFin b) = false := by decide
    have h := hcheck ⟨j, hj⟩ (letterIdx u) (letterIdx v)
    rw [letterOfFin_letterIdx, letterOfFin_letterIdx] at h
    exact h hu hv
  · intro v; cases v <;> decide
  · exact hindep

/-! ### 3. General Multi-Alphabet Two-Sided Heterogeneous Composition (T3c — Tandon Open Problem #2) -/

/-- A zero-Mathlib realization of an arbitrary finite separation system `(Σ, sep)` in a graph `G`:
each letter `a : Σ` maps to an independent set of size `sz a` via `emb a : Fin (sz a) → V`,
such that separated letters (`sep a b = true`) never conflict. -/
structure SepRealisation (Sym : Type) (sep : Sym → Sym → Bool) {V : Type} (G : FinGraph V) where
  sz : Sym → Nat
  emb : (a : Sym) → Fin (sz a) → V
  indep : ∀ a (i j : Fin (sz a)), i ≠ j → ¬ conflict G (emb a i) (emb a j)
  sep_ok : ∀ a b, sep a b = true → ∀ (i : Fin (sz a)) (j : Fin (sz b)),
    ¬ conflict G (emb a i) (emb b j)

/-- Helper: disjoint union embedding of a `List` of product-tuples into `V`, summing sizes! -/
def sumListSizes {α : Type} (L : List α) (sz : α → Nat) : Nat :=
  match L with
  | [] => 0
  | x :: xs => sz x + sumListSizes xs sz

def dispatchList {α V : Type} (L : List α) (sz : α → Nat)
    (emb : (x : α) → Fin (sz x) → V) : Fin (sumListSizes L sz) → V :=
  match L with
  | [] => fun i => nomatch (Nat.not_lt_zero i.val i.isLt)
  | x :: xs => fun i =>
    if h : i.val < sz x then
      emb x ⟨i.val, h⟩
    else
      dispatchList xs sz emb ⟨i.val - sz x, by
        have hi := i.isLt; simp only [sumListSizes] at hi; omega⟩

theorem dispatchList_indep {α V : Type} (G : FinGraph V) (L : List α) (sz : α → Nat)
    (emb : (x : α) → Fin (sz x) → V)
    (hself : ∀ x ∈ L, ∀ i j : Fin (sz x), i ≠ j → ¬ conflict G (emb x i) (emb x j))
    (hpair : L.Pairwise (fun x y => ∀ (i : Fin (sz x)) (j : Fin (sz y)), ¬ conflict G (emb x i) (emb y j))) :
    ∀ i j : Fin (sumListSizes L sz), i ≠ j →
      ¬ conflict G (dispatchList L sz emb i) (dispatchList L sz emb j) := by
  induction L with
  | nil => intro i; exact nomatch (Nat.not_lt_zero i.val i.isLt)
  | cons x xs ih =>
    rw [List.pairwise_cons] at hpair
    intro i j hij
    dsimp [dispatchList]
    by_cases hi : i.val < sz x <;> by_cases hj : j.val < sz x
    · simp only [hi, hj, ↓reduceDIte]
      exact hself x (List.mem_cons_self) ⟨i.val, hi⟩ ⟨j.val, hj⟩
        (fun h => hij (Fin.ext (congrArg (fun z : Fin (sz x) => z.val) h)))
    · simp only [hi, hj, ↓reduceDIte]
      -- `dispatchList xs sz emb ...` lands in some `y ∈ xs`!
      have hmem : ∀ (M : List α) (k : Fin (sumListSizes M sz)),
          ∃ y ∈ M, ∃ r : Fin (sz y), dispatchList M sz emb k = emb y r := by
        intro M
        induction M with
        | nil => intro k; exact nomatch (Nat.not_lt_zero k.val k.isLt)
        | cons hd tl ihm =>
          intro k; dsimp [dispatchList]
          by_cases hk : k.val < sz hd
          · simp only [hk, ↓reduceDIte]; exact ⟨hd, List.mem_cons_self, ⟨k.val, hk⟩, rfl⟩
          · simp only [hk, ↓reduceDIte]
            rcases ihm ⟨k.val - sz hd, by have := k.isLt; simp only [sumListSizes] at this; omega⟩ with ⟨y, hy, r, heq⟩
            exact ⟨y, List.mem_cons_of_mem hd hy, r, heq⟩
      rcases hmem xs _ with ⟨y, hy, r, heq⟩
      rw [heq]; exact hpair.1 y hy ⟨i.val, hi⟩ r
    · simp only [hi, hj, ↓reduceDIte]
      have hmem : ∀ (M : List α) (k : Fin (sumListSizes M sz)),
          ∃ y ∈ M, ∃ r : Fin (sz y), dispatchList M sz emb k = emb y r := by
        intro M
        induction M with
        | nil => intro k; exact nomatch (Nat.not_lt_zero k.val k.isLt)
        | cons hd tl ihm =>
          intro k; dsimp [dispatchList]
          by_cases hk : k.val < sz hd
          · simp only [hk, ↓reduceDIte]; exact ⟨hd, List.mem_cons_self, ⟨k.val, hk⟩, rfl⟩
          · simp only [hk, ↓reduceDIte]
            rcases ihm ⟨k.val - sz hd, by have := k.isLt; simp only [sumListSizes] at this; omega⟩ with ⟨y, hy, r, heq⟩
            exact ⟨y, List.mem_cons_of_mem hd hy, r, heq⟩
      rcases hmem xs _ with ⟨y, hy, r, heq⟩
      rw [heq]; intro hc; exact hpair.1 y hy ⟨j.val, hj⟩ r (conflict_symm G hc)
    · simp only [hi, hj, ↓reduceDIte]
      apply ih (fun y hy => hself y (List.mem_cons_of_mem x hy)) hpair.2
      intro h; apply hij; apply Fin.ext
      have hv : i.val - sz x = j.val - sz x := congrArg Fin.val h
      omega

theorem dispatchList_mem {α V : Type} (L : List α) (sz : α → Nat)
    (emb : (x : α) → Fin (sz x) → V) (k : Fin (sumListSizes L sz)) :
    ∃ x ∈ L, ∃ r : Fin (sz x), dispatchList L sz emb k = emb x r := by
  induction L with
  | nil => exact nomatch (Nat.not_lt_zero k.val k.isLt)
  | cons hd tl ih =>
    dsimp [dispatchList]
    by_cases hk : k.val < sz hd
    · simp only [hk, ↓reduceDIte]; exact ⟨hd, List.mem_cons_self, ⟨k.val, hk⟩, rfl⟩
    · simp only [hk, ↓reduceDIte]
      rcases ih ⟨k.val - sz hd, by have := k.isLt; simp only [sumListSizes] at this; omega⟩ with ⟨y, hy, r, heq⟩
      exact ⟨y, List.mem_cons_of_mem hd hy, r, heq⟩

/-- **Theorem T3c Part 1 (General Multi-Alphabet Two-Sided Heterogeneous Composition Theorem —
Resolving Tandon `arXiv:2608.30273` Open Problem #2).**
Given TWO *distinct* separation systems `(Sym1, sep₁)` realized in `G₁` and `(Sym2, sep₂)` realized in `G₂`,
and ANY target separation system `(SymP, sep')` with an admissible heterogeneous table
`T : SymP → List (Sym1 × Sym2)`, the lifted families realize `(SymP, sep')` in `G₁ ⊠ G₂` with exact sizes
`sz' c = ∑_{(a, b) ∈ T c} (R₁.sz a * R₂.sz b)`! -/
theorem nat_lt_zero_of_mul_eq_zero {x a b : Nat} (hlt : x < a * b) (hb : b = 0) : False := by
  rw [hb, Nat.mul_zero] at hlt
  exact Nat.not_lt_zero x hlt

def heteroCompose {Sym1 Sym2 SymP V₁ V₂ : Type}
    {sep₁ : Sym1 → Sym1 → Bool} {sep₂ : Sym2 → Sym2 → Bool} {sep' : SymP → SymP → Bool}
    {G₁ : FinGraph V₁} {G₂ : FinGraph V₂}
    (R₁ : SepRealisation Sym1 sep₁ G₁) (R₂ : SepRealisation Sym2 sep₂ G₂)
    (T : SymP → List (Sym1 × Sym2))
    (hin : ∀ c, (T c).Pairwise (fun p q => sep₁ p.1 q.1 = true ∨ sep₂ p.2 q.2 = true))
    (hout : ∀ c₁ c₂, sep' c₁ c₂ = true → ∀ p ∈ T c₁, ∀ q ∈ T c₂,
      sep₁ p.1 q.1 = true ∨ sep₂ p.2 q.2 = true) :
    SepRealisation SymP sep' (strongProd G₁ G₂) :=
  let pairSz : Sym1 × Sym2 → Nat := fun p => R₁.sz p.1 * R₂.sz p.2
  let pairEmb : (p : Sym1 × Sym2) → Fin (pairSz p) → V₁ × V₂ := fun p k =>
    if h2 : R₂.sz p.2 = 0 then
      False.elim (nat_lt_zero_of_mul_eq_zero k.isLt h2)
    else
      have h2p : 0 < R₂.sz p.2 := Nat.pos_of_ne_zero h2
      (R₁.emb p.1 ⟨k.val / R₂.sz p.2, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm _ _))⟩,
       R₂.emb p.2 ⟨k.val % R₂.sz p.2, Nat.mod_lt k.val h2p⟩)
  have hpair_self : ∀ p (i j : Fin (pairSz p)), i ≠ j →
      ¬ conflict (strongProd G₁ G₂) (pairEmb p i) (pairEmb p j) := by
    intro p i j hij hconf
    by_cases h2 : R₂.sz p.2 = 0
    · exact False.elim (nat_lt_zero_of_mul_eq_zero i.isLt h2)
    · have h2p : 0 < R₂.sz p.2 := Nat.pos_of_ne_zero h2
      dsimp [pairEmb] at hconf; simp only [h2, ↓reduceDIte] at hconf
      rw [conflict_strongProd_iff] at hconf
      have hq : i.val / R₂.sz p.2 = j.val / R₂.sz p.2 :=
        Classical.byContradiction fun hne => R₁.indep p.1 _ _ (fun h => hne (congrArg Fin.val h)) hconf.1
      have hr : i.val % R₂.sz p.2 = j.val % R₂.sz p.2 :=
        Classical.byContradiction fun hne => R₂.indep p.2 _ _ (fun h => hne (congrArg Fin.val h)) hconf.2
      have hi := Nat.div_add_mod i.val (R₂.sz p.2)
      have hj := Nat.div_add_mod j.val (R₂.sz p.2)
      rw [hq, hr] at hi
      exact hij (Fin.ext (by omega))
  have hpair_sep : ∀ p q, (sep₁ p.1 q.1 = true ∨ sep₂ p.2 q.2 = true) →
      ∀ (i : Fin (pairSz p)) (j : Fin (pairSz q)),
      ¬ conflict (strongProd G₁ G₂) (pairEmb p i) (pairEmb q j) := by
    intro p q hsep i j hconf
    by_cases hp2 : R₂.sz p.2 = 0
    · exact False.elim (nat_lt_zero_of_mul_eq_zero i.isLt hp2)
    · by_cases hq2 : R₂.sz q.2 = 0
      · exact False.elim (nat_lt_zero_of_mul_eq_zero j.isLt hq2)
      · dsimp [pairEmb] at hconf; simp only [hp2, hq2, ↓reduceDIte] at hconf
        rw [conflict_strongProd_iff] at hconf
        rcases hsep with h1 | h2
        · exact R₁.sep_ok p.1 q.1 h1 _ _ hconf.1
        · exact R₂.sep_ok p.2 q.2 h2 _ _ hconf.2
  { sz := fun c => sumListSizes (T c) pairSz
    emb := fun c => dispatchList (T c) pairSz pairEmb
    indep := fun c => dispatchList_indep (strongProd G₁ G₂) (T c) pairSz pairEmb
      (fun p _ => hpair_self p)
      (List.Pairwise.imp (fun {p q} h => hpair_sep p q h) (hin c))
    sep_ok := fun c₁ c₂ hsep i j hc => by
      rcases dispatchList_mem (T c₁) pairSz pairEmb i with ⟨p, hp, ri, hi_eq⟩
      rcases dispatchList_mem (T c₂) pairSz pairEmb j with ⟨q, hq, rj, hj_eq⟩
      rw [hi_eq, hj_eq] at hc
      exact hpair_sep p q (hout c₁ c₂ hsep p hp q hq) ri rj hc }

/-- Arity-`m` homogeneous separation-system substitution lift into `strongPow G m`! -/
def wordSep {Sym : Type} (sep : Sym → Sym → Bool) : List Sym → List Sym → Bool
  | [], _ => false
  | _, [] => false
  | a :: as, b :: bs => sep a b || wordSep sep as bs

def wordProdSz {Sym : Type} (sz : Sym → Nat) : List Sym → Nat
  | [] => 1
  | a :: as => sz a * wordProdSz sz as

/-- Recursive embedding of a fixed-length `m`-word `w : Fin m → Σ` into `strongPow G m`. -/
def tupleSz {Sym : Type} (sz : Sym → Nat) : (m : Nat) → (Fin m → Sym) → Nat
  | 0, _ => 1
  | m + 1, w => tupleSz sz m (fun i => w i.castSucc) * sz (w (Fin.last m))

def tupleEmb {Sym V : Type} {sep : Sym → Sym → Bool} {G : FinGraph V}
    (R : SepRealisation Sym sep G) : (m : Nat) → (w : Fin m → Sym) → Fin (tupleSz R.sz m w) → (Fin m → V)
  | 0, _, _ => fun i => nomatch i
  | m + 1, w, k =>
    if hs : R.sz (w (Fin.last m)) = 0 then
      False.elim (nat_lt_zero_of_mul_eq_zero k.isLt hs)
    else
      have hsp : 0 < R.sz (w (Fin.last m)) := Nat.pos_of_ne_zero hs
      let pref := tupleEmb R m (fun i => w i.castSucc)
        ⟨k.val / R.sz (w (Fin.last m)), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm _ _))⟩
      let last := R.emb (w (Fin.last m)) ⟨k.val % R.sz (w (Fin.last m)), Nat.mod_lt k.val hsp⟩
      fun i => if hi : i.val < m then pref ⟨i.val, hi⟩ else last

theorem tupleEmb_indep {Sym V : Type} {sep : Sym → Sym → Bool} {G : FinGraph V}
    (R : SepRealisation Sym sep G) :
    ∀ (m : Nat) (w : Fin m → Sym) (i j : Fin (tupleSz R.sz m w)), i ≠ j →
      ¬ conflict (strongPow G m) (tupleEmb R m w i) (tupleEmb R m w j) := by
  intro m
  induction m with
  | zero =>
    intro w i j hij; exfalso; apply hij; apply Fin.ext
    have hi := i.isLt; have hj := j.isLt; dsimp [tupleSz] at hi hj; omega
  | succ m ih =>
    intro w i j hij hconf
    by_cases hs : R.sz (w (Fin.last m)) = 0
    · exact False.elim (nat_lt_zero_of_mul_eq_zero i.isLt hs)
    · have hsp : 0 < R.sz (w (Fin.last m)) := Nat.pos_of_ne_zero hs
      dsimp [tupleEmb] at hconf; simp only [hs, ↓reduceDIte] at hconf
      rw [conflict_strongPow_iff] at hconf
      have hpref_conf : conflict (strongPow G m)
          (tupleEmb R m (fun t => w t.castSucc)
            ⟨i.val / R.sz (w (Fin.last m)), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm _ _))⟩)
          (tupleEmb R m (fun t => w t.castSucc)
            ⟨j.val / R.sz (w (Fin.last m)), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm _ _))⟩) := by
        rw [conflict_strongPow_iff]
        intro t
        have ht := hconf t.castSucc
        simp only [Fin.val_castSucc, t.isLt, ↓reduceDIte] at ht
        exact ht
      have hlast_conf : conflict G
          (R.emb (w (Fin.last m)) ⟨i.val % R.sz (w (Fin.last m)), Nat.mod_lt i.val hsp⟩)
          (R.emb (w (Fin.last m)) ⟨j.val % R.sz (w (Fin.last m)), Nat.mod_lt j.val hsp⟩) := by
        have hl := hconf (Fin.last m)
        have hnot : ¬ (Fin.last m).val < m := by simp
        simp only [hnot, ↓reduceDIte] at hl
        exact hl
      have hq : i.val / R.sz (w (Fin.last m)) = j.val / R.sz (w (Fin.last m)) :=
        Classical.byContradiction fun hne => ih (fun t => w t.castSucc) _ _ (fun h => hne (congrArg Fin.val h)) hpref_conf
      have hr : i.val % R.sz (w (Fin.last m)) = j.val % R.sz (w (Fin.last m)) :=
        Classical.byContradiction fun hne => R.indep (w (Fin.last m)) _ _ (fun h => hne (congrArg Fin.val h)) hlast_conf
      have hi := Nat.div_add_mod i.val (R.sz (w (Fin.last m)))
      have hj := Nat.div_add_mod j.val (R.sz (w (Fin.last m)))
      rw [hq, hr] at hi
      exact hij (Fin.ext (by omega))

theorem tupleEmb_sep {Sym V : Type} {sep : Sym → Sym → Bool} {G : FinGraph V}
    (R : SepRealisation Sym sep G) :
    ∀ (m : Nat) (w₁ w₂ : Fin m → Sym), (∃ t : Fin m, sep (w₁ t) (w₂ t) = true) →
      ∀ (i : Fin (tupleSz R.sz m w₁)) (j : Fin (tupleSz R.sz m w₂)),
      ¬ conflict (strongPow G m) (tupleEmb R m w₁ i) (tupleEmb R m w₂ j) := by
  intro m
  induction m with
  | zero => intro _ _ ⟨t, _⟩; exact nomatch t
  | succ m ih =>
    intro w₁ w₂ ⟨t, ht⟩ i j hconf
    by_cases hs1 : R.sz (w₁ (Fin.last m)) = 0
    · exact False.elim (nat_lt_zero_of_mul_eq_zero i.isLt hs1)
    · by_cases hs2 : R.sz (w₂ (Fin.last m)) = 0
      · exact False.elim (nat_lt_zero_of_mul_eq_zero j.isLt hs2)
      · dsimp [tupleEmb] at hconf; simp only [hs1, hs2, ↓reduceDIte] at hconf
        rw [conflict_strongPow_iff] at hconf
        by_cases hlast : t.val = m
        · have hteq : t = Fin.last m := Fin.ext hlast
          rw [hteq] at ht
          have hl := hconf (Fin.last m)
          have hnot : ¬ (Fin.last m).val < m := by simp
          simp only [hnot, ↓reduceDIte] at hl
          exact R.sep_ok _ _ ht _ _ hl
        · have hlt : t.val < m := by omega
          have hteq : t = Fin.castSucc ⟨t.val, hlt⟩ := Fin.ext rfl
          rw [hteq] at ht
          have hpref : conflict (strongPow G m)
              (tupleEmb R m (fun s => w₁ s.castSucc)
                ⟨i.val / R.sz (w₁ (Fin.last m)), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm _ _))⟩)
              (tupleEmb R m (fun s => w₂ s.castSucc)
                ⟨j.val / R.sz (w₂ (Fin.last m)), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm _ _))⟩) := by
            rw [conflict_strongPow_iff]
            intro s
            have hs' := hconf s.castSucc
            simp only [Fin.val_castSucc, s.isLt, ↓reduceDIte] at hs'
            exact hs'
          exact ih _ _ ⟨⟨t.val, hlt⟩, ht⟩ _ _ hpref

/-- Arity-`m` homogeneous substitution lift `SepRealisation Sym sep G → SepRealisation Sym sep (strongPow G m)`. -/
def substLift {Sym V : Type} {sep : Sym → Sym → Bool} {G : FinGraph V}
    (R : SepRealisation Sym sep G) (m : Nat) (T : Sym → List (Fin m → Sym))
    (hin : ∀ c, (T c).Pairwise (fun w₁ w₂ => ∃ t : Fin m, sep (w₁ t) (w₂ t) = true))
    (hout : ∀ c₁ c₂, sep c₁ c₂ = true → ∀ w₁ ∈ T c₁, ∀ w₂ ∈ T c₂,
      ∃ t : Fin m, sep (w₁ t) (w₂ t) = true) :
    SepRealisation Sym sep (strongPow G m) where
  sz c := sumListSizes (T c) (tupleSz R.sz m)
  emb c := dispatchList (T c) (tupleSz R.sz m) (tupleEmb R m)
  indep c := dispatchList_indep (strongPow G m) (T c) (tupleSz R.sz m) (tupleEmb R m)
    (fun w _ => tupleEmb_indep R m w)
    (List.Pairwise.imp (fun {w₁ w₂} h => tupleEmb_sep R m w₁ w₂ h) (hin c))
  sep_ok c₁ c₂ hsep i j hc := by
    rcases dispatchList_mem (T c₁) (tupleSz R.sz m) (tupleEmb R m) i with ⟨w₁, hw₁, ri, hi_eq⟩
    rcases dispatchList_mem (T c₂) (tupleSz R.sz m) (tupleEmb R m) j with ⟨w₂, hw₂, rj, hj_eq⟩
    rw [hi_eq, hj_eq] at hc
    exact tupleEmb_sep R m w₁ w₂ (hout c₁ c₂ hsep w₁ hw₁ w₂ hw₂) ri rj hc

/-- Terminal separated `m`-code lift: yields `HasIndepSetOfSize (strongPow G m) (∑_{w ∈ C} ∏_t R.sz (w t))`! -/
theorem codeLift {Sym V : Type} {sep : Sym → Sym → Bool} {G : FinGraph V}
    (R : SepRealisation Sym sep G) (m : Nat) (C : List (Fin m → Sym))
    (hC : C.Pairwise (fun w₁ w₂ => ∃ t : Fin m, sep (w₁ t) (w₂ t) = true)) :
    HasIndepSetOfSize (strongPow G m) (sumListSizes C (tupleSz R.sz m)) :=
  ⟨dispatchList C (tupleSz R.sz m) (tupleEmb R m),
   dispatchList_indep (strongPow G m) C (tupleSz R.sz m) (tupleEmb R m)
     (fun w _ => tupleEmb_indep R m w)
     (List.Pairwise.imp (fun {w₁ w₂} h => tupleEmb_sep R m w₁ w₂ h) hC)⟩

/-! ### 4. Zero-Mathlib `RichPortSystem` → 7-Letter `SepRealisation` -/

/-- Zero-Mathlib `RichPortSystem` structure matching Buys–Polak–Zuiddam (`Lift.lean`).
Represents `I = B ⊔ O` (with `|B| = nB`, `|O| = d`), two independent transversals `V = ep false`
and `H = ep true`, and auxiliary independent set `X = N ⊔ A ⊔ D` (`|N| = nN`, `|A| = nA`, `|D| = nD`)
with separated footprints! -/
structure RichPortSystem {V : Type} (G : FinGraph V) where
  nB : Nat
  nN : Nat
  nA : Nat
  nD : Nat
  d : Nat
  embB : Fin nB → V
  embN : Fin nN → V
  embA : Fin nA → V
  embD : Fin nD → V
  embO : Fin d → V
  embH : Fin d → V
  embV : Fin d → V
  hB_indep : ∀ i j, i ≠ j → ¬ conflict G (embB i) (embB j)
  hN_indep : ∀ i j, i ≠ j → ¬ conflict G (embN i) (embN j)
  hA_indep : ∀ i j, i ≠ j → ¬ conflict G (embA i) (embA j)
  hD_indep : ∀ i j, i ≠ j → ¬ conflict G (embD i) (embD j)
  hO_indep : ∀ i j, i ≠ j → ¬ conflict G (embO i) (embO j)
  hH_indep : ∀ i j, i ≠ j → ¬ conflict G (embH i) (embH j)
  hV_indep : ∀ i j, i ≠ j → ¬ conflict G (embV i) (embV j)
  hBO : ∀ i j, ¬ conflict G (embB i) (embO j)
  hBH : ∀ i j, ¬ conflict G (embB i) (embH j)
  hBV : ∀ i j, ¬ conflict G (embB i) (embV j)
  hNA : ∀ i j, ¬ conflict G (embN i) (embA j)
  hND : ∀ i j, ¬ conflict G (embN i) (embD j)
  hNO : ∀ i j, ¬ conflict G (embN i) (embO j)
  hNH : ∀ i j, ¬ conflict G (embN i) (embH j)
  hNV : ∀ i j, ¬ conflict G (embN i) (embV j)
  hAD : ∀ i j, ¬ conflict G (embA i) (embD j)
  hAH : ∀ i j, ¬ conflict G (embA i) (embH j)
  hDV : ∀ i j, ¬ conflict G (embD i) (embV j)

def RichPortSystem.toSepRealisation {V : Type} {G : FinGraph V} (S : RichPortSystem G) :
    SepRealisation Letter Letter.sep G where
  sz
    | .B => S.nB | .N => S.nN | .A => S.nA | .D => S.nD
    | .O => S.d  | .H => S.d  | .V => S.d
  emb
    | .B => S.embB | .N => S.embN | .A => S.embA | .D => S.embD
    | .O => S.embO | .H => S.embH | .V => S.embV
  indep a := by
    cases a with
    | B => exact S.hB_indep | N => exact S.hN_indep | A => exact S.hA_indep
    | D => exact S.hD_indep | O => exact S.hO_indep | H => exact S.hH_indep
    | V => exact S.hV_indep
  sep_ok a b hsep i j hc := by
    cases a <;> cases b <;> simp only [Letter.sep] at hsep <;> try exact Bool.noConfusion hsep
    · exact S.hBO i j hc
    · exact S.hBH i j hc
    · exact S.hBV i j hc
    · exact S.hNA i j hc
    · exact S.hND i j hc
    · exact S.hNO i j hc
    · exact S.hNH i j hc
    · exact S.hNV i j hc
    · exact S.hNA j i (conflict_symm G hc)
    · exact S.hAD i j hc
    · exact S.hAH i j hc
    · exact S.hND j i (conflict_symm G hc)
    · exact S.hAD j i (conflict_symm G hc)
    · exact S.hDV i j hc
    · exact S.hBO j i (conflict_symm G hc)
    · exact S.hNO j i (conflict_symm G hc)
    · exact S.hBH j i (conflict_symm G hc)
    · exact S.hNH j i (conflict_symm G hc)
    · exact S.hAH j i (conflict_symm G hc)
    · exact S.hBV j i (conflict_symm G hc)
    · exact S.hNV j i (conflict_symm G hc)
    · exact S.hDV j i (conflict_symm G hc)

/-! ### 5. Pure-Kernel (ZERO `native_decide`!) Certified Substitution & Terminal Code Tables -/

def mk2 (a b : Letter) : Fin 2 → Letter
  | ⟨0, _⟩ => a | ⟨1, _⟩ => b

def mk3 (a b c : Letter) : Fin 3 → Letter
  | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c

def mk4 (a b c d : Letter) : Fin 4 → Letter
  | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c | ⟨3, _⟩ => d

def sep2B (u v : Fin 2 → Letter) : Bool :=
  Letter.sep (u ⟨0, by omega⟩) (v ⟨0, by omega⟩) ||
  Letter.sep (u ⟨1, by omega⟩) (v ⟨1, by omega⟩)

def sep3B (u v : Fin 3 → Letter) : Bool :=
  Letter.sep (u ⟨0, by omega⟩) (v ⟨0, by omega⟩) ||
  Letter.sep (u ⟨1, by omega⟩) (v ⟨1, by omega⟩) ||
  Letter.sep (u ⟨2, by omega⟩) (v ⟨2, by omega⟩)

def sep4B (u v : Fin 4 → Letter) : Bool :=
  Letter.sep (u ⟨0, by omega⟩) (v ⟨0, by omega⟩) ||
  Letter.sep (u ⟨1, by omega⟩) (v ⟨1, by omega⟩) ||
  Letter.sep (u ⟨2, by omega⟩) (v ⟨2, by omega⟩) ||
  Letter.sep (u ⟨3, by omega⟩) (v ⟨3, by omega⟩)

theorem sep2B_sound (u v : Fin 2 → Letter) (h : sep2B u v = true) :
    ∃ t : Fin 2, Letter.sep (u t) (v t) = true := by
  unfold sep2B at h
  rcases Bool.or_eq_true_iff.mp h with h0 | h1
  · exact ⟨⟨0, by omega⟩, h0⟩
  · exact ⟨⟨1, by omega⟩, h1⟩

theorem sep3B_sound (u v : Fin 3 → Letter) (h : sep3B u v = true) :
    ∃ t : Fin 3, Letter.sep (u t) (v t) = true := by
  unfold sep3B at h
  rcases Bool.or_eq_true_iff.mp h with h01 | h2
  · rcases Bool.or_eq_true_iff.mp h01 with h0 | h1
    · exact ⟨⟨0, by omega⟩, h0⟩
    · exact ⟨⟨1, by omega⟩, h1⟩
  · exact ⟨⟨2, by omega⟩, h2⟩

theorem sep4B_sound (u v : Fin 4 → Letter) (h : sep4B u v = true) :
    ∃ t : Fin 4, Letter.sep (u t) (v t) = true := by
  unfold sep4B at h
  rcases Bool.or_eq_true_iff.mp h with h012 | h3
  · rcases Bool.or_eq_true_iff.mp h012 with h01 | h2
    · rcases Bool.or_eq_true_iff.mp h01 with h0 | h1
      · exact ⟨⟨0, by omega⟩, h0⟩
      · exact ⟨⟨1, by omega⟩, h1⟩
    · exact ⟨⟨2, by omega⟩, h2⟩
  · exact ⟨⟨3, by omega⟩, h3⟩

/-- Fast boolean pairwise checker for pure-kernel `decide` verification! -/
def checkPairwiseB {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => true
  | x :: xs => xs.all (p x) && checkPairwiseB p xs

theorem checkPairwiseB_sound {α : Type} (p : α → α → Bool) (L : List α)
    (h : checkPairwiseB p L = true) : L.Pairwise (fun a b => p a b = true) := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    simp only [checkPairwiseB, Bool.and_eq_true_iff] at h
    rw [List.pairwise_cons]
    exact ⟨fun y hy => List.all_eq_true.mp h.1 y hy, ih h.2⟩

def checkCrossB {α : Type} (p : α → α → Bool) (L1 L2 : List α) : Bool :=
  L1.all (fun x => L2.all (fun y => p x y))

theorem checkCrossB_sound {α : Type} (p : α → α → Bool) (L1 L2 : List α)
    (h : checkCrossB p L1 L2 = true) : ∀ x ∈ L1, ∀ y ∈ L2, p x y = true := by
  intro x hx y hy
  exact List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy

/-- Arity-2 Gao squaring substitution `T2a` (20 words). -/
def tblT2a : Letter → List (Fin 2 → Letter)
  | .B => [mk2 .B .B, mk2 .H .D, mk2 .V .A, mk2 .D .V, mk2 .A .H]
  | .N => [mk2 .N .N, mk2 .A .A, mk2 .A .D, mk2 .D .A, mk2 .D .D]
  | .A => [mk2 .A .N, mk2 .N .D]
  | .D => [mk2 .D .N, mk2 .N .A]
  | .O => [mk2 .O .N, mk2 .N .O]
  | .H => [mk2 .H .N, mk2 .N .V]
  | .V => [mk2 .V .N, mk2 .N .H]

/-- Arity-3 substitution `T3c` (48 words). -/
def tblT3c : Letter → List (Fin 3 → Letter)
  | .B => [mk3 .A .B .V, mk3 .A .H .H, mk3 .A .V .A, mk3 .B .B .B, mk3 .D .A .H, mk3 .D .H .A, mk3 .D .N .H,
           mk3 .H .A .A, mk3 .H .A .N, mk3 .H .H .H, mk3 .N .H .D, mk3 .N .V .A, mk3 .V .A .D, mk3 .V .D .B]
  | .N => [mk3 .A .A .D, mk3 .A .D .A, mk3 .B .H .D, mk3 .D .A .B, mk3 .D .B .H, mk3 .H .H .A, mk3 .H .V .H,
           mk3 .N .N .N, mk3 .V .A .A, mk3 .V .D .H]
  | .A => [mk3 .A .B .N, mk3 .A .N .D, mk3 .B .N .A, mk3 .B .V .V, mk3 .H .D .N, mk3 .N .A .B, mk3 .N .D .A,
           mk3 .V .N .V, mk3 .V .V .N]
  | .D => [mk3 .D .N .N, mk3 .N .D .N, mk3 .N .N .D]
  | .O => []
  | .H => [mk3 .B .H .N, mk3 .H .N .B, mk3 .N .B .H]
  | .V => [mk3 .A .V .N, mk3 .D .H .N, mk3 .H .N .A, mk3 .N .A .H, mk3 .N .D .V, mk3 .N .N .V, mk3 .N .V .N,
           mk3 .V .N .D, mk3 .V .N .N]

/-- Arity-3 substitution `T3e` (53 words). -/
def tblT3e : Letter → List (Fin 3 → Letter)
  | .B => [mk3 .A .H .N, mk3 .B .A .H, mk3 .B .B .B, mk3 .B .D .V, mk3 .B .H .D, mk3 .B .V .A, mk3 .D .V .N,
           mk3 .H .D .N, mk3 .H .N .A, mk3 .V .A .N, mk3 .V .N .D]
  | .N => [mk3 .A .A .N, mk3 .A .H .N, mk3 .D .A .N, mk3 .D .D .N, mk3 .H .N .A, mk3 .N .A .A, mk3 .N .A .D,
           mk3 .N .D .A, mk3 .N .D .D, mk3 .N .N .N]
  | .A => [mk3 .A .A .A, mk3 .A .A .D, mk3 .A .D .A, mk3 .A .D .D, mk3 .A .N .N, mk3 .B .N .A, mk3 .H .N .D,
           mk3 .N .A .N]
  | .D => [mk3 .A .N .D, mk3 .D .A .A, mk3 .D .A .D, mk3 .D .D .A, mk3 .D .D .D, mk3 .D .N .N, mk3 .N .D .N,
           mk3 .N .N .D]
  | .O => []
  | .H => [mk3 .B .N .H, mk3 .H .A .A, mk3 .H .A .D, mk3 .H .D .D, mk3 .H .H .A, mk3 .H .N .N, mk3 .N .H .N]
  | .V => [mk3 .A .N .V, mk3 .D .N .H, mk3 .N .N .V, mk3 .N .V .N, mk3 .V .A .A, mk3 .V .A .D, mk3 .V .D .A,
           mk3 .V .D .D, mk3 .V .N .N]

/-- Arity-4 terminal code `C4a` (49 words). -/
def codeC4a : List (Fin 4 → Letter) :=
  [mk4 .B .B .B .B, mk4 .B .N .V .B, mk4 .B .A .H .B, mk4 .B .D .V .B, mk4 .B .H .N .B, mk4 .B .H .D .B,
   mk4 .B .V .A .B, mk4 .N .B .B .V, mk4 .N .N .V .H, mk4 .N .A .V .H, mk4 .N .D .H .H, mk4 .N .H .N .H,
   mk4 .N .H .A .H, mk4 .N .V .D .V, mk4 .A .B .B .V, mk4 .A .N .H .H, mk4 .A .A .V .H, mk4 .A .D .H .H,
   mk4 .A .H .A .H, mk4 .A .V .N .H, mk4 .A .V .D .H, mk4 .D .B .B .H, mk4 .D .N .V .V, mk4 .D .A .V .V,
   mk4 .D .D .H .V, mk4 .D .H .N .V, mk4 .D .H .A .V, mk4 .D .V .D .V, mk4 .H .B .B .A, mk4 .H .N .V .D,
   mk4 .H .A .H .D, mk4 .H .A .V .N, mk4 .H .D .H .N, mk4 .H .D .V .D, mk4 .H .H .N .N, mk4 .H .H .N .D,
   mk4 .H .H .A .N, mk4 .H .H .D .D, mk4 .H .V .A .D, mk4 .H .V .D .N, mk4 .V .B .B .N, mk4 .V .B .B .D,
   mk4 .V .N .V .N, mk4 .V .N .V .A, mk4 .V .A .H .A, mk4 .V .D .V .A, mk4 .V .H .D .A, mk4 .V .V .N .A,
   mk4 .V .V .A .A]

/-- Arity-4 terminal code `C4b` (57 words). -/
def codeC4b : List (Fin 4 → Letter) :=
  [mk4 .A .A .A .V, mk4 .A .A .N .V, mk4 .A .B .H .A, mk4 .A .H .A .A, mk4 .A .H .A .N, mk4 .A .H .N .A,
   mk4 .A .H .N .N, mk4 .A .N .A .V, mk4 .A .N .D .H, mk4 .A .N .H .N, mk4 .A .N .N .H, mk4 .A .V .D .B,
   mk4 .B .A .D .H, mk4 .B .A .V .N, mk4 .B .B .B .B, mk4 .B .B .V .D, mk4 .B .D .B .H, mk4 .B .D .H .N,
   mk4 .B .H .H .H, mk4 .B .V .A .D, mk4 .B .V .N .D, mk4 .D .A .V .A, mk4 .D .H .H .A, mk4 .D .N .B .V,
   mk4 .D .N .V .A, mk4 .D .N .V .N, mk4 .D .V .B .A, mk4 .D .V .B .N, mk4 .H .A .B .H, mk4 .H .B .D .B,
   mk4 .H .B .V .H, mk4 .H .D .A .B, mk4 .H .D .N .B, mk4 .H .N .N .D, mk4 .H .V .H .D, mk4 .H .V .H .N,
   mk4 .N .A .A .V, mk4 .N .A .N .V, mk4 .N .B .H .A, mk4 .N .H .A .N, mk4 .N .H .B .A, mk4 .N .N .A .V,
   mk4 .N .N .D .H, mk4 .N .N .N .V, mk4 .N .N .V .N, mk4 .N .V .D .N, mk4 .N .V .H .A, mk4 .N .V .N .N,
   mk4 .V .A .A .B, mk4 .V .A .N .B, mk4 .V .D .D .H, mk4 .V .H .A .H, mk4 .V .H .N .H, mk4 .V .N .A .B,
   mk4 .V .N .N .A, mk4 .V .N .N .N, mk4 .V .V .H .V]

/-! Pure-kernel (`decide`, ZERO `native_decide`!) admissibility theorems! -/

theorem tblT2a_in_ok (c : Letter) : checkPairwiseB sep2B (tblT2a c) = true := by cases c <;> decide
theorem tblT2a_out_ok (c₁ c₂ : Letter) :
    Letter.sep c₁ c₂ = true → checkCrossB sep2B (tblT2a c₁) (tblT2a c₂) = true := by
  cases c₁ <;> cases c₂ <;> decide

theorem tblT3c_in_ok (c : Letter) : checkPairwiseB sep3B (tblT3c c) = true := by cases c <;> decide
theorem tblT3c_out_ok (c₁ c₂ : Letter) :
    Letter.sep c₁ c₂ = true → checkCrossB sep3B (tblT3c c₁) (tblT3c c₂) = true := by
  cases c₁ <;> cases c₂ <;> decide

theorem tblT3e_in_ok (c : Letter) : checkPairwiseB sep3B (tblT3e c) = true := by cases c <;> decide
theorem tblT3e_out_ok (c₁ c₂ : Letter) :
    Letter.sep c₁ c₂ = true → checkCrossB sep3B (tblT3e c₁) (tblT3e c₂) = true := by
  cases c₁ <;> cases c₂ <;> decide

theorem codeC4a_ok : checkPairwiseB sep4B codeC4a = true := by decide
theorem codeC4b_ok : checkPairwiseB sep4B codeC4b = true := by decide

/-- Lifted `SepRealisation` combinators for `T2a`, `T3c`, `T3e` (pure kernel!). -/
def liftT2a {V : Type} {G : FinGraph V} (R : SepRealisation Letter Letter.sep G) :
    SepRealisation Letter Letter.sep (strongPow G 2) :=
  substLift R 2 tblT2a
    (fun c => List.Pairwise.imp (fun {u v} h => sep2B_sound u v h) (checkPairwiseB_sound sep2B _ (tblT2a_in_ok c)))
    (fun c₁ c₂ hs u hu v hv => sep2B_sound u v (checkCrossB_sound sep2B _ _ (tblT2a_out_ok c₁ c₂ hs) u hu v hv))

def liftT3c {V : Type} {G : FinGraph V} (R : SepRealisation Letter Letter.sep G) :
    SepRealisation Letter Letter.sep (strongPow G 3) :=
  substLift R 3 tblT3c
    (fun c => List.Pairwise.imp (fun {u v} h => sep3B_sound u v h) (checkPairwiseB_sound sep3B _ (tblT3c_in_ok c)))
    (fun c₁ c₂ hs u hu v hv => sep3B_sound u v (checkCrossB_sound sep3B _ _ (tblT3c_out_ok c₁ c₂ hs) u hu v hv))

def liftT3e {V : Type} {G : FinGraph V} (R : SepRealisation Letter Letter.sep G) :
    SepRealisation Letter Letter.sep (strongPow G 3) :=
  substLift R 3 tblT3e
    (fun c => List.Pairwise.imp (fun {u v} h => sep3B_sound u v h) (checkPairwiseB_sound sep3B _ (tblT3e_in_ok c)))
    (fun c₁ c₂ hs u hu v hv => sep3B_sound u v (checkCrossB_sound sep3B _ _ (tblT3e_out_ok c₁ c₂ hs) u hu v hv))

theorem liftC4a {V : Type} {G : FinGraph V} (R : SepRealisation Letter Letter.sep G) :
    HasIndepSetOfSize (strongPow G 4) (sumListSizes codeC4a (tupleSz R.sz 4)) :=
  codeLift R 4 codeC4a
    (List.Pairwise.imp (fun {u v} h => sep4B_sound u v h) (checkPairwiseB_sound sep4B _ codeC4a_ok))

theorem liftC4b {V : Type} {G : FinGraph V} (R : SepRealisation Letter Letter.sep G) :
    HasIndepSetOfSize (strongPow G 4) (sumListSizes codeC4b (tupleSz R.sz 4)) :=
  codeLift R 4 codeC4b
    (List.Pairwise.imp (fun {u v} h => sep4B_sound u v h) (checkPairwiseB_sound sep4B _ codeC4b_ok))

/-- Closed-form weight update functions matching `liftT2a`, `liftT3c`, `liftT3e`, `liftC4a`, `liftC4b`! -/
def evalT2a (w : Letter → Nat) (c : Letter) : Nat := sumListSizes (tblT2a c) (tupleSz w 2)
def evalT3c (w : Letter → Nat) (c : Letter) : Nat := sumListSizes (tblT3c c) (tupleSz w 3)
def evalT3e (w : Letter → Nat) (c : Letter) : Nat := sumListSizes (tblT3e c) (tupleSz w 3)
def evalC4a (w : Letter → Nat) : Nat := sumListSizes codeC4a (tupleSz w 4)
def evalC4b (w : Letter → Nat) : Nat := sumListSizes codeC4b (tupleSz w 4)

/-- **Theorem T3c (Two-Sided Heterogeneous Composition & Pure-Kernel Table Admissibility).** -/
theorem t3c_heterogeneous_composition_and_tables :
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
         ∀ c, R'.sz c = sumListSizes (T c) (fun p => R₁.sz p.1 * R₂.sz p.2)) := by
  refine ⟨fun c => ⟨tblT2a_in_ok c, tblT3c_in_ok c, tblT3e_in_ok c⟩,
          fun c₁ c₂ hs => ⟨tblT2a_out_ok c₁ c₂ hs, tblT3c_out_ok c₁ c₂ hs, tblT3e_out_ok c₁ c₂ hs⟩,
          ⟨codeC4a_ok, codeC4b_ok⟩, ?_⟩
  intro Sym1 Sym2 SymP V₁ V₂ sep₁ sep₂ sep' G₁ G₂ R₁ R₂ T hin hout
  exact ⟨heteroCompose R₁ R₂ T hin hout, fun _ => rfl⟩

end
end ZeroErrorFrontier.SeparationCalculus
