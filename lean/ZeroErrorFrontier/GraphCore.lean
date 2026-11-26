module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

/-!
# Zero-Mathlib Graph Core, Strong Products, Odd Cycles, and Minimal Algebra

Foundation module for `zero-error-torus-frontier` (`v1.0.0`).
Defines finite graphs, strong products `G ⊠ H`, strong powers `G^{\boxtimes d}`,
odd cycles `C_n`, exact integer independence bounds `HasIndepSetOfSize` and `AlphaLe`,
locally-injective graph homomorphisms, and a minimal zero-Mathlib `SimpleField` class
(with instance `ZMod2`) for Haemers's rank bound.

Zero Mathlib imports, zero `sorry`, zero `native_decide`.
-/

namespace ZeroErrorFrontier.GraphCore

@[expose] public section

/-! ### 1. Finite Graphs, Conflict, Strong Products, and Strong Powers -/

/-- A simple undirected irreflexive graph on vertex type `V`. -/
structure FinGraph (V : Type) where
  adj : V → V → Prop
  symm : ∀ {u v}, adj u v → adj v u
  irrefl : ∀ {u}, ¬ adj u u

/-- Closed-neighborhood conflict: equal or adjacent. -/
def conflict {V : Type} (G : FinGraph V) (u v : V) : Prop :=
  u = v ∨ G.adj u v

theorem conflict_refl {V : Type} (G : FinGraph V) (u : V) : conflict G u u :=
  Or.inl rfl

theorem conflict_symm {V : Type} (G : FinGraph V) {u v : V}
    (h : conflict G u v) : conflict G v u :=
  match h with
  | Or.inl heq => Or.inl heq.symm
  | Or.inr hadj => Or.inr (G.symm hadj)

/-- Strong graph product `G ⊠ H`. -/
def strongProd {V W : Type} (G : FinGraph V) (H : FinGraph W) : FinGraph (V × W) where
  adj x y := x ≠ y ∧ conflict G x.1 y.1 ∧ conflict H x.2 y.2
  symm := fun ⟨hne, h1, h2⟩ => ⟨hne.symm, conflict_symm G h1, conflict_symm H h2⟩
  irrefl := fun ⟨hne, _, _⟩ => hne rfl

theorem conflict_strongProd_iff {V W : Type} (G : FinGraph V) (H : FinGraph W)
    (x y : V × W) :
    conflict (strongProd G H) x y ↔ conflict G x.1 y.1 ∧ conflict H x.2 y.2 := by
  constructor
  · intro h
    cases h with
    | inl heq => subst heq; exact ⟨conflict_refl G _, conflict_refl H _⟩
    | inr hadj => exact ⟨hadj.2.1, hadj.2.2⟩
  · intro ⟨h1, h2⟩
    by_cases heq : x = y
    · exact Or.inl heq
    · exact Or.inr ⟨heq, h1, h2⟩

/-- `d`-th strong graph power `G^{\boxtimes d}` on `Fin d → V`. -/
def strongPow {V : Type} (G : FinGraph V) (d : Nat) : FinGraph (Fin d → V) where
  adj x y := x ≠ y ∧ ∀ i : Fin d, conflict G (x i) (y i)
  symm := fun ⟨hne, hall⟩ => ⟨hne.symm, fun i => conflict_symm G (hall i)⟩
  irrefl := fun ⟨hne, _⟩ => hne rfl

theorem conflict_strongPow_iff {V : Type} (G : FinGraph V) (d : Nat)
    (x y : Fin d → V) :
    conflict (strongPow G d) x y ↔ ∀ i : Fin d, conflict G (x i) (y i) := by
  constructor
  · intro h i
    cases h with
    | inl heq => subst heq; exact conflict_refl G _
    | inr hadj => exact hadj.2 i
  · intro hall
    by_cases heq : x = y
    · exact Or.inl heq
    · exact Or.inr ⟨heq, hall⟩

/-! ### 2. Exact Independence Lower and Upper Bounds -/

/-- `G` has an independent set of cardinality `N` (witnessed by an embedding `Fin N → V`
whose distinct images never conflict). -/
def HasIndepSetOfSize {V : Type} (G : FinGraph V) (N : Nat) : Prop :=
  ∃ f : Fin N → V, ∀ i j : Fin N, i ≠ j → ¬ conflict G (f i) (f j)

/-- Universal upper bound `α(G) ≤ B`: every independent set in `G` has size at most `B`. -/
def AlphaLe {V : Type} (G : FinGraph V) (B : Nat) : Prop :=
  ∀ N : Nat, HasIndepSetOfSize G N → N ≤ B

theorem hasIndepSet_mono {V : Type} {G : FinGraph V} {M N : Nat}
    (hMN : M ≤ N) (hN : HasIndepSetOfSize G N) : HasIndepSetOfSize G M := by
  rcases hN with ⟨f, hf⟩
  refine ⟨fun i => f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hMN⟩, ?_⟩
  intro i j hij
  apply hf
  intro heq
  apply hij
  exact Fin.ext (congrArg (fun x : Fin N => x.val) heq)

theorem hasIndepSet_strongProd {V W : Type} {G : FinGraph V} {H : FinGraph W} {N M : Nat}
    (hG : HasIndepSetOfSize G N) (hH : HasIndepSetOfSize H M) :
    HasIndepSetOfSize (strongProd G H) (N * M) := by
  by_cases hM : M = 0
  · subst hM
    exact ⟨fun i => False.elim (Nat.not_lt_zero i.val (by simpa using i.isLt)),
           fun i => False.elim (Nat.not_lt_zero i.val (by simpa using i.isLt))⟩
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    rcases hG with ⟨f, hf⟩
    rcases hH with ⟨g, hg⟩
    let mkQ : Fin (N * M) → Fin N := fun k =>
      ⟨k.val / M, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm N M))⟩
    let mkR : Fin (N * M) → Fin M := fun k => ⟨k.val % M, Nat.mod_lt k.val hMpos⟩
    refine ⟨fun k => (f (mkQ k), g (mkR k)), ?_⟩
    intro i j hij hconf
    rw [conflict_strongProd_iff] at hconf
    have hq : mkQ i = mkQ j := Classical.byContradiction fun hne => hf (mkQ i) (mkQ j) hne hconf.1
    have hr : mkR i = mkR j := Classical.byContradiction fun hne => hg (mkR i) (mkR j) hne hconf.2
    have hqv : i.val / M = j.val / M := congrArg Fin.val hq
    have hrv : i.val % M = j.val % M := congrArg Fin.val hr
    apply hij
    apply Fin.ext
    have hi := Nat.div_add_mod i.val M
    have hj := Nat.div_add_mod j.val M
    rw [hqv, hrv] at hi
    omega

theorem hasIndepSet_strongPow_mul {V : Type} {G : FinGraph V} {a b N : Nat}
    (h : HasIndepSetOfSize (strongPow (strongPow G a) b) N) :
    HasIndepSetOfSize (strongPow G (a * b)) N := by
  by_cases ha : a = 0
  · subst ha
    rcases h with ⟨f, hf⟩
    exact ⟨fun _ idx => False.elim (Nat.not_lt_zero idx.val (by simpa using idx.isLt)),
           fun i j hij _ => hf i j hij ((conflict_strongPow_iff _ _ _ _).mpr fun t =>
             (conflict_strongPow_iff _ _ _ _).mpr fun s => False.elim (Nat.not_lt_zero s.val s.isLt))⟩
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha
    rcases h with ⟨f, hf⟩
    let mkT : Fin (a * b) → Fin b := fun idx => ⟨idx.val / a, Nat.div_lt_of_lt_mul idx.isLt⟩
    let mkS : Fin (a * b) → Fin a := fun idx => ⟨idx.val % a, Nat.mod_lt idx.val hapos⟩
    refine ⟨fun k idx => f k (mkT idx) (mkS idx), ?_⟩
    intro i j hij hconf
    rw [conflict_strongPow_iff] at hconf
    apply hf i j hij
    rw [conflict_strongPow_iff]
    intro t
    rw [conflict_strongPow_iff]
    intro s
    have hlt : t.val * a + s.val < a * b := by
      have ht : t.val + 1 ≤ b := t.isLt
      have h1 : (t.val + 1) * a ≤ b * a := Nat.mul_le_mul_right a ht
      have h2 : t.val * a + s.val < t.val * a + a := Nat.add_lt_add_left s.isLt (t.val * a)
      have h3 : t.val * a + a = (t.val + 1) * a := by rw [Nat.add_mul, Nat.one_mul]
      rw [Nat.mul_comm a b]
      omega
    have hidx := hconf ⟨t.val * a + s.val, hlt⟩
    have hdiv : (t.val * a + s.val) / a = t.val := by
      rw [Nat.mul_comm t.val a, Nat.mul_add_div hapos, Nat.div_eq_of_lt s.isLt, Nat.add_zero]
    have hmod : (t.val * a + s.val) % a = s.val := by
      rw [Nat.mul_comm t.val a, Nat.mul_add_mod, Nat.mod_eq_of_lt s.isLt]
    have ht' : mkT ⟨t.val * a + s.val, hlt⟩ = t := Fin.ext hdiv
    have hs' : mkS ⟨t.val * a + s.val, hlt⟩ = s := Fin.ext hmod
    dsimp only at hidx
    rw [ht', hs'] at hidx
    exact hidx

theorem hasIndepSet_of_strongPow_hom {V W : Type} {G : FinGraph V} {H : FinGraph W} {N : Nat}
    (φ : V → W)
    (hφ : ∀ x y, conflict H (φ x) (φ y) → conflict G x y)
    (h : HasIndepSetOfSize G N) :
    HasIndepSetOfSize H N := by
  rcases h with ⟨f, hf⟩
  exact ⟨fun i => φ (f i), fun i j hij hc => hf i j hij (hφ _ _ hc)⟩

theorem hasIndepSet_of_list {V : Type} (G : FinGraph V) (L : List V)
    (hL : ∀ i j : Fin L.length, i ≠ j → ¬ conflict G (L.get i) (L.get j)) :
    HasIndepSetOfSize G L.length :=
  ⟨fun i => L.get i, hL⟩

/-! ### 3. Cycle Graphs `C_n` and Circular Distance -/

/-- Circular distance on `ℤ_n` for `a, b < n`. -/
def cycDist (n a b : Nat) : Nat :=
  min ((a + n - b) % n) ((b + n - a) % n)

theorem cycDist_symm (n a b : Nat) : cycDist n a b = cycDist n b a := by
  unfold cycDist
  exact Nat.min_comm _ _

theorem cycDist_self (n a : Nat) (hn : 0 < n) : cycDist n a a = 0 := by
  unfold cycDist
  have h : (a + n - a) % n = 0 := by
    have : a + n - a = n := by omega
    rw [this, Nat.mod_self]
  rw [h]; simp

theorem cycDist_eq_zero_iff (n a b : Nat) (ha : a < n) (hb : b < n) :
    cycDist n a b = 0 ↔ a = b := by
  constructor
  · intro h
    unfold cycDist at h
    by_cases hle : (a + n - b) % n ≤ (b + n - a) % n
    · rw [Nat.min_eq_left hle] at h
      by_cases hab : a ≥ b
      · have h1 : a + n - b = (a - b) + n := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
        omega
      · have h1 : (a + n - b) % n = a + n - b := Nat.mod_eq_of_lt (by omega)
        rw [h1] at h
        omega
    · rw [Nat.min_eq_right (Nat.le_of_not_le hle)] at h
      by_cases hba : b ≥ a
      · have h1 : b + n - a = (b - a) + n := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
        omega
      · have h1 : (b + n - a) % n = b + n - a := Nat.mod_eq_of_lt (by omega)
        rw [h1] at h
        omega
  · intro heq; subst heq; exact cycDist_self n a (by omega)

/-- The `n`-cycle graph `C_n` on `Fin n` (`n ≥ 3`). -/
def cycleGraph (n : Nat) : FinGraph (Fin n) where
  adj a b := a ≠ b ∧ cycDist n a.val b.val ≤ 1
  symm := fun ⟨hne, hd⟩ => ⟨hne.symm, by rw [cycDist_symm]; exact hd⟩
  irrefl := fun ⟨hne, _⟩ => hne rfl

theorem conflict_cycleGraph_iff (n : Nat) (a b : Fin n) :
    conflict (cycleGraph n) a b ↔ cycDist n a.val b.val ≤ 1 := by
  constructor
  · intro h
    cases h with
    | inl heq =>
      subst heq
      rw [cycDist_self n a.val (Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt)]
      omega
    | inr hadj => exact hadj.2
  · intro hd
    by_cases heq : a = b
    · exact Or.inl heq
    · exact Or.inr ⟨heq, hd⟩

/-- Signed lift characterization of `cycDist n a b ≤ k` when `a, b < n`. -/
theorem cycDist_le_iff (n a b k : Nat) (ha : a < n) (hb : b < n) :
    cycDist n a b ≤ k ↔
      (a ≥ b ∧ a - b ≤ k) ∨
      (b ≥ a ∧ b - a ≤ k) ∨
      (a + n - b ≤ k) ∨
      (b + n - a ≤ k) := by
  unfold cycDist
  have h1 : (a + n - b) % n = if a ≥ b then a - b else a + n - b := by
    split
    · rename_i hge
      have : a + n - b = (a - b) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rename_i hlt
      exact Nat.mod_eq_of_lt (by omega)
  have h2 : (b + n - a) % n = if b ≥ a then b - a else b + n - a := by
    split
    · rename_i hge
      have : b + n - a = (b - a) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rename_i hlt
      exact Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  constructor
  · intro h
    by_cases hab : a ≥ b <;> by_cases hba : b ≥ a <;> simp only [hab, hba, ↓reduceIte] at h <;> omega
  · intro h
    by_cases hab : a ≥ b <;> by_cases hba : b ≥ a <;> simp only [hab, hba, ↓reduceIte] <;> omega

/-! ### 4. Finite Sums and Minimal Zero-Mathlib Field Typeclass -/

def sumNat : (n : Nat) → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumNat n f + f n

def sumInt : (n : Nat) → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumInt n f + f n

theorem sumNat_congr {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : sumNat n f = sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumNat_le {n : Nat} {f g : Nat → Nat}
    (h : ∀ i, i < n → f i ≤ g i) : sumNat n f ≤ sumNat n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    simp only [sumNat]
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h k (by omega))

theorem sumNat_const (n c : Nat) : sumNat n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumNat]
  | succ k ih =>
    simp only [sumNat, ih, Nat.succ_mul]

theorem sumNat_add (n : Nat) (f g : Nat → Nat) :
    sumNat n (fun i => f i + g i) = sumNat n f + sumNat n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumNat, ih]
    omega

theorem sumNat_swap (m n : Nat) (f : Nat → Nat → Nat) :
    sumNat m (fun i => sumNat n (fun j => f i j)) =
    sumNat n (fun j => sumNat m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumNat]
    have h0 : sumNat n (fun _ => 0) = 0 := by rw [sumNat_const, Nat.mul_zero]
    exact h0.symm
  | succ k ih =>
    simp only [sumNat]
    rw [ih, sumNat_add]

theorem sumInt_congr {n : Nat} {f g : Nat → Int}
    (h : ∀ i, i < n → f i = g i) : sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumInt_nonneg {n : Nat} {f : Nat → Int}
    (h : ∀ i, i < n → 0 ≤ f i) : 0 ≤ sumInt n f := by
  induction n with
  | zero => exact Int.le_refl 0
  | succ k ih =>
    simp only [sumInt]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h k (by omega)
    omega

theorem sumInt_add (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i + g i) = sumInt n f + sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt, ih]
    omega

theorem sumInt_sub (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i - g i) = sumInt n f - sumInt n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumInt, ih]
    omega

theorem sumInt_mul_left (n : Nat) (c : Int) (f : Nat → Int) :
    sumInt n (fun i => c * f i) = c * sumInt n f := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt, ih, Int.mul_add]

theorem sumInt_mul_right (n : Nat) (f : Nat → Int) (c : Int) :
    sumInt n (fun i => f i * c) = sumInt n f * c := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih =>
    simp only [sumInt, ih, Int.add_mul]

theorem sumInt_swap (m n : Nat) (f : Nat → Nat → Int) :
    sumInt m (fun i => sumInt n (fun j => f i j)) =
    sumInt n (fun j => sumInt m (fun i => f i j)) := by
  induction m with
  | zero =>
    simp only [sumInt]
    induction n with
    | zero => rfl
    | succ l ihl => simp only [sumInt, ← ihl]; omega
  | succ k ih =>
    simp only [sumInt]
    rw [ih, sumInt_add]

theorem sumInt_zero (n : Nat) : sumInt n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumInt, ih]; omega

theorem sumInt_single (n idx : Nat) (v : Int) (hidx : idx < n) :
    sumInt n (fun i => if i = idx then v else 0) = v := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [sumInt]
    by_cases hk : k = idx
    · subst hk
      have h0 : sumInt k (fun i => if i = k then v else 0) = 0 := by
        rw [sumInt_congr (g := fun _ => 0) (fun i hi => by
          have : i ≠ k := by omega
          simp [this])]
        exact sumInt_zero k
      simp [h0]
    · have hlt : idx < k := by omega
      simp [hk, ih hlt]

/-- Minimal zero-Mathlib field typeclass for general algebraic bounds (Haemers rank theorem). -/
class SimpleField (F : Type) where
  zero : F
  one : F
  add : F → F → F
  neg : F → F
  mul : F → F → F
  inv : F → F
  add_assoc : ∀ a b c : F, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : F, add a b = add b a
  zero_add : ∀ a : F, add zero a = a
  add_neg : ∀ a : F, add a (neg a) = zero
  mul_assoc : ∀ a b c : F, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : F, mul a b = mul b a
  one_mul : ∀ a : F, mul one a = a
  left_distrib : ∀ a b c : F, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one
  mul_inv_cancel : ∀ a : F, a ≠ zero → mul a (inv a) = one

def fSub {F : Type} [SimpleField F] (a b : F) : F :=
  SimpleField.add a (SimpleField.neg b)

theorem f_add_zero {F : Type} [SimpleField F] (a : F) :
    SimpleField.add a SimpleField.zero = a := by
  rw [SimpleField.add_comm, SimpleField.zero_add]

theorem f_mul_one {F : Type} [SimpleField F] (a : F) :
    SimpleField.mul a SimpleField.one = a := by
  rw [SimpleField.mul_comm, SimpleField.one_mul]

theorem f_right_distrib {F : Type} [SimpleField F] (a b c : F) :
    SimpleField.mul (SimpleField.add a b) c =
    SimpleField.add (SimpleField.mul a c) (SimpleField.mul b c) := by
  rw [SimpleField.mul_comm, SimpleField.left_distrib,
      SimpleField.mul_comm c a, SimpleField.mul_comm c b]

theorem f_neg_add {F : Type} [SimpleField F] (a : F) :
    SimpleField.add (SimpleField.neg a) a = SimpleField.zero := by
  rw [SimpleField.add_comm, SimpleField.add_neg]

theorem f_add_left_cancel {F : Type} [SimpleField F] {a b c : F}
    (h : SimpleField.add a b = SimpleField.add a c) : b = c := by
  have h1 := congrArg (SimpleField.add (SimpleField.neg a)) h
  rw [← SimpleField.add_assoc, ← SimpleField.add_assoc, f_neg_add,
      SimpleField.zero_add, SimpleField.zero_add] at h1
  exact h1

theorem f_mul_zero {F : Type} [SimpleField F] (a : F) :
    SimpleField.mul a SimpleField.zero = SimpleField.zero := by
  have h : SimpleField.add (SimpleField.mul a SimpleField.zero)
      (SimpleField.mul a SimpleField.zero) =
      SimpleField.add (SimpleField.mul a SimpleField.zero) SimpleField.zero := by
    rw [← SimpleField.left_distrib, SimpleField.zero_add, f_add_zero]
  exact f_add_left_cancel h

theorem f_zero_mul {F : Type} [SimpleField F] (a : F) :
    SimpleField.mul SimpleField.zero a = SimpleField.zero := by
  rw [SimpleField.mul_comm, f_mul_zero]

theorem f_mul_neg {F : Type} [SimpleField F] (a b : F) :
    SimpleField.mul a (SimpleField.neg b) = SimpleField.neg (SimpleField.mul a b) := by
  apply f_add_left_cancel (a := SimpleField.mul a b)
  rw [← SimpleField.left_distrib, SimpleField.add_neg, f_mul_zero, SimpleField.add_neg]

theorem f_neg_mul {F : Type} [SimpleField F] (a b : F) :
    SimpleField.mul (SimpleField.neg a) b = SimpleField.neg (SimpleField.mul a b) := by
  rw [SimpleField.mul_comm, f_mul_neg, SimpleField.mul_comm]

theorem f_mul_ne_zero {F : Type} [SimpleField F] {a b : F}
    (ha : a ≠ SimpleField.zero) (hb : b ≠ SimpleField.zero) :
    SimpleField.mul a b ≠ SimpleField.zero := by
  intro hab
  have h1 := congrArg (SimpleField.mul (SimpleField.inv a)) hab
  rw [← SimpleField.mul_assoc, SimpleField.mul_comm (SimpleField.inv a) a,
      SimpleField.mul_inv_cancel a ha, SimpleField.one_mul, f_mul_zero] at h1
  exact hb h1

theorem f_inv_mul_cancel {F : Type} [SimpleField F] (a : F) (ha : a ≠ SimpleField.zero) :
    SimpleField.mul (SimpleField.inv a) a = SimpleField.one := by
  rw [SimpleField.mul_comm, SimpleField.mul_inv_cancel a ha]

def sumF {F : Type} [SimpleField F] : (n : Nat) → (Nat → F) → F
  | 0, _ => SimpleField.zero
  | n + 1, f => SimpleField.add (sumF n f) (f n)

theorem sumF_congr {F : Type} [SimpleField F] {n : Nat} {f g : Nat → F}
    (h : ∀ i, i < n → f i = g i) : sumF n f = sumF n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumF]
    rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumF_zero {F : Type} [SimpleField F] (n : Nat) :
    sumF n (fun _ => (SimpleField.zero : F)) = SimpleField.zero := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumF, ih, SimpleField.zero_add]

theorem sumF_add {F : Type} [SimpleField F] (n : Nat) (f g : Nat → F) :
    sumF n (fun i => SimpleField.add (f i) (g i)) =
    SimpleField.add (sumF n f) (sumF n g) := by
  induction n with
  | zero => simp [sumF, SimpleField.zero_add]
  | succ k ih =>
    simp only [sumF, ih]
    rw [SimpleField.add_assoc, ← SimpleField.add_assoc (sumF k g) (f k) (g k),
        SimpleField.add_comm (sumF k g) (f k), SimpleField.add_assoc (f k) (sumF k g) (g k),
        ← SimpleField.add_assoc]

theorem sumF_mul_left {F : Type} [SimpleField F] (n : Nat) (c : F) (f : Nat → F) :
    sumF n (fun i => SimpleField.mul c (f i)) = SimpleField.mul c (sumF n f) := by
  induction n with
  | zero => simp [sumF, f_mul_zero]
  | succ k ih => simp only [sumF, ih, SimpleField.left_distrib]

theorem sumF_mul_right {F : Type} [SimpleField F] (n : Nat) (f : Nat → F) (c : F) :
    sumF n (fun i => SimpleField.mul (f i) c) = SimpleField.mul (sumF n f) c := by
  induction n with
  | zero => simp [sumF, f_zero_mul]
  | succ k ih => simp only [sumF, ih, f_right_distrib]

theorem sumF_swap {F : Type} [SimpleField F] (m n : Nat) (f : Nat → Nat → F) :
    sumF m (fun i => sumF n (fun j => f i j)) =
    sumF n (fun j => sumF m (fun i => f i j)) := by
  induction m with
  | zero => simp only [sumF]; exact (sumF_zero n).symm
  | succ k ih => simp only [sumF, ih, sumF_add]

theorem sumF_single {F : Type} [SimpleField F] (n idx : Nat) (v : F) (hidx : idx < n) :
    sumF n (fun i => if i = idx then v else SimpleField.zero) = v := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [sumF]
    by_cases hk : k = idx
    · subst hk
      have h0 : sumF k (fun i => if i = k then v else SimpleField.zero) = SimpleField.zero := by
        rw [sumF_congr (g := fun _ => SimpleField.zero) (fun i hi => by
          have : i ≠ k := by omega
          simp [this])]
        exact sumF_zero k
      simp [h0, SimpleField.zero_add]
    · have hlt : idx < k := by omega
      simp [hk, ih hlt, f_add_zero]

/-- Concrete finite field `𝔽_2` on `Bool` (`false = 0`, `true = 1`, `add = xor`, `mul = and`). -/
instance instSimpleFieldBool : SimpleField Bool where
  zero := false
  one := true
  add := xor
  neg := id
  mul := and
  inv := id
  add_assoc := by decide
  add_comm := by decide
  zero_add := by decide
  add_neg := by decide
  mul_assoc := by decide
  mul_comm := by decide
  one_mul := by decide
  left_distrib := by decide
  zero_ne_one := by decide
  mul_inv_cancel := by decide

end
end ZeroErrorFrontier.GraphCore
