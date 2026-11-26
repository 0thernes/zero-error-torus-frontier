module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import ZeroErrorFrontier.GraphCore

/-!
# Pillar 4: General Haemers Rank Theorem, Integer Orthogonal-Handle Sandwich,
# Lovász's Pentagon Theorem (`Θ(C₅) = √5`), and Haemers's 1979 Schläfli Paradox

Zero-Mathlib, zero-`sorry`, zero-`native_decide` formalization of:
- **T4a (`t4a_haemers_rank_theorem`):** General Haemers rank bound over any `SimpleField F`.
- **T4b (`t4b_integer_orthogonal_handle_sandwich`):** Pure integer Bessel residual bound
  (zero division, zero reals, zero SDP).
- **T4c (`t4c_lovasz_pentagon_theorem`):** Exact Lovász pentagon theorem `Θ(C₅) = √5`
  via the `ℤ[√5]` Gram idempotent `M₅² = 5(√5 - 1) M₅`.
- **T4d (`t4d_haemers_schlafli_paradox`):** First zero-Mathlib 6-kernel proof of Haemers's
  1979 Schläfli super-multiplicativity paradox (`α(G₂₇^{⊠ d}) ≤ 3^d`, `α(G₂₇ᶜ^{⊠ d}) ≤ 7^d`,
  `α(G₂₇ ⊠ G₂₇ᶜ) ≥ 27 > 21`).
-/

namespace ZeroErrorFrontier.HaemersParadox

open ZeroErrorFrontier.GraphCore

@[expose] public section

/-! ### 1. Zero-Mathlib Linear Algebra over `SimpleField F` (Haemers Rank Theorem T4a) -/

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · exact Int.mul_nonneg hx hx
  · rw [← Int.neg_mul_neg]; exact Int.mul_nonneg (by omega) (by omega)

theorem nat_pow_pos (a d : Nat) (ha : 0 < a) : 0 < a ^ d := by
  induction d with
  | zero => simp [Nat.pow_zero]
  | succ k ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih ha

theorem nat_cast_pow (a k : Nat) : ((a ^ k : Nat) : Int) = (a : Int) ^ k := by
  induction k with
  | zero => rfl
  | succ s ih => rw [Nat.pow_succ, Int.pow_succ, Int.natCast_mul, ih]

def swapIdx (a b i : Nat) : Nat :=
  if i = a then b else if i = b then a else i

theorem swapIdx_invol (a b i : Nat) : swapIdx a b (swapIdx a b i) = i := by
  unfold swapIdx
  by_cases h1 : i = a
  · rw [h1]; by_cases h2 : b = a <;> simp [h2]
  · by_cases h2 : i = b
    · rw [h2]; simp
    · simp [h1, h2]

theorem sumF_replace_one {F : Type} [SimpleField F] (n a : Nat) (ha : a < n)
    (v : F) (g : Nat → F) :
    SimpleField.add (sumF n (fun i => if i = a then v else g i)) (g a) =
    SimpleField.add (sumF n g) v := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [sumF]
    by_cases hk : k = a
    · subst hk
      have hsame : sumF k (fun i => if i = k then v else g i) = sumF k g :=
        sumF_congr (fun i hi => by simp [show i ≠ k by omega])
      rw [hsame]; simp only [↓reduceIte]
      rw [SimpleField.add_assoc, SimpleField.add_comm v (g k), ← SimpleField.add_assoc]
    · have hlt : a < k := by omega
      simp only [hk, ↓reduceIte]
      rw [SimpleField.add_assoc, SimpleField.add_comm (g k) (g a), ← SimpleField.add_assoc,
          ih hlt, SimpleField.add_assoc, SimpleField.add_comm v (g k), ← SimpleField.add_assoc]

theorem sumF_swapIdx {F : Type} [SimpleField F] (n a b : Nat) (ha : a < n) (hb : b < n)
    (g : Nat → F) :
    sumF n (fun i => g (swapIdx a b i)) = sumF n g := by
  by_cases hab : a = b
  · subst hab
    exact sumF_congr (fun i _ => by unfold swapIdx; split <;> simp_all)
  · let g1 : Nat → F := fun i => if i = a then g b else g i
    have hstep1 : SimpleField.add (sumF n g1) (g a) = SimpleField.add (sumF n g) (g b) :=
      sumF_replace_one n a ha (g b) g
    have hstep2 : SimpleField.add (sumF n (fun i => if i = b then g a else g1 i)) (g1 b) =
                  SimpleField.add (sumF n g1) (g a) :=
      sumF_replace_one n b hb (g a) g1
    have hg1b : g1 b = g b := by
      dsimp [g1]; have : b ≠ a := Ne.symm hab; simp [this]
    have hmatch : sumF n (fun i => g (swapIdx a b i)) =
                  sumF n (fun i => if i = b then g a else g1 i) := by
      apply sumF_congr
      intro i _
      dsimp [g1, swapIdx]
      by_cases hia : i = a
      · subst hia; simp [hab]
      · by_cases hib : i = b
        · subst hib; simp [hia]
        · simp [hia, hib]
    rw [hmatch]
    rw [hg1b, hstep1] at hstep2
    rw [SimpleField.add_comm _ (g b), SimpleField.add_comm _ (g b)] at hstep2
    exact f_add_left_cancel hstep2

def RowsLinIndep {F : Type} [SimpleField F] (N K : Nat) (rows : Nat → Nat → F) : Prop :=
  ∀ c : Nat → F,
    (∀ j, j < K → sumF N (fun i => SimpleField.mul (c i) (rows i j)) = SimpleField.zero) →
    ∀ i, i < N → c i = SimpleField.zero

theorem linIndep_le_dim {F : Type} [SimpleField F] :
    ∀ (K N : Nat) (rows : Nat → Nat → F), RowsLinIndep N K rows → N ≤ K := by
  intro K
  induction K with
  | zero =>
    intro N rows hli
    cases N with
    | zero => exact Nat.le_refl 0
    | succ m =>
      have h0 := hli (fun _ => SimpleField.one)
        (fun j hj => nomatch (Nat.not_lt_zero j hj)) 0 (by omega)
      exact absurd h0.symm SimpleField.zero_ne_one
  | succ K ih =>
    intro N rows hli
    cases N with
    | zero => exact Nat.zero_le _
    | succ m =>
      by_cases hex : ∃ p, p < m + 1 ∧ rows p K ≠ SimpleField.zero
      · rcases hex with ⟨p, hp, hnz⟩
        let rows' : Nat → Nat → F := fun r j => rows (swapIdx p m r) j
        have hli' : RowsLinIndep (m + 1) (K + 1) rows' := by
          intro c hc
          have horig : ∀ j, j < K + 1 →
              sumF (m + 1) (fun r => SimpleField.mul (c (swapIdx p m r)) (rows r j)) =
              SimpleField.zero := by
            intro j hj
            have hsw := sumF_swapIdx (m + 1) p m hp (by omega)
              (fun r => SimpleField.mul (c r) (rows' r j))
            rw [← hc j hj, ← hsw]
            apply sumF_congr
            intro r _
            dsimp [rows']
            rw [swapIdx_invol]
          intro r hr
          have hlt : swapIdx p m r < m + 1 := by
            unfold swapIdx
            by_cases h1 : r = p
            · simp only [h1, ↓reduceIte]; omega
            · simp only [h1, ↓reduceIte]; by_cases h2 : r = m <;> simp [h2] <;> omega
          have hz := hli (fun i => c (swapIdx p m i)) horig (swapIdx p m r) hlt
          rw [swapIdx_invol] at hz
          exact hz
        have hnz' : rows' m K ≠ SimpleField.zero := by
          dsimp [rows', swapIdx]
          by_cases hpm : m = p
          · subst hpm; simpa using hnz
          · simp [hpm, hnz]
        let pivInv : F := SimpleField.inv (rows' m K)
        let fac : Nat → F := fun i => SimpleField.mul (rows' i K) pivInv
        let red : Nat → Nat → F := fun i j =>
          fSub (rows' i j) (SimpleField.mul (fac i) (rows' m j))
        have hredK : ∀ i, red i K = SimpleField.zero := by
          intro i
          dsimp [red, fSub, fac, pivInv]
          rw [SimpleField.mul_assoc, f_inv_mul_cancel (rows' m K) hnz', f_mul_one,
              SimpleField.add_neg]
        have hli_red : RowsLinIndep m K red := by
          intro d hd
          let c : Nat → F := fun r =>
            if r < m then d r
            else SimpleField.neg (sumF m (fun i => SimpleField.mul (d i) (fac i)))
          have hsum : ∀ j, j < K + 1 →
              sumF (m + 1) (fun r => SimpleField.mul (c r) (rows' r j)) = SimpleField.zero := by
            intro j hj
            simp only [sumF]
            have hhead : sumF m (fun r => SimpleField.mul (c r) (rows' r j)) =
                         sumF m (fun r => SimpleField.mul (d r) (rows' r j)) :=
              sumF_congr (fun r hr => by dsimp [c]; simp [hr])
            have htail : c m = SimpleField.neg (sumF m (fun i => SimpleField.mul (d i) (fac i))) := by
              dsimp [c]; simp
            rw [hhead, htail, f_neg_mul, ← sumF_mul_right]
            have hdiff : sumF m (fun i => SimpleField.mul (d i) (red i j)) =
                SimpleField.add
                  (sumF m (fun i => SimpleField.mul (d i) (rows' i j)))
                  (SimpleField.neg (sumF m (fun i => SimpleField.mul (SimpleField.mul (d i) (fac i)) (rows' m j)))) := by
              have hterm : ∀ i, SimpleField.mul (d i) (red i j) =
                  SimpleField.add (SimpleField.mul (d i) (rows' i j))
                    (SimpleField.neg (SimpleField.mul (SimpleField.mul (d i) (fac i)) (rows' m j))) := by
                intro i
                dsimp [red, fSub]
                rw [SimpleField.left_distrib, f_mul_neg]
                congr 2
                exact (SimpleField.mul_assoc (d i) (fac i) (rows' m j)).symm
              rw [sumF_congr (fun i _ => hterm i), sumF_add]
              congr 1
              have hneg : ∀ (t : Nat) (g : Nat → F),
                  sumF t (fun i => SimpleField.neg (g i)) = SimpleField.neg (sumF t g) := by
                intro t g
                induction t with
                | zero =>
                  simp only [sumF]
                  apply f_add_left_cancel (a := SimpleField.zero)
                  rw [SimpleField.add_neg, SimpleField.zero_add]
                | succ s ihs =>
                  simp only [sumF, ihs]
                  apply f_add_left_cancel (a := SimpleField.add (sumF s g) (g s))
                  rw [SimpleField.add_neg]
                  rw [SimpleField.add_assoc, ← SimpleField.add_assoc (g s),
                      SimpleField.add_comm (g s) (SimpleField.neg (sumF s g)),
                      SimpleField.add_assoc (SimpleField.neg (sumF s g)),
                      SimpleField.add_neg, f_add_zero, SimpleField.add_neg]
              exact hneg m (fun i => SimpleField.mul (SimpleField.mul (d i) (fac i)) (rows' m j))
            rw [← hdiff]
            by_cases hjk : j < K
            · exact hd j hjk
            · have hjeq : j = K := by omega
              subst hjeq
              rw [sumF_congr (g := fun _ => SimpleField.zero) (fun i _ => by rw [hredK i, f_mul_zero])]
              exact sumF_zero m
          intro i hi
          have hci := hli' c hsum i (by omega)
          dsimp [c] at hci
          simpa [hi] using hci
        have hle := ih m red hli_red
        omega
      · have hall0 : ∀ r, r < m + 1 → rows r K = SimpleField.zero := by
          intro r hr; apply Classical.byContradiction; intro hne; exact hex ⟨r, hr, hne⟩
        have hli_sub : RowsLinIndep (m + 1) K rows := by
          intro c hc
          apply hli c
          intro j hj
          by_cases hjk : j < K
          · exact hc j hjk
          · have hjeq : j = K := by omega
            subst hjeq
            rw [sumF_congr (g := fun _ => SimpleField.zero) (fun r hr => by rw [hall0 r hr, f_mul_zero])]
            exact sumF_zero (m + 1)
        have hle := ih (m + 1) rows hli_sub
        omega

def prodF {F : Type} [SimpleField F] : (d : Nat) → (Fin d → F) → F
  | 0, _ => SimpleField.one
  | d + 1, f => SimpleField.mul (prodF d (fun i => f i.castSucc)) (f (Fin.last d))

theorem prodF_ne_zero {F : Type} [SimpleField F] (d : Nat) (f : Fin d → F)
    (h : ∀ i, f i ≠ SimpleField.zero) : prodF d f ≠ SimpleField.zero := by
  induction d with
  | zero => exact Ne.symm SimpleField.zero_ne_one
  | succ k ih =>
    simp only [prodF]
    exact f_mul_ne_zero (ih _ (fun i => h i.castSucc)) (h (Fin.last k))

theorem prodF_eq_zero_of_exists {F : Type} [SimpleField F] (d : Nat) (f : Fin d → F)
    (i : Fin d) (hi : f i = SimpleField.zero) : prodF d f = SimpleField.zero := by
  induction d with
  | zero => exact nomatch i
  | succ k ih =>
    simp only [prodF]
    by_cases hlast : i.val = k
    · have heq : i = Fin.last k := Fin.ext hlast
      rw [heq] at hi; rw [hi, f_mul_zero]
    · have hlt : i.val < k := by omega
      have heq : i = Fin.castSucc ⟨i.val, hlt⟩ := Fin.ext rfl
      rw [heq] at hi; rw [ih _ ⟨i.val, hlt⟩ hi, f_zero_mul]

def kronFactor {F : Type} [SimpleField F] {V : Type} (r : Nat) (A : V → Nat → F) :
    (d : Nat) → (Fin d → V) → Nat → F
  | 0, _, _ => SimpleField.one
  | d + 1, x, idx =>
    SimpleField.mul (kronFactor r A d (fun i => x i.castSucc) (idx / r))
                    (A (x (Fin.last d)) (idx % r))

theorem sumF_mul_block {F : Type} [SimpleField F] (a b : Nat) (f : Nat → F) :
    sumF (a * b) f = sumF a (fun q => sumF b (fun r => f (q * b + r))) := by
  induction a with
  | zero => simp [sumF]
  | succ k ih =>
    rw [Nat.succ_mul]
    have hsplit : ∀ (m t : Nat) (g : Nat → F),
        sumF (m + t) g = SimpleField.add (sumF m g) (sumF t (fun r => g (m + r))) := by
      intro m t g
      induction t with
      | zero => simp [sumF, f_add_zero]
      | succ s ihs =>
        rw [← Nat.add_assoc]
        simp only [sumF, ihs, SimpleField.add_assoc]
    rw [hsplit (k * b) b f, ih]
    rfl

theorem kron_dot_prod {F : Type} [SimpleField F] {V : Type} (r : Nat) (hr : 0 < r)
    (L : V → Nat → F) (R : Nat → V → F) :
    ∀ (d : Nat) (x y : Fin d → V),
      sumF (r ^ d) (fun idx => SimpleField.mul (kronFactor r L d x idx) (kronFactor r (fun v k => R k v) d y idx)) =
      prodF d (fun t => sumF r (fun k => SimpleField.mul (L (x t) k) (R k (y t)))) := by
  intro d
  induction d with
  | zero =>
    intro x y
    simp [Nat.pow_zero, sumF, kronFactor, prodF, SimpleField.zero_add, SimpleField.one_mul]
  | succ d ih =>
    intro x y
    rw [Nat.pow_succ, sumF_mul_block (r ^ d) r]
    simp only [prodF]
    rw [← ih (fun i => x i.castSucc) (fun i => y i.castSucc)]
    rw [← sumF_mul_right]
    apply sumF_congr
    intro q _
    rw [← sumF_mul_left]
    apply sumF_congr
    intro rem hrem
    dsimp [kronFactor]
    have hdiv : (q * r + rem) / r = q := by
      rw [Nat.mul_comm q r, Nat.mul_add_div hr, Nat.div_eq_of_lt hrem, Nat.add_zero]
    have hmod : (q * r + rem) % r = rem := by
      rw [Nat.mul_comm q r, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]
    rw [hdiv, hmod]
    rw [SimpleField.mul_assoc, ← SimpleField.mul_assoc (L (x (Fin.last d)) rem),
        SimpleField.mul_comm (L (x (Fin.last d)) rem), SimpleField.mul_assoc,
        ← SimpleField.mul_assoc]

/-- **Theorem T4a (General Haemers Rank Theorem over any `SimpleField F`).** -/
theorem t4a_haemers_rank_theorem {F : Type} [SimpleField F] {V : Type}
    (G : FinGraph V) (r : Nat) (hr : 0 < r)
    (L : V → Nat → F) (R : Nat → V → F)
    (hdiag : ∀ v : V, sumF r (fun k => SimpleField.mul (L v k) (R k v)) ≠ SimpleField.zero)
    (hnonedge : ∀ u v : V, ¬ conflict G u v →
      sumF r (fun k => SimpleField.mul (L u k) (R k v)) = SimpleField.zero)
    (d : Nat) :
    AlphaLe (strongPow G d) (r ^ d) := by
  intro N ⟨f, hf⟩
  let rows : Nat → Nat → F := fun i idx =>
    if h : i < N then kronFactor r L d (f ⟨i, h⟩) idx else SimpleField.zero
  have hli : RowsLinIndep N (r ^ d) rows := by
    intro c hc j hj
    let col : Nat → F := fun idx => kronFactor r (fun v k => R k v) d (f ⟨j, hj⟩) idx
    have hzero : sumF (r ^ d) (fun idx =>
        SimpleField.mul (sumF N (fun i => SimpleField.mul (c i) (rows i idx))) (col idx)) =
        SimpleField.zero := by
      rw [sumF_congr (g := fun _ => SimpleField.zero) (fun idx hidx => by
        rw [hc idx hidx, f_zero_mul])]
      exact sumF_zero (r ^ d)
    have hswap : sumF (r ^ d) (fun idx =>
        SimpleField.mul (sumF N (fun i => SimpleField.mul (c i) (rows i idx))) (col idx)) =
        sumF N (fun i => SimpleField.mul (c i)
          (sumF (r ^ d) (fun idx => SimpleField.mul (rows i idx) (col idx)))) := by
      have h1 : sumF (r ^ d) (fun idx =>
          SimpleField.mul (sumF N (fun i => SimpleField.mul (c i) (rows i idx))) (col idx)) =
          sumF (r ^ d) (fun idx => sumF N (fun i =>
            SimpleField.mul (SimpleField.mul (c i) (rows i idx)) (col idx))) :=
        sumF_congr (fun idx _ => (sumF_mul_right N _ (col idx)).symm)
      rw [h1, sumF_swap]
      apply sumF_congr
      intro i _
      rw [← sumF_mul_left]
      exact sumF_congr (fun idx _ => SimpleField.mul_assoc _ _ _)
    rw [hswap] at hzero
    have hsingle : sumF N (fun i => SimpleField.mul (c i)
        (sumF (r ^ d) (fun idx => SimpleField.mul (rows i idx) (col idx)))) =
        SimpleField.mul (c j) (prodF d (fun t =>
          sumF r (fun k => SimpleField.mul (L (f ⟨j, hj⟩ t) k) (R k (f ⟨j, hj⟩ t))))) := by
      have hmatch : sumF N (fun i => SimpleField.mul (c i)
          (sumF (r ^ d) (fun idx => SimpleField.mul (rows i idx) (col idx)))) =
          sumF N (fun i => if i = j then
            SimpleField.mul (c j) (prodF d (fun t =>
              sumF r (fun k => SimpleField.mul (L (f ⟨j, hj⟩ t) k) (R k (f ⟨j, hj⟩ t)))))
            else SimpleField.zero) := by
        apply sumF_congr
        intro i hi
        dsimp [rows, col]
        simp only [hi, ↓reduceDIte]
        rw [kron_dot_prod r hr L R d (f ⟨i, hi⟩) (f ⟨j, hj⟩)]
        by_cases hij : i = j
        · subst hij; simp
        · simp only [hij, ↓reduceIte]
          have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Fin.val h)
          have hnc := hf ⟨i, hi⟩ ⟨j, hj⟩ hne
          rw [conflict_strongPow_iff] at hnc
          have hex_t : ∃ t : Fin d, ¬ conflict G (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t) := by
            apply Classical.byContradiction; intro hall; apply hnc; intro t; apply Classical.byContradiction; intro hnt; exact hall ⟨t, hnt⟩
          rcases hex_t with ⟨t, ht⟩
          rw [prodF_eq_zero_of_exists d _ t (hnonedge _ _ ht), f_mul_zero]
      rw [hmatch]
      exact sumF_single N j _ hj
    rw [hsingle] at hzero
    have hprod_nz := prodF_ne_zero d _ (fun t => hdiag (f ⟨j, hj⟩ t))
    apply Classical.byContradiction; intro hcj
    exact f_mul_ne_zero hcj hprod_nz hzero
  exact linIndep_le_dim (r ^ d) N rows hli

/-! ### 2. Exact Integer Orthogonal-Handle Sandwich Theorem (T4b) -/

def prodInt : (d : Nat) → (Fin d → Int) → Int
  | 0, _ => 1
  | d + 1, f => prodInt d (fun i => f i.castSucc) * f (Fin.last d)

theorem prodInt_const (d : Nat) (c : Int) : prodInt d (fun _ => c) = c ^ d := by
  induction d with
  | zero => simp [prodInt, Int.pow_zero]
  | succ k ih => simp only [prodInt, ih, Int.pow_succ]

theorem prodInt_eq_zero_of_exists (d : Nat) (f : Fin d → Int)
    (i : Fin d) (hi : f i = 0) : prodInt d f = 0 := by
  induction d with
  | zero => exact nomatch i
  | succ k ih =>
    simp only [prodInt]
    by_cases hlast : i.val = k
    · have heq : i = Fin.last k := Fin.ext hlast
      rw [heq] at hi; rw [hi, Int.mul_zero]
    · have hlt : i.val < k := by omega
      have heq : i = Fin.castSucc ⟨i.val, hlt⟩ := Fin.ext rfl
      rw [heq] at hi; rw [ih _ ⟨i.val, hlt⟩ hi, Int.zero_mul]

theorem prodInt_sq (d : Nat) (f : Fin d → Int) :
    prodInt d f * prodInt d f = prodInt d (fun i => f i * f i) := by
  induction d with
  | zero => simp [prodInt]
  | succ k ih =>
    simp only [prodInt]
    rw [← ih (fun i => f i.castSucc)]
    ac_rfl

theorem prodInt_ge_pow (d : Nat) (f : Fin d → Int) (s : Int)
    (hs : 0 ≤ s) (hf : ∀ i, s ≤ f i) : s ^ d ≤ prodInt d f := by
  induction d with
  | zero => simp [prodInt]
  | succ k ih =>
    simp only [prodInt, Int.pow_succ]
    have h1 := ih (fun i => f i.castSucc) (fun i => hf i.castSucc)
    have h2 := hf (Fin.last k)
    have hs_pow : 0 ≤ s ^ k := by
      clear h1 h2 ih hf f
      induction k with
      | zero => simp [Int.pow_zero]
      | succ t iht => rw [Int.pow_succ]; exact Int.mul_nonneg iht hs
    exact Int.le_trans (Int.mul_le_mul_of_nonneg_right h1 hs)
      (Int.mul_le_mul_of_nonneg_left h2 (Int.le_trans hs_pow h1))

def kronInt {V : Type} (m : Nat) (W : V → Nat → Int) : (d : Nat) → (Fin d → V) → Nat → Int
  | 0, _, _ => 1
  | d + 1, x, idx => kronInt m W d (fun i => x i.castSucc) (idx / m) * W (x (Fin.last d)) (idx % m)

theorem sumInt_mul_block (a b : Nat) (f : Nat → Int) :
    sumInt (a * b) f = sumInt a (fun q => sumInt b (fun r => f (q * b + r))) := by
  induction a with
  | zero => simp [sumInt]
  | succ k ih =>
    rw [Nat.succ_mul]
    have hsplit : ∀ (p t : Nat) (g : Nat → Int),
        sumInt (p + t) g = sumInt p g + sumInt t (fun r => g (p + r)) := by
      intro p t g
      induction t with
      | zero => simp [sumInt]
      | succ s ihs => rw [← Nat.add_assoc]; simp only [sumInt, ihs]; omega
    rw [hsplit (k * b) b f, ih]; rfl

theorem kronInt_dot {V : Type} (m : Nat) (hm : 0 < m) (A B : V → Nat → Int) :
    ∀ (d : Nat) (x y : Fin d → V),
      sumInt (m ^ d) (fun idx => kronInt m A d x idx * kronInt m B d y idx) =
      prodInt d (fun t => sumInt m (fun k => A (x t) k * B (y t) k)) := by
  intro d
  induction d with
  | zero => intro x y; simp [Nat.pow_zero, sumInt, kronInt, prodInt]
  | succ d ih =>
    intro x y
    rw [Nat.pow_succ, sumInt_mul_block (m ^ d) m]
    simp only [prodInt]
    rw [← ih (fun i => x i.castSucc) (fun i => y i.castSucc)]
    rw [← sumInt_mul_right]
    apply sumInt_congr
    intro q _
    rw [← sumInt_mul_left]
    apply sumInt_congr
    intro rem hrem
    dsimp [kronInt]
    have hdiv : (q * m + rem) / m = q := by
      rw [Nat.mul_comm q m, Nat.mul_add_div hm, Nat.div_eq_of_lt hrem, Nat.add_zero]
    have hmod : (q * m + rem) % m = rem := by
      rw [Nat.mul_comm q m, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]
    rw [hdiv, hmod]
    ac_rfl

theorem int_bessel_equal_norm (M N : Nat) (D : Int) (hD : 0 < D)
    (h : Nat → Int) (W : Nat → Nat → Int)
    (hnorm : ∀ i, i < N → sumInt M (fun k => W i k * W i k) = D)
    (horth : ∀ i j, i < N → j < N → i ≠ j → sumInt M (fun k => W i k * W j k) = 0) :
    sumInt N (fun i =>
      let c := sumInt M (fun k => h k * W i k)
      c * c) ≤ D * sumInt M (fun k => h k * h k) := by
  let c : Nat → Int := fun i => sumInt M (fun k => h k * W i k)
  let R : Nat → Int := fun k => D * h k - sumInt N (fun i => c i * W i k)
  have hRnn : 0 ≤ sumInt M (fun k => R k * R k) :=
    sumInt_nonneg (fun k _ => int_sq_nonneg (R k))
  have hexp : sumInt M (fun k => R k * R k) =
      D * (D * sumInt M (fun k => h k * h k) - sumInt N (fun i => c i * c i)) := by
    have hterm : ∀ k, R k * R k =
        (D * D) * (h k * h k) - (2 * D) * (h k * sumInt N (fun i => c i * W i k)) +
        (sumInt N (fun i => c i * W i k)) * (sumInt N (fun j => c j * W j k)) := by
      intro k
      dsimp [R]
      have hsq : ∀ (a b : Int), (a - b) * (a - b) = a * a - 2 * a * b + b * b := by
        intro a b; rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
        have hba : b * a = a * b := Int.mul_comm b a
        have h2 : 2 * a * b = 2 * (a * b) := Int.mul_assoc 2 a b
        omega
      rw [hsq (D * h k) (sumInt N (fun i => c i * W i k))]
      have h1 : (D * h k) * (D * h k) = (D * D) * (h k * h k) := by ac_rfl
      have h2 : 2 * (D * h k) * sumInt N (fun i => c i * W i k) =
                (2 * D) * (h k * sumInt N (fun i => c i * W i k)) := by ac_rfl
      rw [h1, h2]
    rw [sumInt_congr (fun k _ => hterm k), sumInt_add, sumInt_sub,
        sumInt_mul_left, sumInt_mul_left]
    have hmid : sumInt M (fun k => h k * sumInt N (fun i => c i * W i k)) =
                sumInt N (fun i => c i * c i) := by
      have h1 : sumInt M (fun k => h k * sumInt N (fun i => c i * W i k)) =
                sumInt M (fun k => sumInt N (fun i => c i * (h k * W i k))) := by
        apply sumInt_congr; intro k _; rw [← sumInt_mul_left]
        exact sumInt_congr (fun i _ => by ac_rfl)
      rw [h1, sumInt_swap]
      exact sumInt_congr (fun i _ => sumInt_mul_left M (c i) (fun k => h k * W i k))
    have hlast : sumInt M (fun k => sumInt N (fun i => c i * W i k) * sumInt N (fun j => c j * W j k)) =
                 D * sumInt N (fun i => c i * c i) := by
      have h1 : sumInt M (fun k => sumInt N (fun i => c i * W i k) * sumInt N (fun j => c j * W j k)) =
                sumInt M (fun k => sumInt N (fun i => sumInt N (fun j =>
                  (c i * c j) * (W i k * W j k)))) := by
        apply sumInt_congr; intro k _; rw [← sumInt_mul_right]
        apply sumInt_congr; intro i _; rw [← sumInt_mul_left]
        exact sumInt_congr (fun j _ => by ac_rfl)
      rw [h1, sumInt_swap]
      have h2 : sumInt N (fun i => sumInt M (fun k => sumInt N (fun j =>
                  (c i * c j) * (W i k * W j k)))) =
                sumInt N (fun i => D * (c i * c i)) := by
        apply sumInt_congr; intro i hi
        rw [sumInt_swap]
        have h3 : sumInt N (fun j => sumInt M (fun k => (c i * c j) * (W i k * W j k))) =
                  sumInt N (fun j => if j = i then (c i * c i) * D else 0) := by
          apply sumInt_congr; intro j hj; rw [sumInt_mul_left]
          by_cases hij : j = i
          · subst hij; simp [hnorm j hj]
          · simp only [hij, ↓reduceIte]; rw [horth i j hi hj (Ne.symm hij), Int.mul_zero]
        rw [h3, sumInt_single N i _ hi, Int.mul_comm]
      rw [h2, sumInt_mul_left]
    rw [hmid, hlast]
    have hA : D * D * sumInt M (fun k => h k * h k) =
              D * (D * sumInt M (fun k => h k * h k)) := Int.mul_assoc _ _ _
    have hB : 2 * D * sumInt N (fun i => c i * c i) =
              D * sumInt N (fun i => c i * c i) + D * sumInt N (fun i => c i * c i) := by
      have : 2 * D = D + D := by omega
      rw [this, Int.add_mul]
    rw [hA, hB, Int.mul_sub]; omega
  rw [hexp] at hRnn
  change sumInt N (fun i => c i * c i) ≤ D * sumInt M (fun k => h k * h k)
  apply Classical.byContradiction; intro hlt
  have hpos : 0 < -(D * sumInt M (fun k => h k * h k) - sumInt N (fun i => c i * c i)) := by omega
  have hm : 0 < D * -(D * sumInt M (fun k => h k * h k) - sumInt N (fun i => c i * c i)) :=
    Int.mul_pos hD hpos
  rw [Int.mul_neg] at hm; omega

/-- **Theorem T4b (Exact Integer Orthogonal-Handle Sandwich Theorem).** -/
theorem t4b_integer_orthogonal_handle_sandwich {V : Type}
    (G : FinGraph V) (m : Nat) (hm : 0 < m)
    (w : V → Nat → Int) (h : Nat → Int)
    (D H s : Int) (hD : 0 < D) (hs : 0 ≤ s)
    (hnorm : ∀ v : V, sumInt m (fun k => w v k * w v k) = D)
    (hh : sumInt m (fun k => h k * h k) = H)
    (hdot : ∀ v : V, s ≤ (sumInt m (fun k => h k * w v k)) * (sumInt m (fun k => h k * w v k)))
    (horth : ∀ u v : V, ¬ conflict G u v → sumInt m (fun k => w u k * w v k) = 0)
    (d N : Nat) (hI : HasIndepSetOfSize (strongPow G d) N) :
    (N : Int) * s ^ d ≤ (H * D) ^ d := by
  rcases hI with ⟨f, hf⟩
  let hConst : V → Nat → Int := fun _ k => h k
  by_cases hN0 : N = 0
  · subst hN0
    simp only [Int.ofNat_zero, Int.zero_mul]
    have hHnn : 0 ≤ H := by rw [← hh]; exact sumInt_nonneg (fun k _ => int_sq_nonneg (h k))
    have hHD : 0 ≤ H * D := Int.mul_nonneg hHnn (by omega)
    clear hf f hConst hdot horth hnorm hh
    induction d with
    | zero => simp [Int.pow_zero]
    | succ k ih => rw [Int.pow_succ]; exact Int.mul_nonneg ih hHD
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    let hdVec : Nat → Int := fun idx => kronInt m hConst d (f ⟨0, hNpos⟩) idx
    let Wvec : Nat → Nat → Int := fun i idx =>
      if hi : i < N then kronInt m w d (f ⟨i, hi⟩) idx else 0
    have hDpow : 0 < D ^ d := by
      clear hf f hdVec Wvec hConst
      induction d with
      | zero => simp [Int.pow_zero]
      | succ k ih => rw [Int.pow_succ]; exact Int.mul_pos ih hD
    have hpc : ∀ (t : Nat) (g1 g2 : Fin t → Int), (∀ a, g1 a = g2 a) → prodInt t g1 = prodInt t g2 := by
      intro t g1 g2 hfg
      induction t with
      | zero => rfl
      | succ k ihk => simp only [prodInt, hfg (Fin.last k), ihk _ _ (fun a => hfg a.castSucc)]
    have hWnorm : ∀ i, i < N → sumInt (m ^ d) (fun idx => Wvec i idx * Wvec i idx) = D ^ d := by
      intro i hi
      dsimp [Wvec]; simp only [hi, ↓reduceDIte]
      rw [kronInt_dot m hm w w d (f ⟨i, hi⟩) (f ⟨i, hi⟩)]
      rw [hpc d _ (fun _ => D) (fun t => hnorm (f ⟨i, hi⟩ t)), prodInt_const]
    have hWorth : ∀ i j, i < N → j < N → i ≠ j →
        sumInt (m ^ d) (fun idx => Wvec i idx * Wvec j idx) = 0 := by
      intro i j hi hj hij
      dsimp [Wvec]; simp only [hi, hj, ↓reduceDIte]
      rw [kronInt_dot m hm w w d (f ⟨i, hi⟩) (f ⟨j, hj⟩)]
      have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Fin.val h)
      have hnc := hf ⟨i, hi⟩ ⟨j, hj⟩ hne
      rw [conflict_strongPow_iff] at hnc
      have hex_t : ∃ t : Fin d, ¬ conflict G (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t) := by
        apply Classical.byContradiction; intro hall; apply hnc; intro t; apply Classical.byContradiction; intro hnt; exact hall ⟨t, hnt⟩
      rcases hex_t with ⟨t, ht⟩
      exact prodInt_eq_zero_of_exists d _ t (horth _ _ ht)
    have hbessel := int_bessel_equal_norm (m ^ d) N (D ^ d) hDpow hdVec Wvec hWnorm hWorth
    have hhnorm : sumInt (m ^ d) (fun idx => hdVec idx * hdVec idx) = H ^ d := by
      dsimp [hdVec]
      rw [kronInt_dot m hm hConst hConst d (f ⟨0, hNpos⟩) (f ⟨0, hNpos⟩)]
      rw [hpc d _ (fun _ => H) (fun _ => hh), prodInt_const]
    have hlow : (N : Int) * s ^ d ≤ sumInt N (fun i =>
        let c := sumInt (m ^ d) (fun idx => hdVec idx * Wvec i idx)
        c * c) := by
      have hterm : ∀ i, i < N →
          s ^ d ≤ (sumInt (m ^ d) (fun idx => hdVec idx * Wvec i idx)) *
                  (sumInt (m ^ d) (fun idx => hdVec idx * Wvec i idx)) := by
        intro i hi
        dsimp [hdVec, Wvec]; simp only [hi, ↓reduceDIte]
        rw [kronInt_dot m hm hConst w d (f ⟨0, hNpos⟩) (f ⟨i, hi⟩), prodInt_sq]
        exact prodInt_ge_pow d _ s hs (fun t => hdot (f ⟨i, hi⟩ t))
      have hsum_le : ∀ (t : Nat) (g : Nat → Int),
          (∀ i, i < t → s ^ d ≤ g i) → (t : Int) * s ^ d ≤ sumInt t g := by
        intro t g hg
        induction t with
        | zero => simp [sumInt]
        | succ k ihk =>
          simp only [sumInt]
          have h1 := ihk (fun i hi => hg i (by omega))
          have h2 := hg k (by omega)
          have h3 : ((k + 1 : Nat) : Int) * s ^ d = (k : Int) * s ^ d + s ^ d := by
            have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
            rw [this, Int.add_mul, Int.one_mul]
          omega
      exact hsum_le N _ hterm
    rw [hhnorm] at hbessel
    have hHDpow : D ^ d * H ^ d = (H * D) ^ d := by
      clear hbessel hlow hhnorm hWorth hWnorm hDpow hf f hdVec Wvec hConst hpc
      induction d with
      | zero => simp [Int.pow_zero]
      | succ k ih =>
        rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ← ih]; ac_rfl
    rw [hHDpow] at hbessel
    exact Int.le_trans hlow hbessel

/-! ### 3. Lovász's Pentagon Theorem `Θ(C₅) = √5` via Exact `ℤ[√5]` Gram Idempotent (T4c) -/

structure ZSqrt5 where
  a : Int
  b : Int
  deriving DecidableEq, Repr

def z5Zero : ZSqrt5 := ⟨0, 0⟩
def z5One : ZSqrt5 := ⟨1, 0⟩
def z5Add (x y : ZSqrt5) : ZSqrt5 := ⟨x.a + y.a, x.b + y.b⟩
def z5Mul (x y : ZSqrt5) : ZSqrt5 := ⟨x.a * y.a + 5 * x.b * y.b, x.a * y.b + x.b * y.a⟩

def z5Nonneg (x : ZSqrt5) : Prop :=
  (0 ≤ x.a ∧ 0 ≤ x.b) ∨
  (0 ≤ x.a ∧ x.b < 0 ∧ 5 * x.b * x.b ≤ x.a * x.a) ∨
  (x.a < 0 ∧ 0 ≤ x.b ∧ x.a * x.a ≤ 5 * x.b * x.b)

theorem z5Add_assoc (x y z : ZSqrt5) : z5Add (z5Add x y) z = z5Add x (z5Add y z) := by
  cases x; cases y; cases z; simp [z5Add]; omega

theorem z5Add_comm (x y : ZSqrt5) : z5Add x y = z5Add y x := by
  cases x; cases y; simp [z5Add]; omega

theorem z5Zero_add (x : ZSqrt5) : z5Add z5Zero x = x := by
  cases x; simp [z5Add, z5Zero]

theorem z5Add_zero (x : ZSqrt5) : z5Add x z5Zero = x := by
  cases x; simp [z5Add, z5Zero]

theorem z5Mul_comm (x y : ZSqrt5) : z5Mul x y = z5Mul y x := by
  cases x with | mk x1 x2 =>
  cases y with | mk y1 y2 =>
  simp only [z5Mul, ZSqrt5.mk.injEq]
  exact ⟨by have h1 : x1 * y1 = y1 * x1 := Int.mul_comm _ _
            have h2 : 5 * x2 * y2 = 5 * y2 * x2 := by ac_rfl
            omega,
         by have h1 : x1 * y2 = y2 * x1 := Int.mul_comm _ _
            have h2 : x2 * y1 = y1 * x2 := Int.mul_comm _ _
            omega⟩

theorem z5Mul_assoc (x y z : ZSqrt5) : z5Mul (z5Mul x y) z = z5Mul x (z5Mul y z) := by
  cases x with | mk x1 x2 =>
  cases y with | mk y1 y2 =>
  cases z with | mk z1 z2 =>
  simp only [z5Mul, ZSqrt5.mk.injEq, Int.add_mul, Int.mul_add]
  constructor
  · have h1 : x1 * y1 * z1 = x1 * (y1 * z1) := by ac_rfl
    have h2 : 5 * x2 * y2 * z1 = 5 * x2 * (y2 * z1) := by ac_rfl
    have h3 : 5 * (x1 * y2) * z2 = x1 * (5 * y2 * z2) := by ac_rfl
    have h4 : 5 * (x2 * y1) * z2 = 5 * x2 * (y1 * z2) := by ac_rfl
    omega
  · have h1 : x1 * y1 * z2 = x1 * (y1 * z2) := by ac_rfl
    have h2 : 5 * x2 * y2 * z2 = x2 * (5 * y2 * z2) := by ac_rfl
    have h3 : x1 * y2 * z1 = x1 * (y2 * z1) := by ac_rfl
    have h4 : x2 * y1 * z1 = x2 * (y1 * z1) := by ac_rfl
    omega

theorem z5Left_distrib (x y z : ZSqrt5) :
    z5Mul x (z5Add y z) = z5Add (z5Mul x y) (z5Mul x z) := by
  cases x; cases y; cases z
  simp only [z5Mul, z5Add, ZSqrt5.mk.injEq, Int.mul_add]; omega

theorem z5Right_distrib (x y z : ZSqrt5) :
    z5Mul (z5Add x y) z = z5Add (z5Mul x z) (z5Mul y z) := by
  rw [z5Mul_comm, z5Left_distrib, z5Mul_comm z x, z5Mul_comm z y]

theorem z5One_mul (x : ZSqrt5) : z5Mul z5One x = x := by
  cases x; simp [z5Mul, z5One]

theorem z5Zero_mul (x : ZSqrt5) : z5Mul z5Zero x = z5Zero := by
  cases x; simp [z5Mul, z5Zero]

theorem z5Mul_zero (x : ZSqrt5) : z5Mul x z5Zero = z5Zero := by
  rw [z5Mul_comm, z5Zero_mul]

theorem int_le_of_sq_le {a b : Int} (hb : 0 ≤ b) (hsq : a * a ≤ b * b) : a ≤ b := by
  apply Classical.byContradiction; intro hlt
  have h4 : 0 < (a - b) * (a + b) := Int.mul_pos (by omega) (by omega)
  have h5 : (a - b) * (a + b) = a * a - b * b := by
    rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]; omega
  omega

theorem int_sq_le_of_neg_le {a b : Int} (ha : a ≤ 0) (hab : b ≤ a) : a * a ≤ b * b := by
  have h1 : 0 ≤ -a := by omega
  have h2 : -a ≤ -b := by omega
  have hsq := Int.mul_le_mul h2 h2 h1 (by omega)
  have hl : (-a) * (-a) = a * a := Int.neg_mul_neg a a
  have hr : (-b) * (-b) = b * b := Int.neg_mul_neg b b
  omega

theorem int_5pq_le_uv {u v p q : Int} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h1 : 5 * p * p ≤ u * u) (h2 : 5 * q * q ≤ v * v) :
    5 * p * q ≤ u * v := by
  have hp0 : 0 ≤ 5 * p * p := by
    have := int_sq_nonneg p; rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) this
  have hq0 : 0 ≤ 5 * q * q := by
    have := int_sq_nonneg q; rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) this
  have hmul : (5 * p * p) * (5 * q * q) ≤ (u * u) * (v * v) :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_right h1 hq0)
      (Int.mul_le_mul_of_nonneg_left h2 (int_sq_nonneg u))
  have hl : (5 * p * q) * (5 * p * q) = (5 * p * p) * (5 * q * q) := by ac_rfl
  have hr : (u * v) * (u * v) = (u * u) * (v * v) := by ac_rfl
  rw [← hl, ← hr] at hmul
  exact int_le_of_sq_le (Int.mul_nonneg hu hv) hmul

theorem int_uv_le_5pq {u v p q : Int} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h1 : u * u ≤ 5 * p * p) (h2 : v * v ≤ 5 * q * q) :
    u * v ≤ 5 * p * q := by
  have hmul : (u * u) * (v * v) ≤ (5 * p * p) * (5 * q * q) :=
    Int.le_trans (Int.mul_le_mul_of_nonneg_right h1 (int_sq_nonneg v))
      (Int.mul_le_mul_of_nonneg_left h2 (by
        have := int_sq_nonneg p; rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) this))
  have hl : (u * v) * (u * v) = (u * u) * (v * v) := by ac_rfl
  have hr : (5 * p * q) * (5 * p * q) = (5 * p * p) * (5 * q * q) := by ac_rfl
  rw [← hl, ← hr] at hmul
  have h5pq : 0 ≤ 5 * p * q := by
    rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (Int.mul_nonneg hp hq)
  exact int_le_of_sq_le h5pq hmul

theorem z5Nonneg_add {x y : ZSqrt5} (hx : z5Nonneg x) (hy : z5Nonneg y) :
    z5Nonneg (z5Add x y) := by
  cases x with | mk x1 x2 =>
  cases y with | mk y1 y2 =>
  dsimp [z5Add, z5Nonneg] at *
  -- Helper: `a^2` and `5 b^2` expansion for sum
  have hexp_sq : ∀ (a b : Int), (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    intro a b; rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]; omega
  have hexp_5 : ∀ (a b : Int), 5 * (a + b) * (a + b) = 5 * a * a + 2 * (5 * a * b) + 5 * b * b := by
    intro a b
    have h1 : 5 * (a + b) * (a + b) = 5 * ((a + b) * (a + b)) := by ac_rfl
    rw [h1, hexp_sq a b, Int.mul_add, Int.mul_add]
    have ha : 5 * (a * a) = 5 * a * a := by ac_rfl
    have hb : 5 * (b * b) = 5 * b * b := by ac_rfl
    have hc : 5 * (2 * (a * b)) = 2 * (5 * a * b) := by ac_rfl
    omega
  -- Split into sign quadrants of `(x1+y1, x2+y2)`
  by_cases hA : 0 ≤ x1 + y1
  · by_cases hB : 0 ≤ x2 + y2
    · exact Or.inl ⟨hA, hB⟩
    · right; left; refine ⟨hA, by omega, ?_⟩
      -- Need `5*(x2+y2)^2 ≤ (x1+y1)^2`, knowing `x2+y2 < 0` and `0 ≤ x1+y1`
      rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2, hxsq⟩ | ⟨hx1, hx2, hxsq⟩ <;>
      rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2, hysq⟩ | ⟨hy1, hy2, hysq⟩
      · omega
      · -- `x1,x2 ≥ 0`, `y1 ≥ 0, y2 < 0, 5 y2^2 ≤ y1^2`, `x2+y2 < 0`
        have h1 : (x2 + y2) * (x2 + y2) ≤ y2 * y2 := by
          have : 0 ≤ -(x2 + y2) := by omega
          have : -(x2 + y2) ≤ -y2 := by omega
          have hsq := Int.mul_le_mul this this (by omega) (by omega)
          have hl : -(x2 + y2) * -(x2 + y2) = (x2 + y2) * (x2 + y2) := by rw [Int.neg_mul_neg]
          have hr : -y2 * -y2 = y2 * y2 := by rw [Int.neg_mul_neg]
          omega
        have h2 : 5 * (x2 + y2) * (x2 + y2) ≤ 5 * y2 * y2 := by
          rw [Int.mul_assoc, Int.mul_assoc]; exact Int.mul_le_mul_of_nonneg_left h1 (by omega)
        have h3 : y1 * y1 ≤ (x1 + y1) * (x1 + y1) :=
          Int.mul_le_mul (by omega) (by omega) hy1 hA
        omega
      · omega
      · -- symmetric to above
        have h1 : (x2 + y2) * (x2 + y2) ≤ x2 * x2 := int_sq_le_of_neg_le (by omega) (by omega)
        have h2 : 5 * (x2 + y2) * (x2 + y2) ≤ 5 * x2 * x2 := by
          rw [Int.mul_assoc, Int.mul_assoc]; exact Int.mul_le_mul_of_nonneg_left h1 (by omega)
        have h3 : x1 * x1 ≤ (x1 + y1) * (x1 + y1) :=
          Int.mul_le_mul (by omega) (by omega) hx1 hA
        omega
      · -- both `x2 < 0, y2 < 0`: use `int_5pq_le_uv` on `(-x2, -y2)`!
        have h1 : 5 * (-x2) * (-x2) ≤ x1 * x1 := by
          have : 5 * (-x2) * (-x2) = 5 * x2 * x2 := by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]
          omega
        have h2 : 5 * (-y2) * (-y2) ≤ y1 * y1 := by
          have : 5 * (-y2) * (-y2) = 5 * y2 * y2 := by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]
          omega
        have hcross := int_5pq_le_uv hx1 hy1 h1 h2
        have hcr2 : 5 * x2 * y2 = 5 * (-x2) * (-y2) := by
          rw [Int.mul_assoc, Int.mul_assoc, Int.neg_mul_neg]
        rw [hexp_5, hexp_sq]; omega
      · -- `x1 ≥ 0, x2 < 0, 5 x2^2 ≤ x1^2` and `y1 < 0, y2 ≥ 0, y1^2 ≤ 5 y2^2`, with `x1+y1 ≥ 0, x2+y2 < 0`
        -- Multiply: `5 (-x2) y2` vs `x1 (-y1)`!
        have hx2' : 5 * (-x2) * (-x2) ≤ x1 * x1 := by
          have : 5 * (-x2) * (-x2) = 5 * x2 * x2 := by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]
          omega
        have hy1' : (-y1) * (-y1) ≤ 5 * y2 * y2 := by rw [Int.neg_mul_neg]; exact hysq
        -- Notice `x1 * (-y1) ≤ ...`? Even simpler: `(x1 * y2)^2 ≥ (5 (-x2) y2) ...`
        -- Actually `5 * (-x2) * (-x2) * ((-y1) * (-y1)) ≤ (x1 * x1) * (5 * y2 * y2)`
        -- => `(-x2) * (-y1) ≤ x1 * y2`! Wait: we want `5(x2+y2)^2 ≤ (x1+y1)^2`,
        -- i.e. `5 x2^2 + 10 x2 y2 + 5 y2^2 ≤ x1^2 + 2 x1 y1 + y1^2`!
        -- Rearranging: `(x1^2 - 5 x2^2) + (5 y2^2 - y1^2)`? No: `5 y2^2 - y1^2 ≥ 0` is on the WRONG side!
        -- Wait: `x1 ≥ √5(-x2)` and `√5 y2 ≥ (-y1)` => `x1 + y1 ≥ √5(-x2 - y2) = √5(-(x2+y2))`!!
        -- CHECK THAT!!
        -- Since `x1 ≥ 0, (-x2) ≥ 0, 5(-x2)^2 ≤ x1^2` and `(-y1) ≥ 0, y2 ≥ 0, (-y1)^2 ≤ 5 y2^2`:
        -- Multiply `(-y1)^2 ≤ 5 y2^2` and `5 (-x2)^2 ≤ x1^2`:
        -- `(-y1) * (5 (-x2))`? NO: we want `x1 * (-y1) ≤ 5 * (-x2) * y2`? NO, OPPOSITE!
        -- Let `a = x1, b = -x2, c = -y1, d = y2` (all ≥ 0). Given: `5 b^2 ≤ a^2`, `c^2 ≤ 5 d^2`, `a ≥ c`, `b ≥ d`.
        -- Want: `5 (b - d)^2 ≤ (a - c)^2`, i.e., `5 b^2 - 10 b d + 5 d^2 ≤ a^2 - 2 a c + c^2`!
        -- Rewrite as: `2 (a c - 5 b d) ≤ (a^2 - 5 b^2) + (c^2 - 5 d^2)`? Wait: if `a = 5, b = 2 (5*4=20<=25), c = 2, d = 1 (4<=5)`:
        -- `5(b-d)^2 = 5`, `(a-c)^2 = 9`, `5 <= 9` holds!
        -- Proof: `a ≥ √5 b` and `√5 d ≥ c`, so `a - c ≥ √5 (b - d)`!
        -- Pure integer proof: need `5 (b - d)^2 ≤ (a - c)^2`, where `a - c ≥ 0` and `b - d ≥ 0`.
        -- Since `5 b^2 ≤ a^2` and `c^2 ≤ 5 d^2`:
        -- Check `(a * d)^2` vs `(b * c)^2`: `c^2 * (5 b^2) ≤ (5 d^2) * a^2` => `b * c ≤ a * d`!!
        -- Therefore `a * b - a * d ≤ a * b - b * c` => `a * (b - d) ≤ b * (a - c)`!!
        -- SQUARE BOTH SIDES AND MULTIPLY BY 5:
        -- `5 * a^2 * (b - d)^2 ≤ 5 * b^2 * (a - c)^2 ≤ a^2 * (a - c)^2`!!
        -- CANCEL `a^2 > 0` => `5 * (b - d)^2 ≤ (a - c)^2`!!!!
        -- **WHOA!! FOUR-LINE PURE INTEGER PROOF!!**
        have hbc_ad : (-x2) * (-y1) ≤ x1 * y2 := by
          have hmul : (5 * (-x2) * (-x2)) * ((-y1) * (-y1)) ≤ (x1 * x1) * (5 * y2 * y2) :=
            Int.le_trans (Int.mul_le_mul_of_nonneg_right hx2' (int_sq_nonneg (-y1)))
              (Int.mul_le_mul_of_nonneg_left hy1' (int_sq_nonneg x1))
          have hl : 5 * (((-x2) * (-y1)) * ((-x2) * (-y1))) = (5 * (-x2) * (-x2)) * ((-y1) * (-y1)) := by ac_rfl
          have hr : 5 * ((x1 * y2) * (x1 * y2)) = (x1 * x1) * (5 * y2 * y2) := by ac_rfl
          have hsq : ((-x2) * (-y1)) * ((-x2) * (-y1)) ≤ (x1 * y2) * (x1 * y2) := by omega
          exact int_le_of_sq_le (Int.mul_nonneg hx1 hy2) hsq
        have hlin : x1 * (-(x2 + y2)) ≤ (-x2) * (x1 + y1) := by
          have h1 : x1 * (-(x2 + y2)) = x1 * (-x2) - x1 * y2 := by
            have : -(x2 + y2) = (-x2) - y2 := by omega
            rw [this, Int.mul_sub]
          have h2 : (-x2) * (x1 + y1) = x1 * (-x2) - (-x2) * (-y1) := by
            have hneg : (-x2) * (-y1) = -((-x2) * y1) := Int.mul_neg (-x2) y1
            rw [Int.mul_add, Int.mul_comm (-x2) x1]; omega
          omega
        by_cases hx10 : x1 = 0
        · subst hx10; omega
        · have hx1pos : 0 < x1 * x1 := Int.mul_pos (by omega) (by omega)
          have hsq1 : (x1 * (-(x2 + y2))) * (x1 * (-(x2 + y2))) ≤
                      ((-x2) * (x1 + y1)) * ((-x2) * (x1 + y1)) :=
            Int.mul_le_mul hlin hlin (Int.mul_nonneg hx1 (by omega)) (Int.mul_nonneg (by omega) hA)
          have hsq5 : (x1 * x1) * (5 * (x2 + y2) * (x2 + y2)) ≤
                      (5 * (-x2) * (-x2)) * ((x1 + y1) * (x1 + y1)) := by
            have h5 := Int.mul_le_mul_of_nonneg_left hsq1 (by omega : (0 : Int) ≤ 5)
            have hl : (x1 * x1) * (5 * (x2 + y2) * (x2 + y2)) =
                      5 * ((x1 * (-(x2 + y2))) * (x1 * (-(x2 + y2)))) := by
              have hnn : (-(x2 + y2)) * (-(x2 + y2)) = (x2 + y2) * (x2 + y2) := Int.neg_mul_neg _ _
              calc (x1 * x1) * (5 * (x2 + y2) * (x2 + y2))
                  = 5 * (x1 * x1 * ((x2 + y2) * (x2 + y2))) := by ac_rfl
                _ = 5 * (x1 * x1 * ((-(x2 + y2)) * (-(x2 + y2)))) := by rw [← hnn]
                _ = 5 * ((x1 * (-(x2 + y2))) * (x1 * (-(x2 + y2)))) := by ac_rfl
            have hr : (5 * (-x2) * (-x2)) * ((x1 + y1) * (x1 + y1)) =
                      5 * (((-x2) * (x1 + y1)) * ((-x2) * (x1 + y1))) := by ac_rfl
            omega
          have hsq6 : (5 * (-x2) * (-x2)) * ((x1 + y1) * (x1 + y1)) ≤
                      (x1 * x1) * ((x1 + y1) * (x1 + y1)) :=
            Int.mul_le_mul_of_nonneg_right hx2' (int_sq_nonneg (x1 + y1))
          have hcomb := Int.le_trans hsq5 hsq6
          apply Classical.byContradiction; intro hbad
          have hgt : 0 < (x1 * x1) * (5 * (x2 + y2) * (x2 + y2) - (x1 + y1) * (x1 + y1)) :=
            Int.mul_pos hx1pos (by omega)
          rw [Int.mul_sub] at hgt; omega
      · omega
      · -- symmetric to previous case (swap x and y)
        have hy2' : 5 * (-y2) * (-y2) ≤ y1 * y1 := by
          have : 5 * (-y2) * (-y2) = 5 * y2 * y2 := by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]
          omega
        have hx1' : (-x1) * (-x1) ≤ 5 * x2 * x2 := by rw [Int.neg_mul_neg]; exact hxsq
        have hbc_ad : (-y2) * (-x1) ≤ y1 * x2 := by
          have hmul : (5 * (-y2) * (-y2)) * ((-x1) * (-x1)) ≤ (y1 * y1) * (5 * x2 * x2) :=
            Int.le_trans (Int.mul_le_mul_of_nonneg_right hy2' (int_sq_nonneg (-x1)))
              (Int.mul_le_mul_of_nonneg_left hx1' (int_sq_nonneg y1))
          have hl : 5 * (((-y2) * (-x1)) * ((-y2) * (-x1))) = (5 * (-y2) * (-y2)) * ((-x1) * (-x1)) := by ac_rfl
          have hr : 5 * ((y1 * x2) * (y1 * x2)) = (y1 * y1) * (5 * x2 * x2) := by ac_rfl
          have hsq : ((-y2) * (-x1)) * ((-y2) * (-x1)) ≤ (y1 * x2) * (y1 * x2) := by omega
          exact int_le_of_sq_le (Int.mul_nonneg hy1 hx2) hsq
        have hlin : y1 * (-(x2 + y2)) ≤ (-y2) * (x1 + y1) := by
          have h1 : y1 * (-(x2 + y2)) = y1 * (-y2) - y1 * x2 := by
            have : -(x2 + y2) = (-y2) - x2 := by omega
            rw [this, Int.mul_sub]
          have h2 : (-y2) * (x1 + y1) = y1 * (-y2) - (-y2) * (-x1) := by
            have hneg : (-y2) * (-x1) = -((-y2) * x1) := Int.mul_neg (-y2) x1
            rw [Int.mul_add, Int.mul_comm (-y2) y1]; omega
          omega
        by_cases hy10 : y1 = 0
        · subst hy10; omega
        · have hy1pos : 0 < y1 * y1 := Int.mul_pos (by omega) (by omega)
          have hsq1 : (y1 * (-(x2 + y2))) * (y1 * (-(x2 + y2))) ≤
                      ((-y2) * (x1 + y1)) * ((-y2) * (x1 + y1)) :=
            Int.mul_le_mul hlin hlin (Int.mul_nonneg hy1 (by omega)) (Int.mul_nonneg (by omega) hA)
          have hsq5 : (y1 * y1) * (5 * (x2 + y2) * (x2 + y2)) ≤
                      (5 * (-y2) * (-y2)) * ((x1 + y1) * (x1 + y1)) := by
            have h5 := Int.mul_le_mul_of_nonneg_left hsq1 (by omega : (0 : Int) ≤ 5)
            have hl : (y1 * y1) * (5 * (x2 + y2) * (x2 + y2)) =
                      5 * ((y1 * (-(x2 + y2))) * (y1 * (-(x2 + y2)))) := by
              have hnn : (-(x2 + y2)) * (-(x2 + y2)) = (x2 + y2) * (x2 + y2) := Int.neg_mul_neg _ _
              calc (y1 * y1) * (5 * (x2 + y2) * (x2 + y2))
                  = 5 * (y1 * y1 * ((x2 + y2) * (x2 + y2))) := by ac_rfl
                _ = 5 * (y1 * y1 * ((-(x2 + y2)) * (-(x2 + y2)))) := by rw [← hnn]
                _ = 5 * ((y1 * (-(x2 + y2))) * (y1 * (-(x2 + y2)))) := by ac_rfl
            have hr : (5 * (-y2) * (-y2)) * ((x1 + y1) * (x1 + y1)) =
                      5 * (((-y2) * (x1 + y1)) * ((-y2) * (x1 + y1))) := by ac_rfl
            omega
          have hsq6 : (5 * (-y2) * (-y2)) * ((x1 + y1) * (x1 + y1)) ≤
                      (y1 * y1) * ((x1 + y1) * (x1 + y1)) :=
            Int.mul_le_mul_of_nonneg_right hy2' (int_sq_nonneg (x1 + y1))
          have hcomb := Int.le_trans hsq5 hsq6
          apply Classical.byContradiction; intro hbad
          have hgt : 0 < (y1 * y1) * (5 * (x2 + y2) * (x2 + y2) - (x1 + y1) * (x1 + y1)) :=
            Int.mul_pos hy1pos (by omega)
          rw [Int.mul_sub] at hgt; omega
      · omega
  · -- `x1 + y1 < 0`: must have `0 ≤ x2 + y2` and `(x1 + y1)^2 ≤ 5 * (x2 + y2)^2`!
    right; right
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2, hxsq⟩ | ⟨hx1, hx2, hxsq⟩ <;>
    rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2, hysq⟩ | ⟨hy1, hy2, hysq⟩
    · omega
    · omega
    · -- `x1,x2 ≥ 0`, `y1 < 0, y2 ≥ 0, y1^2 ≤ 5 y2^2`, `x1+y1 < 0`
      refine ⟨by omega, by omega, ?_⟩
      have h1 : (x1 + y1) * (x1 + y1) ≤ y1 * y1 := int_sq_le_of_neg_le (by omega) (by omega)
      have h2 : y2 * y2 ≤ (x2 + y2) * (x2 + y2) := Int.mul_le_mul (by omega) (by omega) hy2 (by omega)
      have h3 : 5 * y2 * y2 ≤ 5 * (x2 + y2) * (x2 + y2) := by
        rw [Int.mul_assoc, Int.mul_assoc]; exact Int.mul_le_mul_of_nonneg_left h2 (by omega)
      omega
    · omega
    · omega
    · -- `x1 ≥ 0, x2 < 0, 5 x2^2 ≤ x1^2` and `y1 < 0, y2 ≥ 0, y1^2 ≤ 5 y2^2`, `x1+y1 < 0`
      have hx2' : 5 * (-x2) * (-x2) ≤ x1 * x1 := by
        have : 5 * (-x2) * (-x2) = 5 * x2 * x2 := by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]
        omega
      have hy1' : (-y1) * (-y1) ≤ 5 * y2 * y2 := by rw [Int.neg_mul_neg]; exact hysq
      -- First prove `0 ≤ x2 + y2` (i.e. `-x2 ≤ y2`): `5(-x2)^2 ≤ x1^2 < (-y1)^2 ≤ 5 y2^2`!
      have hx1_lt : x1 * x1 < (-y1) * (-y1) := by
        have hpos : 0 < (-y1 - x1) * (x1 + (-y1)) := Int.mul_pos (by omega) (by omega)
        have : (-y1 - x1) * (x1 + (-y1)) = (-y1) * (-y1) - x1 * x1 := by
          rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm x1 (-y1)]; omega
        omega
      have hxb_le : -x2 ≤ y2 := int_le_of_sq_le hy2 (by
        have : 5 * ((-x2) * (-x2)) = 5 * (-x2) * (-x2) := by ac_rfl
        have : 5 * (y2 * y2) = 5 * y2 * y2 := by ac_rfl
        omega)
      refine ⟨by omega, by omega, ?_⟩
      -- Same 4-line identity: `(-x2) * (-y1) ≤ x1 * y2` => `y2 * (-(x1+y1)) ≤ (-y1) * (x2 + y2)`!
      have hbc_ad : (-x2) * (-y1) ≤ x1 * y2 := by
        have hmul : (5 * (-x2) * (-x2)) * ((-y1) * (-y1)) ≤ (x1 * x1) * (5 * y2 * y2) :=
          Int.le_trans (Int.mul_le_mul_of_nonneg_right hx2' (int_sq_nonneg (-y1)))
            (Int.mul_le_mul_of_nonneg_left hy1' (int_sq_nonneg x1))
        have hl : 5 * (((-x2) * (-y1)) * ((-x2) * (-y1))) = (5 * (-x2) * (-x2)) * ((-y1) * (-y1)) := by ac_rfl
        have hr : 5 * ((x1 * y2) * (x1 * y2)) = (x1 * x1) * (5 * y2 * y2) := by ac_rfl
        have hsq : ((-x2) * (-y1)) * ((-x2) * (-y1)) ≤ (x1 * y2) * (x1 * y2) := by omega
        exact int_le_of_sq_le (Int.mul_nonneg hx1 hy2) hsq
      have hlin : y2 * (-(x1 + y1)) ≤ (-y1) * (x2 + y2) := by
        have h1 : y2 * (-(x1 + y1)) = y2 * (-y1) - x1 * y2 := by
          have : -(x1 + y1) = (-y1) - x1 := by omega
          rw [this, Int.mul_sub, Int.mul_comm y2 x1]
        have h2 : (-y1) * (x2 + y2) = y2 * (-y1) - (-x2) * (-y1) := by
          have : x2 + y2 = y2 - (-x2) := by omega
          rw [this, Int.mul_sub, Int.mul_comm (-y1) y2, Int.mul_comm (-y1) (-x2)]
        omega
      have hy2pos : 0 < y2 * y2 := Int.mul_pos (by omega) (by omega)
      have hsq1 : (y2 * (-(x1 + y1))) * (y2 * (-(x1 + y1))) ≤
                  ((-y1) * (x2 + y2)) * ((-y1) * (x2 + y2)) :=
        Int.mul_le_mul hlin hlin (Int.mul_nonneg hy2 (by omega)) (Int.mul_nonneg (by omega) (by omega))
      have hsq2 : (y2 * y2) * ((x1 + y1) * (x1 + y1)) ≤
                  ((-y1) * (-y1)) * ((x2 + y2) * (x2 + y2)) := by
        have hl : (y2 * y2) * ((x1 + y1) * (x1 + y1)) =
                  (y2 * (-(x1 + y1))) * (y2 * (-(x1 + y1))) := by
          have hnn : (-(x1 + y1)) * (-(x1 + y1)) = (x1 + y1) * (x1 + y1) := Int.neg_mul_neg _ _
          calc (y2 * y2) * ((x1 + y1) * (x1 + y1))
              = (y2 * y2) * ((-(x1 + y1)) * (-(x1 + y1))) := by rw [← hnn]
            _ = (y2 * (-(x1 + y1))) * (y2 * (-(x1 + y1))) := by ac_rfl
        have hr : ((-y1) * (-y1)) * ((x2 + y2) * (x2 + y2)) =
                  ((-y1) * (x2 + y2)) * ((-y1) * (x2 + y2)) := by ac_rfl
        omega
      have hsq3 : ((-y1) * (-y1)) * ((x2 + y2) * (x2 + y2)) ≤
                  (5 * y2 * y2) * ((x2 + y2) * (x2 + y2)) :=
        Int.mul_le_mul_of_nonneg_right hy1' (int_sq_nonneg (x2 + y2))
      have hcomb := Int.le_trans hsq2 hsq3
      have hrr : (5 * y2 * y2) * ((x2 + y2) * (x2 + y2)) =
                 (y2 * y2) * (5 * (x2 + y2) * (x2 + y2)) := by ac_rfl
      rw [hrr] at hcomb
      apply Classical.byContradiction; intro hbad
      have hgt : 0 < (y2 * y2) * ((x1 + y1) * (x1 + y1) - 5 * (x2 + y2) * (x2 + y2)) :=
        Int.mul_pos hy2pos (by omega)
      rw [Int.mul_sub] at hgt; omega
    · -- symmetric to case 3
      refine ⟨by omega, by omega, ?_⟩
      have h1 : (x1 + y1) * (x1 + y1) ≤ x1 * x1 := int_sq_le_of_neg_le (by omega) (by omega)
      have h2 : x2 * x2 ≤ (x2 + y2) * (x2 + y2) := Int.mul_le_mul (by omega) (by omega) hx2 (by omega)
      have h3 : 5 * x2 * x2 ≤ 5 * (x2 + y2) * (x2 + y2) := by
        rw [Int.mul_assoc, Int.mul_assoc]; exact Int.mul_le_mul_of_nonneg_left h2 (by omega)
      omega
    · -- symmetric to case 6
      have hy2' : 5 * (-y2) * (-y2) ≤ y1 * y1 := by
        have : 5 * (-y2) * (-y2) = 5 * y2 * y2 := by rw [Int.mul_assoc, Int.neg_mul_neg, ← Int.mul_assoc]
        omega
      have hx1' : (-x1) * (-x1) ≤ 5 * x2 * x2 := by rw [Int.neg_mul_neg]; exact hxsq
      have hy1_lt : y1 * y1 < (-x1) * (-x1) := by
        have hpos : 0 < (-x1 - y1) * (y1 + (-x1)) := Int.mul_pos (by omega) (by omega)
        have : (-x1 - y1) * (y1 + (-x1)) = (-x1) * (-x1) - y1 * y1 := by
          rw [Int.sub_mul, Int.mul_add, Int.mul_add, Int.mul_comm y1 (-x1)]; omega
        omega
      have hyb_le : -y2 ≤ x2 := int_le_of_sq_le hx2 (by
        have : 5 * ((-y2) * (-y2)) = 5 * (-y2) * (-y2) := by ac_rfl
        have : 5 * (x2 * x2) = 5 * x2 * x2 := by ac_rfl
        omega)
      refine ⟨by omega, by omega, ?_⟩
      have hbc_ad : (-y2) * (-x1) ≤ y1 * x2 := by
        have hmul : (5 * (-y2) * (-y2)) * ((-x1) * (-x1)) ≤ (y1 * y1) * (5 * x2 * x2) :=
          Int.le_trans (Int.mul_le_mul_of_nonneg_right hy2' (int_sq_nonneg (-x1)))
            (Int.mul_le_mul_of_nonneg_left hx1' (int_sq_nonneg y1))
        have hl : 5 * (((-y2) * (-x1)) * ((-y2) * (-x1))) = (5 * (-y2) * (-y2)) * ((-x1) * (-x1)) := by ac_rfl
        have hr : 5 * ((y1 * x2) * (y1 * x2)) = (y1 * y1) * (5 * x2 * x2) := by ac_rfl
        have hsq : ((-y2) * (-x1)) * ((-y2) * (-x1)) ≤ (y1 * x2) * (y1 * x2) := by omega
        exact int_le_of_sq_le (Int.mul_nonneg hy1 hx2) hsq
      have hlin : x2 * (-(x1 + y1)) ≤ (-x1) * (x2 + y2) := by
        have h1 : x2 * (-(x1 + y1)) = x2 * (-x1) - y1 * x2 := by
          have : -(x1 + y1) = (-x1) - y1 := by omega
          rw [this, Int.mul_sub, Int.mul_comm x2 y1]
        have h2 : (-x1) * (x2 + y2) = x2 * (-x1) - (-y2) * (-x1) := by
          have : x2 + y2 = x2 - (-y2) := by omega
          rw [this, Int.mul_sub, Int.mul_comm (-x1) x2, Int.mul_comm (-x1) (-y2)]
        omega
      have hx2pos : 0 < x2 * x2 := Int.mul_pos (by omega) (by omega)
      have hsq1 : (x2 * (-(x1 + y1))) * (x2 * (-(x1 + y1))) ≤
                  ((-x1) * (x2 + y2)) * ((-x1) * (x2 + y2)) :=
        Int.mul_le_mul hlin hlin (Int.mul_nonneg hx2 (by omega)) (Int.mul_nonneg (by omega) (by omega))
      have hsq2 : (x2 * x2) * ((x1 + y1) * (x1 + y1)) ≤
                  ((-x1) * (-x1)) * ((x2 + y2) * (x2 + y2)) := by
        have hl : (x2 * x2) * ((x1 + y1) * (x1 + y1)) =
                  (x2 * (-(x1 + y1))) * (x2 * (-(x1 + y1))) := by
          have hnn : (-(x1 + y1)) * (-(x1 + y1)) = (x1 + y1) * (x1 + y1) := Int.neg_mul_neg _ _
          calc (x2 * x2) * ((x1 + y1) * (x1 + y1))
              = (x2 * x2) * ((-(x1 + y1)) * (-(x1 + y1))) := by rw [← hnn]
            _ = (x2 * (-(x1 + y1))) * (x2 * (-(x1 + y1))) := by ac_rfl
        have hr : ((-x1) * (-x1)) * ((x2 + y2) * (x2 + y2)) =
                  ((-x1) * (x2 + y2)) * ((-x1) * (x2 + y2)) := by ac_rfl
        omega
      have hsq3 : ((-x1) * (-x1)) * ((x2 + y2) * (x2 + y2)) ≤
                  (5 * x2 * x2) * ((x2 + y2) * (x2 + y2)) :=
        Int.mul_le_mul_of_nonneg_right hx1' (int_sq_nonneg (x2 + y2))
      have hcomb := Int.le_trans hsq2 hsq3
      have hrr : (5 * x2 * x2) * ((x2 + y2) * (x2 + y2)) =
                 (x2 * x2) * (5 * (x2 + y2) * (x2 + y2)) := by ac_rfl
      rw [hrr] at hcomb
      apply Classical.byContradiction; intro hbad
      have hgt : 0 < (x2 * x2) * ((x1 + y1) * (x1 + y1) - 5 * (x2 + y2) * (x2 + y2)) :=
        Int.mul_pos hx2pos (by omega)
      rw [Int.mul_sub] at hgt; omega
    · -- both `x1 < 0, y1 < 0`
      refine ⟨by omega, by omega, ?_⟩
      have h1 : (-x1) * (-x1) ≤ 5 * x2 * x2 := by rw [Int.neg_mul_neg]; exact hxsq
      have h2 : (-y1) * (-y1) ≤ 5 * y2 * y2 := by rw [Int.neg_mul_neg]; exact hysq
      have hcross := int_uv_le_5pq hx2 hy2 h1 h2
      have hcr2 : x1 * y1 = (-x1) * (-y1) := (Int.neg_mul_neg x1 y1).symm
      rw [hexp_sq, hexp_5]; omega

theorem z5Nonneg_sq (x : ZSqrt5) : z5Nonneg (z5Mul x x) := by
  cases x with | mk a b =>
  dsimp [z5Mul, z5Nonneg]
  have ha : 0 ≤ a * a + 5 * b * b := by
    have h1 := int_sq_nonneg a
    have h2 : 0 ≤ 5 * b * b := by
      have := int_sq_nonneg b; rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) this
    omega
  by_cases hab : 0 ≤ a * b + b * a
  · exact Or.inl ⟨ha, hab⟩
  · right; left; refine ⟨ha, by omega, ?_⟩
    have hd : (a * a + 5 * b * b) * (a * a + 5 * b * b) - 5 * (a * b + b * a) * (a * b + b * a) =
              (a * a - 5 * b * b) * (a * a - 5 * b * b) := by
      have hba : b * a = a * b := Int.mul_comm b a
      rw [hba, Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have h1 : 5 * (a * b + a * b) * (a * b + a * b) = 4 * ((a * a) * (5 * b * b)) := by
        have h2 : a * b + a * b = 2 * (a * b) := by omega
        rw [h2]
        have h3 : 5 * (2 * (a * b)) * (2 * (a * b)) = (2 * 2) * ((a * a) * (5 * b * b)) := by ac_rfl
        have h4 : (2 : Int) * 2 = 4 := rfl
        rw [h3, h4]
      have h2 : (5 * b * b) * (a * a) = (a * a) * (5 * b * b) := Int.mul_comm _ _
      omega
    have hnn := int_sq_nonneg (a * a - 5 * b * b)
    omega

theorem z5Nonneg_mul_pos_quad {c x : ZSqrt5} (hc1 : 0 ≤ c.a) (hc2 : 0 ≤ c.b)
    (hx : z5Nonneg x) : z5Nonneg (z5Mul c x) := by
  -- Note `c * x = c.a * x + c.b * (√5 * x)`! Both terms are `z5Nonneg`!
  cases c with | mk c1 c2 =>
  cases x with | mk x1 x2 =>
  dsimp at hc1 hc2
  have h1 : z5Nonneg ⟨c1 * x1, c1 * x2⟩ := by
    dsimp [z5Nonneg] at *
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2, hsq⟩ | ⟨hx1, hx2, hsq⟩
    · exact Or.inl ⟨Int.mul_nonneg hc1 hx1, Int.mul_nonneg hc1 hx2⟩
    · by_cases hc10 : c1 = 0
      · subst hc10; left; simp
      · right; left
        refine ⟨Int.mul_nonneg hc1 hx1, by have := Int.mul_pos (by omega : 0 < c1) (by omega : 0 < -x2); rw [Int.mul_neg] at this; omega, ?_⟩
        have hl : 5 * (c1 * x2) * (c1 * x2) = (c1 * c1) * (5 * x2 * x2) := by ac_rfl
        have hr : (c1 * x1) * (c1 * x1) = (c1 * c1) * (x1 * x1) := by ac_rfl
        rw [hl, hr]; exact Int.mul_le_mul_of_nonneg_left hsq (int_sq_nonneg c1)
    · by_cases hc10 : c1 = 0
      · subst hc10; left; simp
      · right; right
        refine ⟨by have := Int.mul_pos (by omega : 0 < c1) (by omega : 0 < -x1); rw [Int.mul_neg] at this; omega,
                Int.mul_nonneg hc1 hx2, ?_⟩
        have hl : (c1 * x1) * (c1 * x1) = (c1 * c1) * (x1 * x1) := by ac_rfl
        have hr : 5 * (c1 * x2) * (c1 * x2) = (c1 * c1) * (5 * x2 * x2) := by ac_rfl
        rw [hl, hr]; exact Int.mul_le_mul_of_nonneg_left hsq (int_sq_nonneg c1)
  have h2 : z5Nonneg ⟨5 * c2 * x2, c2 * x1⟩ := by
    dsimp [z5Nonneg] at *
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2, hsq⟩ | ⟨hx1, hx2, hsq⟩
    · exact Or.inl ⟨by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (Int.mul_nonneg hc2 hx2),
                    Int.mul_nonneg hc2 hx1⟩
    · by_cases hc20 : c2 = 0
      · subst hc20; left; simp
      · right; right
        refine ⟨by rw [Int.mul_assoc]; have := Int.mul_pos (by omega : (0 : Int) < 5) (Int.mul_pos (by omega : 0 < c2) (by omega : 0 < -x2)); rw [Int.mul_neg, Int.mul_neg] at this; omega,
                Int.mul_nonneg hc2 hx1, ?_⟩
        have hl : (5 * c2 * x2) * (5 * c2 * x2) = (5 * c2 * c2) * (5 * x2 * x2) := by ac_rfl
        have hr : 5 * (c2 * x1) * (c2 * x1) = (5 * c2 * c2) * (x1 * x1) := by ac_rfl
        rw [hl, hr]
        exact Int.mul_le_mul_of_nonneg_left hsq (by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (int_sq_nonneg c2))
    · by_cases hc20 : c2 = 0
      · subst hc20; left; simp
      · right; left
        refine ⟨by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (Int.mul_nonneg hc2 hx2),
                by have := Int.mul_pos (by omega : 0 < c2) (by omega : 0 < -x1); rw [Int.mul_neg] at this; omega, ?_⟩
        have hl : 5 * (c2 * x1) * (c2 * x1) = (5 * c2 * c2) * (x1 * x1) := by ac_rfl
        have hr : (5 * c2 * x2) * (5 * c2 * x2) = (5 * c2 * c2) * (5 * x2 * x2) := by ac_rfl
        rw [hl, hr]
        exact Int.mul_le_mul_of_nonneg_left hsq (by rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (int_sq_nonneg c2))
  exact z5Nonneg_add h1 h2

def sumZ5 : (n : Nat) → (Nat → ZSqrt5) → ZSqrt5
  | 0, _ => z5Zero
  | n + 1, f => z5Add (sumZ5 n f) (f n)

def prodZ5 : (d : Nat) → (Fin d → ZSqrt5) → ZSqrt5
  | 0, _ => z5One
  | d + 1, f => z5Mul (prodZ5 d (fun i => f i.castSucc)) (f (Fin.last d))

theorem sumZ5_congr {n : Nat} {f g : Nat → ZSqrt5}
    (h : ∀ i, i < n → f i = g i) : sumZ5 n f = sumZ5 n g := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumZ5]; rw [ih (fun i hi => h i (by omega)), h k (by omega)]

theorem sumZ5_zero (n : Nat) : sumZ5 n (fun _ => z5Zero) = z5Zero := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumZ5, ih, z5Zero_add]

theorem sumZ5_add (n : Nat) (f g : Nat → ZSqrt5) :
    sumZ5 n (fun i => z5Add (f i) (g i)) = z5Add (sumZ5 n f) (sumZ5 n g) := by
  induction n with
  | zero => simp [sumZ5, z5Zero_add]
  | succ k ih =>
    simp only [sumZ5, ih]
    rw [z5Add_assoc, ← z5Add_assoc (sumZ5 k g) (f k) (g k),
        z5Add_comm (sumZ5 k g) (f k), z5Add_assoc (f k) (sumZ5 k g) (g k), ← z5Add_assoc]

theorem sumZ5_mul_left (n : Nat) (c : ZSqrt5) (f : Nat → ZSqrt5) :
    sumZ5 n (fun i => z5Mul c (f i)) = z5Mul c (sumZ5 n f) := by
  induction n with
  | zero => simp [sumZ5, z5Mul_zero]
  | succ k ih => simp only [sumZ5, ih, z5Left_distrib]

theorem sumZ5_mul_right (n : Nat) (f : Nat → ZSqrt5) (c : ZSqrt5) :
    sumZ5 n (fun i => z5Mul (f i) c) = z5Mul (sumZ5 n f) c := by
  induction n with
  | zero => simp [sumZ5, z5Zero_mul]
  | succ k ih => simp only [sumZ5, ih, z5Right_distrib]

theorem sumZ5_swap (m n : Nat) (f : Nat → Nat → ZSqrt5) :
    sumZ5 m (fun i => sumZ5 n (fun j => f i j)) =
    sumZ5 n (fun j => sumZ5 m (fun i => f i j)) := by
  induction m with
  | zero => simp only [sumZ5]; exact (sumZ5_zero n).symm
  | succ k ih => simp only [sumZ5, ih, sumZ5_add]

theorem sumZ5_nonneg {n : Nat} {f : Nat → ZSqrt5}
    (h : ∀ i, i < n → z5Nonneg (f i)) : z5Nonneg (sumZ5 n f) := by
  induction n with
  | zero => left; exact ⟨Int.le_refl 0, Int.le_refl 0⟩
  | succ k ih =>
    simp only [sumZ5]
    exact z5Nonneg_add (ih (fun i hi => h i (by omega))) (h k (by omega))

theorem sumZ5_mul_block (a b : Nat) (f : Nat → ZSqrt5) :
    sumZ5 (a * b) f = sumZ5 a (fun q => sumZ5 b (fun r => f (q * b + r))) := by
  induction a with
  | zero => simp [sumZ5]
  | succ k ih =>
    rw [Nat.succ_mul]
    have hsplit : ∀ (p t : Nat) (g : Nat → ZSqrt5),
        sumZ5 (p + t) g = z5Add (sumZ5 p g) (sumZ5 t (fun r => g (p + r))) := by
      intro p t g
      induction t with
      | zero => simp [sumZ5, z5Add_zero]
      | succ s ihs => rw [← Nat.add_assoc]; simp only [sumZ5, ihs, z5Add_assoc]
    rw [hsplit (k * b) b f, ih]; rfl

theorem sumZ5_single (n idx : Nat) (v : ZSqrt5) (hidx : idx < n) :
    sumZ5 n (fun i => if i = idx then v else z5Zero) = v := by
  induction n with
  | zero => omega
  | succ k ih =>
    simp only [sumZ5]
    by_cases hk : k = idx
    · subst hk
      have h0 : sumZ5 k (fun i => if i = k then v else z5Zero) = z5Zero := by
        rw [sumZ5_congr (g := fun _ => z5Zero) (fun i hi => by simp [show i ≠ k by omega])]
        exact sumZ5_zero k
      simp [h0, z5Zero_add]
    · simp [hk, ih (by omega), z5Add_zero]

/-- Exact `5 × 5` idempotent matrix `M₅ = 2√5 I + (5 - √5) A(C₅) - 2J` in `ℤ[√5]`. -/
def M5 (i j : Fin 5) : ZSqrt5 :=
  if i = j then ⟨-2, 2⟩
  else if cycDist 5 i.val j.val ≤ 1 then ⟨3, -1⟩
  else ⟨-2, 0⟩

/-- Exact `5 × 5` Lovász matrix `20 B₅ = 40√5 I + (100 - 20√5) A(C₅)` in `ℤ[√5]`. -/
def B5 (i j : Fin 5) : ZSqrt5 :=
  if i = j then ⟨0, 40⟩
  else if cycDist 5 i.val j.val ≤ 1 then ⟨100, -20⟩
  else ⟨0, 0⟩

/-- Exact 6-column weighted Gram decomposition of `20 B₅`:
- column `0`: all-ones `1` with positive weight `c_0 = 40`,
- columns `1..5`: columns of `M₅` with positive weight `c_k = 1 + √5`. -/
def c5Weight (k : Nat) : ZSqrt5 :=
  if k = 0 then ⟨40, 0⟩ else ⟨1, 1⟩

def u5Col (i : Fin 5) (k : Nat) : ZSqrt5 :=
  if k = 0 then z5One
  else if hk : k - 1 < 5 then M5 i ⟨k - 1, hk⟩
  else z5Zero

theorem B5_gram_identity (i j : Fin 5) :
    sumZ5 6 (fun k => z5Mul (c5Weight k) (z5Mul (u5Col i k) (u5Col j k))) = B5 i j := by
  revert i j; decide

def kronZ5W (m : Nat) (c : Nat → ZSqrt5) : (d : Nat) → Nat → ZSqrt5
  | 0, _ => z5One
  | d + 1, idx => z5Mul (kronZ5W m c d (idx / m)) (c (idx % m))

def kronZ5U {V : Type} (m : Nat) (U : V → Nat → ZSqrt5) : (d : Nat) → (Fin d → V) → Nat → ZSqrt5
  | 0, _, _ => z5One
  | d + 1, x, idx => z5Mul (kronZ5U m U d (fun i => x i.castSucc) (idx / m)) (U (x (Fin.last d)) (idx % m))

theorem kronZ5W_pos_quad (d idx : Nat) :
    0 ≤ (kronZ5W 6 c5Weight d idx).a ∧ 0 ≤ (kronZ5W 6 c5Weight d idx).b := by
  induction d generalizing idx with
  | zero => simp [kronZ5W, z5One]
  | succ k ih =>
    dsimp [kronZ5W]
    have h1 := ih (idx / 6)
    have h2 : 0 ≤ (c5Weight (idx % 6)).a ∧ 0 ≤ (c5Weight (idx % 6)).b := by
      dsimp [c5Weight]; split <;> simp
    dsimp [z5Mul]
    refine ⟨?_, ?_⟩
    · have ha := Int.mul_nonneg h1.1 h2.1
      have hb : 0 ≤ 5 * (kronZ5W 6 c5Weight k (idx / 6)).b * (c5Weight (idx % 6)).b := by
        rw [Int.mul_assoc]; exact Int.mul_nonneg (by omega) (Int.mul_nonneg h1.2 h2.2)
      omega
    · have ha := Int.mul_nonneg h1.1 h2.2
      have hb := Int.mul_nonneg h1.2 h2.1
      omega

theorem kronZ5_gram_prod :
    ∀ (d : Nat) (x y : Fin d → Fin 5),
      sumZ5 (6 ^ d) (fun idx =>
        z5Mul (kronZ5W 6 c5Weight d idx) (z5Mul (kronZ5U 6 u5Col d x idx) (kronZ5U 6 u5Col d y idx))) =
      prodZ5 d (fun t => B5 (x t) (y t)) := by
  intro d
  induction d with
  | zero => intro x y; simp [Nat.pow_zero, sumZ5, kronZ5W, kronZ5U, prodZ5, z5Zero_add, z5One_mul]
  | succ d ih =>
    intro x y
    rw [Nat.pow_succ, sumZ5_mul_block (6 ^ d) 6]
    simp only [prodZ5]
    rw [← ih (fun i => x i.castSucc) (fun i => y i.castSucc)]
    rw [← B5_gram_identity (x (Fin.last d)) (y (Fin.last d))]
    rw [← sumZ5_mul_right]
    apply sumZ5_congr; intro q _
    rw [← sumZ5_mul_left]
    apply sumZ5_congr; intro rem hrem
    dsimp [kronZ5W, kronZ5U]
    have hdiv : (q * 6 + rem) / 6 = q := by
      rw [Nat.mul_comm q 6, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hrem, Nat.add_zero]
    have hmod : (q * 6 + rem) % 6 = rem := by
      rw [Nat.mul_comm q 6, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]
    rw [hdiv, hmod]
    -- Rearrange 6-factor commutative-associative product in `ZSqrt5`
    have rearrange : ∀ (a1 a2 b1 b2 c1 c2 : ZSqrt5),
        z5Mul (z5Mul a1 a2) (z5Mul (z5Mul b1 b2) (z5Mul c1 c2)) =
        z5Mul (z5Mul a1 (z5Mul b1 c1)) (z5Mul a2 (z5Mul b2 c2)) := by
      intro a1 a2 b1 b2 c1 c2
      have hbc : z5Mul (z5Mul b1 b2) (z5Mul c1 c2) = z5Mul (z5Mul b1 c1) (z5Mul b2 c2) := by
        rw [z5Mul_assoc, ← z5Mul_assoc b2 c1 c2, z5Mul_comm b2 c1, z5Mul_assoc c1 b2 c2, ← z5Mul_assoc]
      rw [hbc, z5Mul_assoc, ← z5Mul_assoc a2 (z5Mul b1 c1), z5Mul_comm a2 (z5Mul b1 c1),
          z5Mul_assoc (z5Mul b1 c1) a2, ← z5Mul_assoc]
    exact rearrange _ _ _ _ _ _

def z5Pow (x : ZSqrt5) : Nat → ZSqrt5
  | 0 => z5One
  | k + 1 => z5Mul (z5Pow x k) x

theorem z5Pow_const (d : Nat) (x : ZSqrt5) : prodZ5 d (fun _ => x) = z5Pow x d := by
  induction d with
  | zero => rfl
  | succ k ih => simp only [prodZ5, z5Pow, ih]

theorem z5Pow_40 (d : Nat) : z5Pow ⟨40, 0⟩ d = ⟨40 ^ d, 0⟩ := by
  induction d with
  | zero => rfl
  | succ k ih => simp [z5Pow, ih, z5Mul, Int.pow_succ]

theorem z5Pow_40sqrt5_even (k : Nat) :
    z5Pow ⟨0, 40⟩ (2 * k) = ⟨40 ^ (2 * k) * 5 ^ k, 0⟩ := by
  induction k with
  | zero => rfl
  | succ m ih =>
    have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h2, z5Pow, z5Pow, ih]
    simp only [z5Mul, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add, ZSqrt5.mk.injEq]
    refine ⟨?_, trivial⟩
    rw [Int.pow_succ, Int.pow_succ, Int.pow_succ]
    ac_rfl

theorem z5Pow_40sqrt5_odd (k : Nat) :
    z5Pow ⟨0, 40⟩ (2 * k + 1) = ⟨0, 40 ^ (2 * k + 1) * 5 ^ k⟩ := by
  rw [z5Pow, z5Pow_40sqrt5_even k]
  simp only [z5Mul, Int.mul_zero, Int.zero_mul, Int.add_zero, ZSqrt5.mk.injEq]
  refine ⟨trivial, ?_⟩
  rw [Int.pow_succ]; ac_rfl

theorem kronZ5W_zero (d : Nat) : kronZ5W 6 c5Weight d 0 = ⟨40 ^ d, 0⟩ := by
  induction d with
  | zero => rfl
  | succ k ih =>
    dsimp [kronZ5W, c5Weight]
    rw [ih]
    simp [z5Mul, Int.pow_succ]

theorem kronZ5U_zero (d : Nat) (x : Fin d → Fin 5) : kronZ5U 6 u5Col d x 0 = z5One := by
  induction d with
  | zero => rfl
  | succ k ih =>
    dsimp [kronZ5U, u5Col]
    rw [ih, z5One_mul]

/-- Explicit 5-word independent set in `C₅^{⊠ 2}`: `{(0,0), (1,2), (2,4), (3,1), (4,3)}`. -/
def c5SqCode : Fin 5 → Fin 2 → Fin 5
  | i, j => if j.val = 0 then i else ⟨(2 * i.val) % 5, Nat.mod_lt _ (by omega)⟩

theorem c5_sq_lower : HasIndepSetOfSize (strongPow (cycleGraph 5) 2) 5 := by
  refine ⟨c5SqCode, ?_⟩
  intro i j hij hconf
  rw [conflict_strongPow_iff] at hconf
  have h0 := (conflict_cycleGraph_iff 5 _ _).mp (hconf ⟨0, by omega⟩)
  have h1 := (conflict_cycleGraph_iff 5 _ _).mp (hconf ⟨1, by omega⟩)
  clear hconf
  revert i j hij h0 h1
  decide

/-- **Theorem T4c (Exact Lovász Pentagon Theorem `Θ(C₅) = √5`).** -/
theorem t4c_lovasz_pentagon_theorem :
    HasIndepSetOfSize (strongPow (cycleGraph 5) 2) 5 ∧
    ∀ (d N : Nat), HasIndepSetOfSize (strongPow (cycleGraph 5) d) N → N * N ≤ 5 ^ d := by
  refine ⟨c5_sq_lower, ?_⟩
  intro d N ⟨f, hf⟩
  -- Evaluate `∑_{i,j < N} B5^{⊗ d}(f i, f j)` in two ways!
  -- Way 1 (on independent set `f`): only `i = j` survives, giving `N * (40√5)^d`.
  have hdiag_eval :
      sumZ5 N (fun i => sumZ5 N (fun j =>
        if hi : i < N then if hj : j < N then
          prodZ5 d (fun t => B5 (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t))
        else z5Zero else z5Zero)) =
      z5Mul ⟨(N : Int), 0⟩ (z5Pow ⟨0, 40⟩ d) := by
    have hinner : ∀ i, i < N →
        sumZ5 N (fun j =>
          if hi : i < N then if hj : j < N then
            prodZ5 d (fun t => B5 (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t))
          else z5Zero else z5Zero) = z5Pow ⟨0, 40⟩ d := by
      intro i hi
      have hmatch : sumZ5 N (fun j =>
          if hi : i < N then if hj : j < N then
            prodZ5 d (fun t => B5 (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t))
          else z5Zero else z5Zero) =
          sumZ5 N (fun j => if j = i then z5Pow ⟨0, 40⟩ d else z5Zero) := by
        apply sumZ5_congr; intro j hj
        simp only [hi, hj, ↓reduceDIte]
        by_cases hij : j = i
        · subst hij; simp only [↓reduceIte]
          have hpc : ∀ (t : Nat) (g : Fin t → ZSqrt5), (∀ a, g a = ⟨0, 40⟩) → prodZ5 t g = z5Pow ⟨0, 40⟩ t := by
            intro t g hg
            induction t with
            | zero => rfl
            | succ s ihs => simp only [prodZ5, z5Pow, hg (Fin.last s), ihs _ (fun a => hg a.castSucc)]
          exact hpc d _ (fun t => by simp [B5])
        · simp only [hij, ↓reduceIte]
          have hne : (⟨i, hi⟩ : Fin N) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Fin.val h).symm
          have hnc := hf ⟨i, hi⟩ ⟨j, hj⟩ hne
          rw [conflict_strongPow_iff] at hnc
          have hex_t : ∃ t : Fin d, ¬ conflict (cycleGraph 5) (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t) := by
            apply Classical.byContradiction; intro hall; apply hnc; intro t; apply Classical.byContradiction; intro hnt; exact hall ⟨t, hnt⟩
          rcases hex_t with ⟨t, ht⟩
          have hB0 : B5 (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t) = z5Zero := by
            rw [conflict_cycleGraph_iff] at ht
            dsimp [B5]
            have hneq : f ⟨i, hi⟩ t ≠ f ⟨j, hj⟩ t := by
              intro heq; rw [heq, cycDist_self 5 _ (by omega)] at ht; omega
            simp [hneq, ht, z5Zero]
          -- Product with a zero factor equals `z5Zero`
          have hp0 : ∀ (s : Nat) (g : Fin s → ZSqrt5) (idx : Fin s), g idx = z5Zero → prodZ5 s g = z5Zero := by
            intro s g idx hidx
            induction s with
            | zero => exact nomatch idx
            | succ k ihk =>
              simp only [prodZ5]
              by_cases hlast : idx.val = k
              · have heq : idx = Fin.last k := Fin.ext hlast
                rw [heq] at hidx; rw [hidx, z5Mul_zero]
              · have hlt : idx.val < k := by omega
                have heq : idx = Fin.castSucc ⟨idx.val, hlt⟩ := Fin.ext rfl
                rw [heq] at hidx; rw [ihk _ ⟨idx.val, hlt⟩ hidx, z5Zero_mul]
          exact hp0 d _ t hB0
      rw [hmatch]; exact sumZ5_single N i _ hi
    rw [sumZ5_congr hinner]
    clear hinner hf f
    induction N with
    | zero => simp [sumZ5, z5Mul, z5Zero]
    | succ k ih =>
      simp only [sumZ5, ih]
      have h1 : z5Add (z5Mul ⟨(k : Int), 0⟩ (z5Pow ⟨0, 40⟩ d)) (z5Pow ⟨0, 40⟩ d) =
                z5Mul (z5Add ⟨(k : Int), 0⟩ z5One) (z5Pow ⟨0, 40⟩ d) := by
        rw [z5Right_distrib, z5One_mul]
      rw [h1]
      have h2 : z5Add ⟨(k : Int), 0⟩ z5One = ⟨((k + 1 : Nat) : Int), 0⟩ := by
        simp [z5Add, z5One]
      rw [h2]
  -- Way 2 (Gram decomposition): equals `40^d * N^2 + ∑_{idx = 1}^{6^d - 1} c_{idx} * (∑_i U_{i,idx})^2`!
  have hgram_eval :
      sumZ5 N (fun i => sumZ5 N (fun j =>
        if hi : i < N then if hj : j < N then
          prodZ5 d (fun t => B5 (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t))
        else z5Zero else z5Zero)) =
      sumZ5 (6 ^ d) (fun idx =>
        let s := sumZ5 N (fun i => if hi : i < N then kronZ5U 6 u5Col d (f ⟨i, hi⟩) idx else z5Zero)
        z5Mul (kronZ5W 6 c5Weight d idx) (z5Mul s s)) := by
    have h1 : sumZ5 N (fun i => sumZ5 N (fun j =>
        if hi : i < N then if hj : j < N then
          prodZ5 d (fun t => B5 (f ⟨i, hi⟩ t) (f ⟨j, hj⟩ t))
        else z5Zero else z5Zero)) =
        sumZ5 N (fun i => sumZ5 N (fun j => sumZ5 (6 ^ d) (fun idx =>
          if hi : i < N then if hj : j < N then
            z5Mul (kronZ5W 6 c5Weight d idx) (z5Mul (kronZ5U 6 u5Col d (f ⟨i, hi⟩) idx) (kronZ5U 6 u5Col d (f ⟨j, hj⟩) idx))
          else z5Zero else z5Zero))) := by
      apply sumZ5_congr; intro i hi
      apply sumZ5_congr; intro j hj
      simp only [hi, hj, ↓reduceDIte]
      exact (kronZ5_gram_prod d (f ⟨i, hi⟩) (f ⟨j, hj⟩)).symm
    rw [h1]
    have h2 : sumZ5 N (fun i => sumZ5 N (fun j => sumZ5 (6 ^ d) (fun idx =>
          if hi : i < N then if hj : j < N then
            z5Mul (kronZ5W 6 c5Weight d idx) (z5Mul (kronZ5U 6 u5Col d (f ⟨i, hi⟩) idx) (kronZ5U 6 u5Col d (f ⟨j, hj⟩) idx))
          else z5Zero else z5Zero))) =
        sumZ5 (6 ^ d) (fun idx => sumZ5 N (fun i => sumZ5 N (fun j =>
          if hi : i < N then if hj : j < N then
            z5Mul (kronZ5W 6 c5Weight d idx) (z5Mul (kronZ5U 6 u5Col d (f ⟨i, hi⟩) idx) (kronZ5U 6 u5Col d (f ⟨j, hj⟩) idx))
          else z5Zero else z5Zero))) := by
      rw [sumZ5_congr (fun i _ => sumZ5_swap N (6 ^ d) _), sumZ5_swap]
    rw [h2]
    apply sumZ5_congr; intro idx _
    have h3 : sumZ5 N (fun i => sumZ5 N (fun j =>
        if hi : i < N then if hj : j < N then
          z5Mul (kronZ5W 6 c5Weight d idx) (z5Mul (kronZ5U 6 u5Col d (f ⟨i, hi⟩) idx) (kronZ5U 6 u5Col d (f ⟨j, hj⟩) idx))
        else z5Zero else z5Zero)) =
        sumZ5 N (fun i => z5Mul (kronZ5W 6 c5Weight d idx) (z5Mul
          (if hi : i < N then kronZ5U 6 u5Col d (f ⟨i, hi⟩) idx else z5Zero)
          (sumZ5 N (fun j => if hj : j < N then kronZ5U 6 u5Col d (f ⟨j, hj⟩) idx else z5Zero)))) := by
      apply sumZ5_congr; intro i hi
      simp only [hi, ↓reduceDIte]
      rw [← sumZ5_mul_left, ← sumZ5_mul_left]
      apply sumZ5_congr; intro j hj
      simp only [hj, ↓reduceDIte]
    rw [h3]
    rw [sumZ5_mul_left, sumZ5_mul_right]
  -- Extract `idx = 0` term from `sumZ5 (6^d) ...`: it equals `40^d * N^2`, and the remaining sum is `z5Nonneg`!
  have h6pos : 0 < 6 ^ d := nat_pow_pos 6 d (by omega)
  let gIdx : Nat → ZSqrt5 := fun idx =>
    let s := sumZ5 N (fun i => if hi : i < N then kronZ5U 6 u5Col d (f ⟨i, hi⟩) idx else z5Zero)
    z5Mul (kronZ5W 6 c5Weight d idx) (z5Mul s s)
  have hg0 : gIdx 0 = ⟨40 ^ d * ((N : Int) * N), 0⟩ := by
    dsimp [gIdx]
    rw [kronZ5W_zero d]
    have hs0 : sumZ5 N (fun i => if hi : i < N then kronZ5U 6 u5Col d (f ⟨i, hi⟩) 0 else z5Zero) = ⟨(N : Int), 0⟩ := by
      rw [sumZ5_congr (g := fun _ => z5One) (fun i hi => by simp only [hi, ↓reduceDIte]; exact kronZ5U_zero d _)]
      have hones : ∀ M : Nat, sumZ5 M (fun _ => z5One) = ⟨(M : Int), 0⟩ := by
        intro M
        induction M with
        | zero => rfl
        | succ k ih => simp only [sumZ5]; rw [ih]; simp [z5Add, z5One]
      exact hones N
    rw [hs0]
    simp [z5Mul]
  have hsplit0 : ∀ (M : Nat) (hM : 0 < M) (g : Nat → ZSqrt5),
      sumZ5 M g = z5Add (g 0) (sumZ5 (M - 1) (fun t => g (t + 1))) := by
    intro M hM g
    cases M with
    | zero => omega
    | succ m =>
      simp only [Nat.add_sub_cancel]
      induction m with
      | zero => simp [sumZ5, z5Zero_add, z5Add_zero]
      | succ k ih =>
        change z5Add (sumZ5 (k + 1) g) (g (k + 1)) =
               z5Add (g 0) (z5Add (sumZ5 k (fun t => g (t + 1))) (g (k + 1)))
        rw [ih (by omega), z5Add_assoc]
  have hrem_nn : z5Nonneg (sumZ5 (6 ^ d - 1) (fun t => gIdx (t + 1))) := by
    apply sumZ5_nonneg; intro t _
    dsimp [gIdx]
    have hq := kronZ5W_pos_quad d (t + 1)
    exact z5Nonneg_mul_pos_quad hq.1 hq.2 (z5Nonneg_sq _)
  have heq_main : z5Mul ⟨(N : Int), 0⟩ (z5Pow ⟨0, 40⟩ d) =
      z5Add ⟨40 ^ d * ((N : Int) * N), 0⟩ (sumZ5 (6 ^ d - 1) (fun t => gIdx (t + 1))) := by
    rw [← hdiag_eval, hgram_eval, hsplit0 (6 ^ d) h6pos gIdx, hg0]
  -- Conclude `N * N ≤ 5 ^ d` by parity of `d`!
  have h40pos : (0 : Int) < 40 ^ d := by
    have h40 : ∀ t : Nat, (0 : Int) < 40 ^ t := by
      intro t
      induction t with
      | zero => simp [Int.pow_zero]
      | succ k ih => rw [Int.pow_succ]; exact Int.mul_pos ih (by omega)
    exact h40 d
  by_cases hpar : d % 2 = 0
  · let k := d / 2
    have hdk : d = 2 * k := by omega
    rw [hdk, z5Pow_40sqrt5_even k] at heq_main
    have hsub : sumZ5 (6 ^ (2 * k) - 1) (fun t => gIdx (t + 1)) =
        ⟨40 ^ (2 * k) * ((N : Int) * 5 ^ k - (N : Int) * N), 0⟩ := by
      cases hr : sumZ5 (6 ^ (2 * k) - 1) (fun t => gIdx (t + 1)) with
      | mk ra rb =>
        rw [hr] at heq_main
        simp only [z5Mul, z5Add, ZSqrt5.mk.injEq, Int.mul_zero, Int.zero_mul, Int.add_zero] at heq_main
        simp only [ZSqrt5.mk.injEq]
        refine ⟨?_, by omega⟩
        rw [Int.mul_sub]
        have h1 : (N : Int) * (40 ^ (2 * k) * 5 ^ k) = 40 ^ (2 * k) * ((N : Int) * 5 ^ k) := by ac_rfl
        omega
    rw [hdk] at hrem_nn h40pos
    rw [hsub] at hrem_nn
    dsimp [z5Nonneg] at hrem_nn
    have hnn_int : 0 ≤ 40 ^ (2 * k) * ((N : Int) * 5 ^ k - (N : Int) * N) := by
      rcases hrem_nn with ⟨h, _⟩ | ⟨h, _⟩ | ⟨ha, _, hsq⟩
      · exact h
      · exact h
      · exfalso
        have hpos := Int.mul_pos (by omega : 0 < -(40 ^ (2 * k) * ((N : Int) * 5 ^ k - (N : Int) * N)))
                                 (by omega : 0 < -(40 ^ (2 * k) * ((N : Int) * 5 ^ k - (N : Int) * N)))
        rw [Int.neg_mul_neg] at hpos
        omega
    have hNle : (N : Int) * N ≤ (N : Int) * 5 ^ k := by
      apply Classical.byContradiction; intro hlt
      have hneg := Int.mul_pos h40pos (by omega : 0 < (N : Int) * N - (N : Int) * 5 ^ k)
      rw [Int.mul_sub] at hneg hnn_int; omega
    -- `N * N ≤ N * 5^k` implies `N ≤ 5^k`, hence `N * N ≤ 5^(2*k)`!
    have hNle5k : N ≤ 5 ^ k := by
      by_cases hN0 : N = 0
      · subst hN0; exact Nat.zero_le _
      · have hNpos : (0 : Int) < (N : Int) := by omega
        apply Classical.byContradiction; intro hgt
        have h1 : ((5 ^ k : Nat) : Int) < (N : Int) := by exact_mod_cast (by omega : 5 ^ k < N)
        have hpow : ((5 ^ k : Nat) : Int) = (5 : Int) ^ k := nat_cast_pow 5 k
        rw [hpow] at h1
        have h2 := Int.mul_pos hNpos (by omega : 0 < (N : Int) - (5 : Int) ^ k)
        rw [Int.mul_sub] at h2; omega
    have hsq := Nat.mul_le_mul hNle5k hNle5k
    rw [← Nat.pow_add, show k + k = 2 * k by omega, ← hdk] at hsq
    exact hsq
  · let k := d / 2
    have hdk : d = 2 * k + 1 := by omega
    rw [hdk, z5Pow_40sqrt5_odd k] at heq_main
    have hsub : sumZ5 (6 ^ (2 * k + 1) - 1) (fun t => gIdx (t + 1)) =
        ⟨-(40 ^ (2 * k + 1) * ((N : Int) * N)), 40 ^ (2 * k + 1) * ((N : Int) * 5 ^ k)⟩ := by
      cases hr : sumZ5 (6 ^ (2 * k + 1) - 1) (fun t => gIdx (t + 1)) with
      | mk ra rb =>
        rw [hr] at heq_main
        simp only [z5Mul, z5Add, ZSqrt5.mk.injEq, Int.mul_zero, Int.zero_mul, Int.add_zero, Int.zero_add] at heq_main
        simp only [ZSqrt5.mk.injEq]
        refine ⟨by omega, ?_⟩
        have h1 : (N : Int) * (40 ^ (2 * k + 1) * 5 ^ k) = 40 ^ (2 * k + 1) * ((N : Int) * 5 ^ k) := by ac_rfl
        omega
    rw [hdk] at hrem_nn h40pos
    rw [hsub] at hrem_nn
    by_cases hN0 : N = 0
    · subst hN0; exact Nat.zero_le _
    · have hNpos : (0 : Int) < (N : Int) := by omega
      have hneg_a : -(40 ^ (2 * k + 1) * ((N : Int) * N)) < 0 := by
        have := Int.mul_pos h40pos (Int.mul_pos hNpos hNpos); omega
      dsimp [z5Nonneg] at hrem_nn
      have hsq : (-(40 ^ (2 * k + 1) * ((N : Int) * N))) * (-(40 ^ (2 * k + 1) * ((N : Int) * N))) ≤
                 5 * (40 ^ (2 * k + 1) * ((N : Int) * 5 ^ k)) * (40 ^ (2 * k + 1) * ((N : Int) * 5 ^ k)) := by
        rcases hrem_nn with ⟨ha, _⟩ | ⟨ha, _, _⟩ | ⟨_, _, hle⟩
        · omega
        · omega
        · exact hle
      rw [Int.neg_mul_neg] at hsq
      -- Cancel common positive factor `(40^(2k+1))^2 * N^2`!
      let C : Int := (40 ^ (2 * k + 1) * 40 ^ (2 * k + 1)) * ((N : Int) * N)
      have hCpos : 0 < C := Int.mul_pos (Int.mul_pos h40pos h40pos) (Int.mul_pos hNpos hNpos)
      have hl : (40 ^ (2 * k + 1) * ((N : Int) * N)) * (40 ^ (2 * k + 1) * ((N : Int) * N)) =
                C * ((N : Int) * N) := by dsimp [C]; ac_rfl
      have hr : 5 * (40 ^ (2 * k + 1) * ((N : Int) * 5 ^ k)) * (40 ^ (2 * k + 1) * ((N : Int) * 5 ^ k)) =
                C * (5 ^ (2 * k + 1)) := by
        dsimp [C]
        have h5 : (5 : Int) ^ (2 * k + 1) = 5 * (5 ^ k * 5 ^ k) := by
          rw [show 2 * k + 1 = k + k + 1 by omega, Int.pow_succ, Int.pow_add]; ac_rfl
        rw [h5]; ac_rfl
      rw [hl, hr] at hsq
      have hint_le : (N : Int) * N ≤ (5 : Int) ^ (2 * k + 1) := by
        apply Classical.byContradiction; intro hgt
        have hpos := Int.mul_pos hCpos (by omega : 0 < (N : Int) * N - (5 : Int) ^ (2 * k + 1))
        rw [Int.mul_sub] at hpos; omega
      have hpow5 : ((5 ^ (2 * k + 1) : Nat) : Int) = (5 : Int) ^ (2 * k + 1) := nat_cast_pow 5 (2 * k + 1)
      rw [← hpow5] at hint_le
      rw [hdk]
      exact_mod_cast hint_le

/-! ### 4. Haemers's 1979 Schläfli-Graph Shannon Super-Multiplicativity Paradox (T4d) -/

/-- Exact pair index `Fin 15 → Fin 6 × Fin 6` for the `c_{ij}` lines (`0 ≤ i < j < 6`). -/
def cPair : Nat → Nat × Nat
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (0, 3) | 3 => (0, 4) | 4 => (0, 5)
  | 5 => (1, 2) | 6 => (1, 3) | 7 => (1, 4) | 8 => (1, 5)
  | 9 => (2, 3) | 10 => (2, 4) | 11 => (2, 5)
  | 12 => (3, 4) | 13 => (3, 5)
  | _ => (4, 5)

/-- Intersection graph of the 27 lines on a cubic surface: `G₂₇ᶜ = SRG(27, 10, 1, 5)`. -/
def schlafliCompAdjB (u v : Fin 27) : Bool :=
  if u = v then false
  else if u.val < 6 then
    if v.val < 6 then false
    else if v.val < 12 then u.val != v.val - 6
    else let p := cPair (v.val - 12); u.val == p.1 || u.val == p.2
  else if u.val < 12 then
    if v.val < 6 then u.val - 6 != v.val
    else if v.val < 12 then false
    else let p := cPair (v.val - 12); u.val - 6 == p.1 || u.val - 6 == p.2
  else
    let pu := cPair (u.val - 12)
    if v.val < 6 then v.val == pu.1 || v.val == pu.2
    else if v.val < 12 then v.val - 6 == pu.1 || v.val - 6 == pu.2
    else
      let pv := cPair (v.val - 12)
      pu.1 != pv.1 && pu.1 != pv.2 && pu.2 != pv.1 && pu.2 != pv.2

theorem schlafliCompAdjB_symm (u v : Fin 27) :
    schlafliCompAdjB u v = schlafliCompAdjB v u := by
  revert u v; decide

theorem schlafliCompAdjB_irrefl (u : Fin 27) : schlafliCompAdjB u u = false := by
  revert u; decide

/-- The Schläfli complement `G₂₇ᶜ = SRG(27, 10, 1, 5)`. -/
def schlafliComp : FinGraph (Fin 27) where
  adj u v := schlafliCompAdjB u v = true
  symm := fun {u v} h => by rw [schlafliCompAdjB_symm]; exact h
  irrefl := fun {u} h => by rw [schlafliCompAdjB_irrefl] at h; exact Bool.noConfusion h

/-- The Schläfli graph `G₂₇ = SRG(27, 16, 10, 8)`. -/
def schlafliGraph : FinGraph (Fin 27) where
  adj u v := u ≠ v ∧ schlafliCompAdjB u v = false
  symm := fun {u v} ⟨hne, hf⟩ => ⟨hne.symm, by rw [schlafliCompAdjB_symm]; exact hf⟩
  irrefl := fun {u} ⟨hne, _⟩ => hne rfl

/-- Pure integer `ℤ⁸` Lovász orthogonal-handle representation of `G₂₇` (entries in `{-1, 0, 1, 2}`):
- `a_i`: `2 e_i + (0,0,0,0,0,0,2,0)`
- `b_i`: `2 e_i + (0,0,0,0,0,0,0,2)`
- `c_{ij}`: `∑_{k ∉ {i,j}} e_k - e_i - e_j + (0,0,0,0,0,0,1,1)`
Handle `h = (1,1,1,1,1,1,3,3)` satisfies `||h||² = 24`, `||w_v||² = 8`, `h · w_v = 8`,
`w_u · w_v = 0` on all non-edges of `G₂₇`, hence `H * D / s = 24 * 8 / 64 = 3`! -/
def schlafliVec (v : Fin 27) (k : Nat) : Int :=
  if v.val < 6 then
    if k < 6 then (if k = v.val then 2 else 0)
    else if k = 6 then 2 else 0
  else if v.val < 12 then
    if k < 6 then (if k = v.val - 6 then 2 else 0)
    else if k = 7 then 2 else 0
  else
    let p := cPair (v.val - 12)
    if k < 6 then (if k = p.1 ∨ k = p.2 then -1 else 1)
    else if k < 8 then 1 else 0

def schlafliHandle (k : Nat) : Int :=
  if k < 6 then 1 else if k < 8 then 3 else 0

theorem schlafliVec_norm (v : Fin 27) :
    sumInt 8 (fun k => schlafliVec v k * schlafliVec v k) = 8 := by
  revert v; decide

theorem schlafliHandle_norm :
    sumInt 8 (fun k => schlafliHandle k * schlafliHandle k) = 24 := by
  decide

theorem schlafliVec_handle_dot (v : Fin 27) :
    sumInt 8 (fun k => schlafliHandle k * schlafliVec v k) = 8 := by
  revert v; decide

theorem schlafliVec_orth (u v : Fin 27) :
    schlafliCompAdjB u v = true →
    sumInt 8 (fun k => schlafliVec u k * schlafliVec v k) = 0 := by
  revert u v; decide

/-- `α(G₂₇^{⊠ d}) ≤ 3^d` for all `d ≥ 1`, via T4b! -/
theorem schlafli_alpha_le_3_pow (d : Nat) :
    AlphaLe (strongPow schlafliGraph d) (3 ^ d) := by
  intro N hI
  have hbound := t4b_integer_orthogonal_handle_sandwich schlafliGraph 8 (by omega)
    schlafliVec schlafliHandle 8 24 64 (by omega) (by omega)
    schlafliVec_norm schlafliHandle_norm
    (fun v => by rw [schlafliVec_handle_dot v]; omega)
    (fun u v hnc => by
      have hcomp : schlafliCompAdjB u v = true := by
        apply Classical.byContradiction; intro hfalse
        have hf : schlafliCompAdjB u v = false := by cases h : schlafliCompAdjB u v <;> simp_all
        by_cases heq : u = v
        · exact hnc (Or.inl heq)
        · exact hnc (Or.inr ⟨heq, hf⟩)
      exact schlafliVec_orth u v hcomp)
    d N hI
  -- `(24 * 8)^d = 192^d = 3^d * 64^d`, cancel `64^d > 0`!
  have h192 : ((24 : Int) * 8) ^ d = (3 : Int) ^ d * (64 : Int) ^ d := by
    have : (24 : Int) * 8 = 3 * 64 := by omega
    rw [this]
    clear hbound hI
    induction d with
    | zero => rfl
    | succ k ih => rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ih]; ac_rfl
  rw [h192] at hbound
  have h64pos : (0 : Int) < (64 : Int) ^ d := by
    clear h192 hbound hI
    induction d with
    | zero => simp [Int.pow_zero]
    | succ k ih => rw [Int.pow_succ]; exact Int.mul_pos ih (by omega)
  have hNle : (N : Int) ≤ (3 : Int) ^ d := by
    apply Classical.byContradiction; intro hgt
    have hpos := Int.mul_pos (by omega : 0 < (N : Int) - (3 : Int) ^ d) h64pos
    rw [Int.sub_mul] at hpos; omega
  have hpow3 : ((3 ^ d : Nat) : Int) = (3 : Int) ^ d := nat_cast_pow 3 d
  rw [← hpow3] at hNle
  exact_mod_cast hNle

/-- Exact `27 × 7` `𝔽₂` factorization `I + A(G₂₇ᶜ) = L * R` (bit-packed rows for fast kernel check). -/
def schlafliLBits (u : Fin 27) : Nat :=
  match u.val with
  | 0 => 1   | 1 => 2   | 2 => 4   | 3 => 8   | 4 => 16  | 5 => 32
  | 6 => 62  | 7 => 61  | 8 => 59  | 9 => 55  | 10 => 47 | 11 => 31
  | 12 => 64 | 13 => 70 | 14 => 74 | 15 => 82 | 16 => 98
  | 17 => 69 | 18 => 73 | 19 => 81 | 20 => 97
  | 21 => 79 | 22 => 87 | 23 => 103
  | 24 => 91 | 25 => 107 | _ => 115

def schlafliRBits : Nat → Nat
  | 0 => 130945
  | 1 => 1974082
  | 2 => 14823108
  | 3 => 52710856
  | 4 => 88640464
  | 5 => 110168032
  | 6 => 132124867
  | _ => 0

def schlafliL (u : Fin 27) (k : Nat) : Bool := ((schlafliLBits u) >>> k) &&& 1 == 1
def schlafliR (k : Nat) (v : Fin 27) : Bool := ((schlafliRBits k) >>> v.val) &&& 1 == 1

theorem schlafli_f2_factor_exact (u v : Fin 27) :
    sumF 7 (fun k => SimpleField.mul (schlafliL u k) (schlafliR k v)) =
    ((u == v) || schlafliCompAdjB u v) := by
  revert u v; decide

/-- `α(G₂₇ᶜ^{⊠ d}) ≤ 7^d` for all `d ≥ 1`, via T4a over `𝔽₂`! -/
theorem schlafliComp_alpha_le_7_pow (d : Nat) :
    AlphaLe (strongPow schlafliComp d) (7 ^ d) := by
  apply t4a_haemers_rank_theorem (F := Bool) schlafliComp 7 (by omega) schlafliL schlafliR
  · intro v
    rw [schlafli_f2_factor_exact v v]
    simp [SimpleField.zero]
  · intro u v hnc
    rw [schlafli_f2_factor_exact u v]
    have hne : u ≠ v := fun h => hnc (Or.inl h)
    have hf : schlafliCompAdjB u v = false := by
      cases h : schlafliCompAdjB u v
      · rfl
      · exact absurd (Or.inr h) hnc
    simp [hne, hf, SimpleField.zero]

/-- Diagonal independent set of size `27` in `G₂₇ ⊠ G₂₇ᶜ`. -/
theorem schlafli_prod_lower_27 :
    HasIndepSetOfSize (strongProd schlafliGraph schlafliComp) 27 := by
  refine ⟨fun i => (i, i), ?_⟩
  intro i j hij hconf
  rw [conflict_strongProd_iff] at hconf
  rcases hconf.1 with heq | ⟨_, hf⟩
  · exact hij heq
  · rcases hconf.2 with heq | ht
    · exact hij heq
    · dsimp [schlafliComp] at ht; rw [hf] at ht; exact Bool.noConfusion ht

/-- **Theorem T4d (Haemers's 1979 Schläfli-Graph Shannon Super-Multiplicativity Paradox).** -/
theorem t4d_haemers_schlafli_paradox :
    (∀ d : Nat, AlphaLe (strongPow schlafliGraph d) (3 ^ d)) ∧
    (∀ d : Nat, AlphaLe (strongPow schlafliComp d) (7 ^ d)) ∧
    HasIndepSetOfSize (strongProd schlafliGraph schlafliComp) 27 ∧
    3 * 7 < 27 :=
  ⟨schlafli_alpha_le_3_pow, schlafliComp_alpha_le_7_pow, schlafli_prod_lower_27, by omega⟩

end
end ZeroErrorFrontier.HaemersParadox
