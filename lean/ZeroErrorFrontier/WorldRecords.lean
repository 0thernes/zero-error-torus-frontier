module
-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander Stephen Donahue

public import ZeroErrorFrontier.GraphCore
public import ZeroErrorFrontier.CosetQuotient
public import ZeroErrorFrontier.SeparationCalculus

/-!
# Pillar 2: Four Consecutive All-Time Odd-Cycle Shannon-Capacity World Records
# (`C₂₅`, `C₂₇`, `C₂₉`, `C₃₁`) — Pure Kernel, Zero `native_decide`, Zero `sorry`

Machine-checked lower bounds strictly surpassing the 55-year Baumert–Hales (`d = 3`)
records on four consecutive odd cycles:
- **T2a (`t2a_c25_world_record`):** `Θ(C₂₅) ≥ 12.344196091426841` (`p = 144`, `H*` 37-coset + 625 ports)
- **T2b (`t2b_c27_world_record`):** `Θ(C₂₇) ≥ 13.319390984674515` (`p = 2048`, Baumert `31,466` + 88 ports)
- **T2c (`t2c_c29_world_record`):** `Θ(C₂₉) ≥ 14.319949949077991` (`p = 4`, `H_BPZ` 50-coset `42,050`)
- **T2d (`t2d_c31_world_record`):** `Θ(C₃₁) ≥ 15.308776193986504` (`p = 2048`, Baumert `54,913` + 133 ports)

All 2,300+ digit inequalities are certified via exact 28-digit monotone lower/upper
bounding chains so every external proof kernel (`leanchecker`, `con-leche`, `con-ron`,
`nanoda_bin`) verifies the full theorem suite in seconds with zero `native_decide`.
-/

namespace ZeroErrorFrontier.WorldRecords

open ZeroErrorFrontier.GraphCore
open ZeroErrorFrontier.CosetQuotient
open ZeroErrorFrontier.SeparationCalculus

@[expose] public section

/-! ### 1. Strong-Power Flattening (`(G^{⊠ a})^{⊠ b} ≃ G^{⊠ (b * a)}`) -/

def flatPow {V : Type} (a b : Nat) (ha : 0 < a) (x : Fin b → Fin a → V) : Fin (b * a) → V :=
  fun k => x ⟨k.val / a, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm _ _))⟩
             ⟨k.val % a, Nat.mod_lt k.val ha⟩

theorem flatPow_conflict {V : Type} (G : FinGraph V) (a b : Nat) (ha : 0 < a)
    (x y : Fin b → Fin a → V)
    (hc : conflict (strongPow G (b * a)) (flatPow a b ha x) (flatPow a b ha y)) :
    conflict (strongPow (strongPow G a) b) x y := by
  rw [conflict_strongPow_iff] at hc ⊢
  intro r
  rw [conflict_strongPow_iff]
  intro s
  have hlt : r.val * a + s.val < b * a := by
    have h1 : (r.val + 1) * a ≤ b * a := Nat.mul_le_mul_right a (Nat.succ_le_of_lt r.isLt)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  have hk := hc ⟨r.val * a + s.val, hlt⟩
  dsimp [flatPow] at hk
  have hdiv : (r.val * a + s.val) / a = r.val := by
    rw [Nat.mul_comm r.val a, Nat.mul_add_div ha, Nat.div_eq_of_lt s.isLt, Nat.add_zero]
  have hmod : (r.val * a + s.val) % a = s.val := by
    rw [Nat.mul_comm r.val a, Nat.mul_add_mod, Nat.mod_eq_of_lt s.isLt]
  have hr : (⟨(r.val * a + s.val) / a, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq hlt (Nat.mul_comm _ _))⟩ : Fin b) = r :=
    Fin.ext hdiv
  have hs : (⟨(r.val * a + s.val) % a, Nat.mod_lt _ ha⟩ : Fin a) = s := Fin.ext hmod
  rw [hr, hs] at hk
  exact hk

def repackSep {Sym V : Type} {sep : Sym → Sym → Bool} {G : FinGraph V} {a b : Nat} (ha : 0 < a)
    (R : SepRealisation Sym sep (strongPow (strongPow G a) b)) :
    SepRealisation Sym sep (strongPow G (b * a)) where
  sz := R.sz
  emb c i := flatPow a b ha (R.emb c i)
  indep c i j hij hc := R.indep c i j hij (flatPow_conflict G a b ha _ _ hc)
  sep_ok c₁ c₂ hsep i j hc := R.sep_ok c₁ c₂ hsep i j (flatPow_conflict G a b ha _ _ hc)

theorem hasIndepSet_repackPow {V : Type} (G : FinGraph V) (a b N : Nat) (ha : 0 < a)
    (h : HasIndepSetOfSize (strongPow (strongPow G a) b) N) :
    HasIndepSetOfSize (strongPow G (b * a)) N := by
  rcases h with ⟨f, hf⟩
  exact ⟨fun i => flatPow a b ha (f i), fun i j hij hc => hf i j hij (flatPow_conflict G a b ha _ _ hc)⟩

/-! ### 2. Monotone 28-Digit Lower-Bound & Power-Certification Engine -/

theorem tupleSz_mono {Sym : Type} (w₁ w₂ : Sym → Nat) (hle : ∀ c, w₁ c ≤ w₂ c) :
    ∀ (m : Nat) (u : Fin m → Sym), tupleSz w₁ m u ≤ tupleSz w₂ m u
  | 0, _ => Nat.le_refl 1
  | m + 1, u => Nat.mul_le_mul (tupleSz_mono w₁ w₂ hle m (fun i => u i.castSucc)) (hle (u (Fin.last m)))

theorem tupleSz_scale {Sym : Type} (w : Sym → Nat) (S : Nat) :
    ∀ (m : Nat) (u : Fin m → Sym), tupleSz (fun c => w c * S) m u = tupleSz w m u * S ^ m
  | 0, _ => by simp [tupleSz]
  | m + 1, u => by
    simp only [tupleSz, tupleSz_scale w S m (fun i => u i.castSucc), Nat.pow_succ]
    ac_rfl

theorem sumListSizes_mono {α : Type} (L : List α) (f g : α → Nat) (hle : ∀ x, f x ≤ g x) :
    sumListSizes L f ≤ sumListSizes L g := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons a tl ih => simp only [sumListSizes]; exact Nat.add_le_add (hle a) ih

theorem sumListSizes_scale {α : Type} (L : List α) (f : α → Nat) (S : Nat) :
    sumListSizes L (fun x => f x * S) = sumListSizes L f * S := by
  induction L with
  | nil => simp [sumListSizes]
  | cons a tl ih => simp only [sumListSizes, ih, Nat.add_mul]

theorem stepLo_tbl {m : Nat} (T : Letter → List (Fin m → Letter))
    (lo lo' w : Letter → Nat) (e sh e' : Nat) (he' : e' = m * e + sh)
    (hlo : ∀ c, lo c * 10 ^ e ≤ w c)
    (hstep : ∀ c, lo' c * 10 ^ sh ≤ sumListSizes (T c) (tupleSz lo m)) :
    ∀ c, lo' c * 10 ^ e' ≤ sumListSizes (T c) (tupleSz w m) := by
  subst he'
  intro c
  have h1 : lo' c * 10 ^ (m * e + sh) = (lo' c * 10 ^ sh) * (10 ^ e) ^ m := by
    rw [Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm e m]; ac_rfl
  rw [h1]
  have h2 : (lo' c * 10 ^ sh) * (10 ^ e) ^ m ≤ sumListSizes (T c) (tupleSz lo m) * (10 ^ e) ^ m :=
    Nat.mul_le_mul_right _ (hstep c)
  have h3 : sumListSizes (T c) (tupleSz lo m) * (10 ^ e) ^ m =
            sumListSizes (T c) (tupleSz (fun a => lo a * 10 ^ e) m) := by
    rw [← sumListSizes_scale]
    congr 1; funext u; exact (tupleSz_scale lo (10 ^ e) m u).symm
  have h4 : sumListSizes (T c) (tupleSz (fun a => lo a * 10 ^ e) m) ≤ sumListSizes (T c) (tupleSz w m) :=
    sumListSizes_mono (T c) _ _ (fun u => tupleSz_mono _ w hlo m u)
  rw [h3] at h2
  exact Nat.le_trans h2 h4

theorem stepFinal_code (C : List (Fin 4 → Letter)) (lo w : Letter → Nat) (e e4 : Nat) (he4 : e4 = 4 * e)
    (hlo : ∀ c, lo c * 10 ^ e ≤ w c) :
    sumListSizes C (tupleSz lo 4) * 10 ^ e4 ≤ sumListSizes C (tupleSz w 4) := by
  subst he4
  have h1 : sumListSizes C (tupleSz lo 4) * 10 ^ (4 * e) =
            sumListSizes C (tupleSz (fun a => lo a * 10 ^ e) 4) := by
    rw [Nat.mul_comm 4 e, Nat.pow_mul, ← sumListSizes_scale]
    congr 1; funext u; exact (tupleSz_scale lo (10 ^ e) 4 u).symm
  rw [h1]
  exact sumListSizes_mono C _ _ (fun u => tupleSz_mono _ w hlo 4 u)

/-- Scaled upper-bound invariant: `a^p * 10^25 ≤ U * 10^e * D^p`. -/
def PowLe (a D p U e : Nat) : Prop :=
  a ^ p * 10 ^ 25 ≤ U * 10 ^ e * D ^ p

theorem pow10_pos (k : Nat) : 0 < 10 ^ k := by
  induction k with
  | zero => decide
  | succ s ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih (by omega)

theorem powLe_base (target : Nat) :
    PowLe target (10 ^ 15) 1 (target * 10 ^ 10) 0 := by
  unfold PowLe
  rw [Nat.pow_one, Nat.pow_one, Nat.pow_zero, Nat.mul_one, Nat.mul_assoc, ← Nat.pow_add]
  exact Nat.le_refl _

theorem powLe_sq {a D p U e U' sh : Nat} (h : PowLe a D p U e) (hsh : 25 ≤ sh)
    (hU : U * U ≤ U' * 10 ^ sh) :
    PowLe a D (2 * p) U' (2 * e + sh - 25) := by
  unfold PowLe at h ⊢
  have hsq := Nat.mul_le_mul h h
  have hl : (a ^ p * 10 ^ 25) * (a ^ p * 10 ^ 25) = (a ^ (2 * p) * 10 ^ 25) * 10 ^ 25 := by
    have h2p : a ^ (2 * p) = a ^ p * a ^ p := by rw [show 2 * p = p + p by omega, Nat.pow_add]
    rw [h2p]; ac_rfl
  have hr1 : (U * 10 ^ e * D ^ p) * (U * 10 ^ e * D ^ p) =
             (U * U) * (10 ^ (2 * e) * D ^ (2 * p)) := by
    have h2e : 10 ^ (2 * e) = 10 ^ e * 10 ^ e := by rw [show 2 * e = e + e by omega, Nat.pow_add]
    have h2d : D ^ (2 * p) = D ^ p * D ^ p := by rw [show 2 * p = p + p by omega, Nat.pow_add]
    rw [h2e, h2d]; ac_rfl
  have hr2 : (U * U) * (10 ^ (2 * e) * D ^ (2 * p)) ≤
             (U' * 10 ^ sh) * (10 ^ (2 * e) * D ^ (2 * p)) := Nat.mul_le_mul_right _ hU
  have hr3 : (U' * 10 ^ sh) * (10 ^ (2 * e) * D ^ (2 * p)) =
             (U' * 10 ^ (2 * e + sh - 25) * D ^ (2 * p)) * 10 ^ 25 := by
    have hsum : 10 ^ (2 * e + sh - 25) * 10 ^ 25 = 10 ^ sh * 10 ^ (2 * e) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    calc (U' * 10 ^ sh) * (10 ^ (2 * e) * D ^ (2 * p))
        = U' * (10 ^ sh * 10 ^ (2 * e)) * D ^ (2 * p) := by ac_rfl
      _ = U' * (10 ^ (2 * e + sh - 25) * 10 ^ 25) * D ^ (2 * p) := by rw [← hsum]
      _ = (U' * 10 ^ (2 * e + sh - 25) * D ^ (2 * p)) * 10 ^ 25 := by ac_rfl
  rw [hl, hr1] at hsq
  have hcomb := Nat.le_trans hsq (hr3 ▸ hr2)
  exact Nat.le_of_mul_le_mul_right hcomb (pow10_pos 25)

theorem powLe_cube {a D p U e U' sh : Nat} (h : PowLe a D p U e) (hsh : 50 ≤ sh)
    (hU : U * U * U ≤ U' * 10 ^ sh) :
    PowLe a D (3 * p) U' (3 * e + sh - 50) := by
  unfold PowLe at h ⊢
  have hcu := Nat.mul_le_mul (Nat.mul_le_mul h h) h
  have hl : (a ^ p * 10 ^ 25) * (a ^ p * 10 ^ 25) * (a ^ p * 10 ^ 25) =
            (a ^ (3 * p) * 10 ^ 25) * 10 ^ 50 := by
    have h3p : a ^ (3 * p) = a ^ p * a ^ p * a ^ p := by
      rw [show 3 * p = p + p + p by omega, Nat.pow_add, Nat.pow_add]
    have h50 : 10 ^ 25 * 10 ^ 25 = 10 ^ 50 := by rw [← Nat.pow_add]
    rw [h3p]; calc (a ^ p * 10 ^ 25) * (a ^ p * 10 ^ 25) * (a ^ p * 10 ^ 25)
        = (a ^ p * a ^ p * a ^ p * 10 ^ 25) * (10 ^ 25 * 10 ^ 25) := by ac_rfl
      _ = (a ^ p * a ^ p * a ^ p * 10 ^ 25) * 10 ^ 50 := by rw [h50]
  have hr1 : (U * 10 ^ e * D ^ p) * (U * 10 ^ e * D ^ p) * (U * 10 ^ e * D ^ p) =
             (U * U * U) * (10 ^ (3 * e) * D ^ (3 * p)) := by
    have h3e : 10 ^ (3 * e) = 10 ^ e * 10 ^ e * 10 ^ e := by
      rw [show 3 * e = e + e + e by omega, Nat.pow_add, Nat.pow_add]
    have h3d : D ^ (3 * p) = D ^ p * D ^ p * D ^ p := by
      rw [show 3 * p = p + p + p by omega, Nat.pow_add, Nat.pow_add]
    rw [h3e, h3d]; ac_rfl
  have hr2 : (U * U * U) * (10 ^ (3 * e) * D ^ (3 * p)) ≤
             (U' * 10 ^ sh) * (10 ^ (3 * e) * D ^ (3 * p)) := Nat.mul_le_mul_right _ hU
  have hr3 : (U' * 10 ^ sh) * (10 ^ (3 * e) * D ^ (3 * p)) =
             (U' * 10 ^ (3 * e + sh - 50) * D ^ (3 * p)) * 10 ^ 50 := by
    have hsum : 10 ^ (3 * e + sh - 50) * 10 ^ 50 = 10 ^ sh * 10 ^ (3 * e) := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    calc (U' * 10 ^ sh) * (10 ^ (3 * e) * D ^ (3 * p))
        = U' * (10 ^ sh * 10 ^ (3 * e)) * D ^ (3 * p) := by ac_rfl
      _ = U' * (10 ^ (3 * e + sh - 50) * 10 ^ 50) * D ^ (3 * p) := by rw [← hsum]
      _ = (U' * 10 ^ (3 * e + sh - 50) * D ^ (3 * p)) * 10 ^ 50 := by ac_rfl
  rw [hl, hr1] at hcu
  have hcomb := Nat.le_trans hcu (hr3 ▸ hr2)
  exact Nat.le_of_mul_le_mul_right hcomb (pow10_pos 50)

theorem powLe_cast_p {a D p p' U e : Nat} (hp : p = p') (h : PowLe a D p U e) :
    PowLe a D p' U e := hp ▸ h

theorem powLe_finish {a D p U e raw exp10 M : Nat}
    (hU : PowLe a D p U e) (hM : raw * 10 ^ exp10 ≤ M)
    (he : exp10 + 25 ≤ e) (hcmp : U * 10 ^ (e - (exp10 + 25)) ≤ raw) :
    a ^ p ≤ M * D ^ p := by
  unfold PowLe at hU
  have h1 : U * 10 ^ e ≤ raw * 10 ^ (exp10 + 25) := by
    have hpow : 10 ^ e = 10 ^ (e - (exp10 + 25)) * 10 ^ (exp10 + 25) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [hpow, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hcmp
  have h2 : raw * 10 ^ (exp10 + 25) ≤ M * 10 ^ 25 := by
    rw [Nat.pow_add, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hM
  have h3 : a ^ p * 10 ^ 25 ≤ (M * D ^ p) * 10 ^ 25 := by
    have hcomb := Nat.le_trans hU (Nat.mul_le_mul_right (D ^ p) (Nat.le_trans h1 h2))
    have hrr : M * 10 ^ 25 * D ^ p = (M * D ^ p) * 10 ^ 25 := by ac_rfl
    rw [hrr] at hcomb
    exact hcomb
  exact Nat.le_of_mul_le_mul_right h3 (pow10_pos 25)

/-! ### 3. Universal `H*`-Invariant `n²`-Port System & `C₂₅` World Record (T2a) -/

theorem cycDist_shift_eq (n a b s : Nat) (ha : a < n) (hb : b < n) (hn : 0 < n) :
    cycDist n ((a + s) % n) ((b + s) % n) = cycDist n a b := by
  have hle : ∀ (x y c : Nat), x < n → y < n → cycDist n ((x + c) % n) ((y + c) % n) ≤ cycDist n x y := by
    intro x y c hx hy
    by_cases hfull : n ≤ cycDist n x y
    · have hbd : cycDist n ((x + c) % n) ((y + c) % n) < n := by
        unfold cycDist
        exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.mod_lt _ hn)
      omega
    · rcases cycDist_signed_delta n x y (cycDist n x y) hx hy (Nat.le_refl _) with ⟨δ, q, h1, h2, heq⟩
      rcases int_mod_decomp (x + c) n hn with ⟨kx, hkx⟩
      rcases int_mod_decomp (y + c) n hn with ⟨ky, hky⟩
      have hd : (((x + c) % n : Nat) : Int) - (((y + c) % n : Nat) : Int) = (q + ky - kx) * (n : Int) + δ := by
        have hm : (q + ky - kx) * (n : Int) = q * n + ky * n - kx * n := by rw [Int.sub_mul, Int.add_mul]
        omega
      exact cycDist_of_signed_delta n _ _ (cycDist n x y) (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
        (by omega) δ (q + ky - kx) h1 h2 hd
  have hdir1 := hle a b s ha hb
  have hback : ∀ z : Nat, z < n → ((z + s) % n + (n - s % n)) % n = z := by
    intro z hz
    rw [Nat.mod_add_mod]
    have hsum : z + s + (n - s % n) = z + (s / n + 1) * n := by
      have hsm := Nat.div_add_mod s n
      have hml := Nat.mod_lt s hn
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (s / n) n]; omega
    rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
  have hdir2 := hle ((a + s) % n) ((b + s) % n) (n - s % n) (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
  rw [hback a ha, hback b hb] at hdir2
  omega

/-- Lift a quotient family `Q : Fin K → Fin n × Fin n` under `H*` (`n ≥ 15`) to `K * (n * n)` vertices. -/
def liftHStarFamily (n K : Nat) (hn : 0 < n) (Q : Fin K → Fin n × Fin n) (idx : Fin (K * (n * n))) :
    Fin 4 → Fin n :=
  have hn2 : 0 < n * n := Nat.mul_pos hn hn
  let qIdx : Fin K := ⟨idx.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (Nat.mul_comm _ _))⟩
  let rem := idx.val % (n * n)
  let u : Fin n := ⟨rem / n, Nat.div_lt_of_lt_mul (Nat.mod_lt idx.val hn2)⟩
  let v : Fin n := ⟨rem % n, Nat.mod_lt rem hn⟩
  liftHStar n hn (Q qIdx) u v

theorem liftHStarFamily_indep {n K : Nat} (hn : 15 ≤ n) (Q : Fin K → Fin n × Fin n)
    (hQ : ∀ i j : Fin K, i ≠ j → ¬ conflict (qGraphHStar n) (Q i) (Q j)) :
    ∀ i j : Fin (K * (n * n)), i ≠ j →
      ¬ conflict (strongPow (cycleGraph n) 4)
          (liftHStarFamily n K (by omega) Q i) (liftHStarFamily n K (by omega) Q j) := by
  intro i j hij hconf
  have hres := liftHStar_conflict_implies_quot hn _ _ _ _ _ _ hconf
  have hqeq : (⟨i.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm _ _))⟩ : Fin K) =
              ⟨j.val / (n * n), Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq j.isLt (Nat.mul_comm _ _))⟩ := by
    apply Classical.byContradiction; intro hne; exact hQ _ _ hne hres.1
  have ⟨hu, hv⟩ := hres.2 (congrArg Q hqeq)
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

theorem liftHStarFamily_cross {n K₁ K₂ : Nat} (hn : 15 ≤ n)
    (Q₁ : Fin K₁ → Fin n × Fin n) (Q₂ : Fin K₂ → Fin n × Fin n)
    (hcross : ∀ a b, ¬ conflict (qGraphHStar n) (Q₁ a) (Q₂ b)) :
    ∀ (i : Fin (K₁ * (n * n))) (j : Fin (K₂ * (n * n))),
      ¬ conflict (strongPow (cycleGraph n) 4)
          (liftHStarFamily n K₁ (by omega) Q₁ i) (liftHStarFamily n K₂ (by omega) Q₂ j) := by
  intro i j hconf
  exact hcross _ _ (liftHStar_conflict_implies_quot hn _ _ _ _ _ _ hconf).1

/-- Universal `H*`-invariant `n²`-port `RichPortSystem` for EVERY odd `k ≥ 3` (`n = 8k + 1`,
`C₂₅, C₄₁, C₅₇, ...`), lifting `t1e_infinite_hstar_family_and_ports` with ZERO computation! -/
def hstarOddRichPortSystem (k : Nat) (hk : 3 ≤ k) (hodd : k % 2 = 1) :
    RichPortSystem (strongPow (cycleGraph (8 * k + 1)) 4) :=
  let n := 8 * k + 1
  let M := hstarM k
  let dIdx := 4 * k * k - (k / 2 + 1)
  have hn15 : 15 ≤ n := by dsimp [n]; omega
  have hnpos : 0 < n := by omega
  have hkk : 9 ≤ k * k := Nat.mul_le_mul hk hk
  have h4kk : 4 * k * k = 4 * (k * k) := Nat.mul_assoc 4 k k
  have hk_le_kk : k ≤ k * k := by
    have := Nat.mul_le_mul_left k (show 1 ≤ k by omega); simpa using this
  have hM_ge3 : 3 ≤ M := by dsimp [M, hstarM]; rw [h4kk]; omega
  have hdIdx_lt : dIdx < M := by dsimp [dIdx, M, hstarM]; rw [h4kk]; omega
  have hdIdx_pos : 0 < dIdx := by dsimp [dIdx]; rw [h4kk]; omega
  let p0 : Fin n × Fin n := (⟨0, hnpos⟩, ⟨0, hnpos⟩)
  let p1 : Fin n × Fin n := (⟨n - 1, by omega⟩, ⟨0, hnpos⟩)
  let Xq : Fin M → Fin n × Fin n := fun t =>
    let pt := hstarPt k hk t
    (⟨(pt.1.val + 1) % n, Nat.mod_lt _ hnpos⟩,
     ⟨(pt.2.val + n - 1) % n, Nat.mod_lt _ hnpos⟩)
  have hport := (t1e_infinite_hstar_family_and_ports k hk).2.2.2 hodd
  have hp0_eq : hstarPt k hk ⟨0, by omega⟩ = p0 := hport.1
  have hp1_priv : ∀ t : Fin M, conflict (qGraphHStar n) p1 (hstarPt k hk t) ↔ t.val = 0 := hport.2.1
  have hA_foot : ∀ t : Fin M, conflict (qGraphHStar n) p0 (Xq t) ↔ t.val = 0 := hport.2.2.1
  have hD_foot : ∀ t : Fin M, conflict (qGraphHStar n) p1 (Xq t) ↔ t.val = dIdx := hport.2.2.2.1
  have hX_indep : ∀ t₁ t₂ : Fin M, t₁ ≠ t₂ → ¬ conflict (qGraphHStar n) (Xq t₁) (Xq t₂) := by
    intro t₁ t₂ hne hc
    rw [qGraphHStar, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff] at hc
    dsimp [Xq] at hc
    have h1 := cycDist_shift_eq n (hstarPt k hk t₁).1.val (hstarPt k hk t₂).1.val 1
      (hstarPt k hk t₁).1.isLt (hstarPt k hk t₂).1.isLt hnpos
    have h2 : cycDist n (((hstarPt k hk t₁).2.val + n - 1) % n) (((hstarPt k hk t₂).2.val + n - 1) % n) =
              cycDist n (hstarPt k hk t₁).2.val (hstarPt k hk t₂).2.val := by
      have ha : (hstarPt k hk t₁).2.val + n - 1 = (hstarPt k hk t₁).2.val + (n - 1) := by omega
      have hb : (hstarPt k hk t₂).2.val + n - 1 = (hstarPt k hk t₂).2.val + (n - 1) := by omega
      rw [ha, hb]
      exact cycDist_shift_eq n _ _ (n - 1) (hstarPt k hk t₁).2.isLt (hstarPt k hk t₂).2.isLt hnpos
    rw [h1] at hc; rw [h2] at hc
    exact hstarPt_indep k hk t₁ t₂ hne (by
      rw [qGraphHStar, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff]; exact hc)
  let idxB : Fin (M - 1) → Fin M := fun r => ⟨r.val + 1, by omega⟩
  let idxN : Fin (M - 2) → Fin M := fun r =>
    if h : r.val + 1 < dIdx then ⟨r.val + 1, by omega⟩ else ⟨r.val + 2, by omega⟩
  have hidxB_inj : ∀ a b : Fin (M - 1), idxB a = idxB b → a = b := by
    intro a b heq; apply Fin.ext; have := congrArg Fin.val heq; dsimp [idxB] at this; omega
  have hidxN_inj : ∀ a b : Fin (M - 2), idxN a = idxN b → a = b := by
    intro a b heq; apply Fin.ext; have hv := congrArg Fin.val heq; dsimp [idxN] at hv
    split at hv <;> split at hv <;> simp at hv <;> omega
  have hidxN_ne0 : ∀ r : Fin (M - 2), (idxN r).val ≠ 0 := by
    intro r; dsimp [idxN]; split <;> dsimp <;> omega
  have hidxN_neD : ∀ r : Fin (M - 2), (idxN r).val ≠ dIdx := by
    intro r; dsimp [idxN]; split <;> dsimp <;> omega
  let qB : Fin (M - 1) → Fin n × Fin n := fun r => hstarPt k hk (idxB r)
  let qN : Fin (M - 2) → Fin n × Fin n := fun r => Xq (idxN r)
  let qA : Fin 1 → Fin n × Fin n := fun _ => Xq ⟨0, by omega⟩
  let qD : Fin 1 → Fin n × Fin n := fun _ => Xq ⟨dIdx, hdIdx_lt⟩
  let qO : Fin 1 → Fin n × Fin n := fun _ => p0
  let qH : Fin 1 → Fin n × Fin n := fun _ => p1
  have hsing_indep : ∀ (q : Fin 1 → Fin n × Fin n) (i j : Fin 1), i ≠ j → ¬ conflict (qGraphHStar n) (q i) (q j) := by
    intro _ i j hij; exact False.elim (hij (Fin.ext (by omega)))
  { nB := (M - 1) * (n * n)
    nN := (M - 2) * (n * n)
    nA := 1 * (n * n)
    nD := 1 * (n * n)
    d  := 1 * (n * n)
    embB := liftHStarFamily n (M - 1) hnpos qB
    embN := liftHStarFamily n (M - 2) hnpos qN
    embA := liftHStarFamily n 1 hnpos qA
    embD := liftHStarFamily n 1 hnpos qD
    embO := liftHStarFamily n 1 hnpos qO
    embH := liftHStarFamily n 1 hnpos qH
    embV := liftHStarFamily n 1 hnpos qO
    hB_indep := liftHStarFamily_indep hn15 qB (fun a b hab =>
      hstarPt_indep k hk (idxB a) (idxB b) (fun h => hab (hidxB_inj a b h)))
    hN_indep := liftHStarFamily_indep hn15 qN (fun a b hab =>
      hX_indep (idxN a) (idxN b) (fun h => hab (hidxN_inj a b h)))
    hA_indep := liftHStarFamily_indep hn15 qA (hsing_indep qA)
    hD_indep := liftHStarFamily_indep hn15 qD (hsing_indep qD)
    hO_indep := liftHStarFamily_indep hn15 qO (hsing_indep qO)
    hH_indep := liftHStarFamily_indep hn15 qH (hsing_indep qH)
    hV_indep := liftHStarFamily_indep hn15 qO (hsing_indep qO)
    hBO := liftHStarFamily_cross hn15 qB qO (fun a _ hc => by
      dsimp [qB, qO] at hc; rw [← hp0_eq] at hc
      exact hstarPt_indep k hk (idxB a) ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; dsimp [idxB] at this; omega) hc)
    hBH := liftHStarFamily_cross hn15 qB qH (fun a _ hc => by
      dsimp [qB, qH] at hc
      have h0 := (hp1_priv (idxB a)).mp (conflict_symm _ hc)
      dsimp [idxB] at h0; omega)
    hBV := liftHStarFamily_cross hn15 qB qO (fun a _ hc => by
      dsimp [qB, qO] at hc; rw [← hp0_eq] at hc
      exact hstarPt_indep k hk (idxB a) ⟨0, by omega⟩ (fun h => by have := congrArg Fin.val h; dsimp [idxB] at this; omega) hc)
    hNA := liftHStarFamily_cross hn15 qN qA (fun a _ hc =>
      hX_indep (idxN a) ⟨0, by omega⟩ (fun h => hidxN_ne0 a (congrArg Fin.val h)) hc)
    hND := liftHStarFamily_cross hn15 qN qD (fun a _ hc =>
      hX_indep (idxN a) ⟨dIdx, hdIdx_lt⟩ (fun h => hidxN_neD a (congrArg Fin.val h)) hc)
    hNO := liftHStarFamily_cross hn15 qN qO (fun a _ hc =>
      hidxN_ne0 a ((hA_foot (idxN a)).mp (conflict_symm _ hc)))
    hNH := liftHStarFamily_cross hn15 qN qH (fun a _ hc =>
      hidxN_neD a ((hD_foot (idxN a)).mp (conflict_symm _ hc)))
    hNV := liftHStarFamily_cross hn15 qN qO (fun a _ hc =>
      hidxN_ne0 a ((hA_foot (idxN a)).mp (conflict_symm _ hc)))
    hAD := liftHStarFamily_cross hn15 qA qD (fun _ _ hc =>
      hX_indep ⟨0, by omega⟩ ⟨dIdx, hdIdx_lt⟩ (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega) hc)
    hAH := liftHStarFamily_cross hn15 qA qH (fun _ _ hc => by
      have h0 := (hD_foot ⟨0, by omega⟩).mp (conflict_symm _ hc); dsimp at h0; omega)
    hDV := liftHStarFamily_cross hn15 qD qO (fun _ _ hc => by
      have h0 := (hA_foot ⟨dIdx, hdIdx_lt⟩).mp (conflict_symm _ hc); dsimp at h0; omega) }

theorem hstarOddRichPortSystem_sz (k : Nat) (hk : 3 ≤ k) (hodd : k % 2 = 1) (c : Letter) :
    (hstarOddRichPortSystem k hk hodd).toSepRealisation.sz c =
    match c with
    | .B => (hstarM k - 1) * ((8 * k + 1) * (8 * k + 1))
    | .N => (hstarM k - 2) * ((8 * k + 1) * (8 * k + 1))
    | .A => 1 * ((8 * k + 1) * (8 * k + 1))
    | .D => 1 * ((8 * k + 1) * (8 * k + 1))
    | .O => 1 * ((8 * k + 1) * (8 * k + 1))
    | .H => 1 * ((8 * k + 1) * (8 * k + 1))
    | .V => 1 * ((8 * k + 1) * (8 * k + 1)) := by
  cases c <;> rfl

/-! #### 28-Digit Monotone Certificate for `C₂₅` (`p = 144`) -/

def lo_c25_0 : Letter → Nat
  | .B => 22500 | .N => 21875 | .A => 625 | .D => 625
  | .O => 625 | .H => 625 | .V => 625

def lo_c25_1 : Letter → Nat
  | .B => 11444091796875 | .N => 10495361328125 | .A => 974365234375 | .D => 897216796875
  | .O => 0 | .H => 922851562500 | .V => 948486328125

def lo_c25_2 : Letter → Nat
  | .B => 1594009899344091536477208137 | .N => 1239317665561276953667402267
  | .A => 343791798789505264721810817  | .D => 308810324221121845766901969
  | .O => 0 | .H => 317408237342024222016334533 | .V => 335146765842073364183306694

/-- **Theorem T2a (`C₂₅` World Record: `Θ(C₂₅) ≥ 12.344196091426841`).** -/
theorem t2a_c25_world_record :
    ∃ M : Nat, HasIndepSetOfSize (strongPow (cycleGraph 25) 144) M ∧
      12344196091426841 ^ 144 ≤ M * (10 ^ 15) ^ 144 := by
  let R0 := (hstarOddRichPortSystem 3 (by omega) (by omega)).toSepRealisation
  let R1 := repackSep (a := 4) (b := 3) (by omega) (liftT3c R0)
  let R2 := repackSep (a := 12) (b := 3) (by omega) (liftT3e R1)
  have hM : HasIndepSetOfSize (strongPow (cycleGraph 25) 144) (sumListSizes codeC4b (tupleSz R2.sz 4)) :=
    hasIndepSet_repackPow (cycleGraph 25) 36 4 _ (by omega) (liftC4b R2)
  have h0 : ∀ c, lo_c25_0 c * 10 ^ 0 ≤ R0.sz c := by
    intro c; dsimp only [R0]; rw [hstarOddRichPortSystem_sz]; cases c <;> decide
  have h1 : ∀ c, lo_c25_1 c * 10 ^ 0 ≤ R1.sz c :=
    stepLo_tbl tblT3c lo_c25_0 lo_c25_1 R0.sz 0 0 0 (by decide) h0 (by intro c; cases c <;> decide)
  have h2 : ∀ c, lo_c25_2 c * 10 ^ 12 ≤ R2.sz c :=
    stepLo_tbl tblT3e lo_c25_1 lo_c25_2 R1.sz 0 12 12 (by decide) h1 (by intro c; cases c <;> decide)
  have hM_lo : sumListSizes codeC4b (tupleSz lo_c25_2 4) * 10 ^ 48 ≤ sumListSizes codeC4b (tupleSz R2.sz 4) :=
    stepFinal_code codeC4b lo_c25_2 R2.sz 12 48 (by decide) h2
  have hu0 := powLe_base 12344196091426841
  have hu1 := powLe_sq hu0 (sh := 25) (by decide) (U' := 1523791771435976982885392553) (by decide)
  have hu2 := powLe_sq hu1 (sh := 27) (by decide) (U' := 2321941362695992718922413947) (by decide)
  have hu3 := powLe_sq hu2 (sh := 27) (by decide) (U' := 5391411691798523607917991890) (by decide)
  have hu4 := powLe_sq hu3 (sh := 28) (by decide) (U' := 2906732003046181851217476325) (by decide)
  have hu5 := powLe_cube hu4 (sh := 55) (by decide) (U' := 2455924302477425750667937738) (by decide)
  have hu6 := powLe_cube hu5 (sh := 55) (by decide) (U' := 1481306505038447372197944756) (by decide)
  exact ⟨sumListSizes codeC4b (tupleSz R2.sz 4), hM,
    powLe_finish hu6 hM_lo (by decide) (by decide)⟩

/-! ### 4. `C₂₉` World Record (T2c: 50-Coset `H_BPZ`, `42,050` Words, `Θ(C₂₉) ≥ 14.319949949077991`) -/

def q29HBPZ : List (Nat × Nat) :=
  [(0, 0), (0, 21), (0, 25), (1, 17), (2, 13), (3, 5), (3, 9), (4, 1), (4, 21), (4, 25),
   (5, 17), (6, 13), (7, 5), (7, 9), (8, 1), (8, 22), (8, 26), (9, 18), (10, 14), (11, 6),
   (11, 10), (12, 2), (12, 23), (12, 27), (13, 19), (14, 15), (15, 10), (16, 2), (16, 6),
   (16, 23), (16, 27), (17, 19), (18, 15), (19, 11), (20, 3), (20, 7), (20, 24), (20, 28),
   (21, 20), (22, 15), (23, 11), (24, 3), (24, 7), (24, 24), (24, 28), (25, 20), (26, 16),
   (27, 12), (28, 4), (28, 8)]

def q25HBPZ : List (Nat × Nat) :=
  [(0, 14), (1, 19), (2, 2), (2, 6), (2, 23), (3, 10), (4, 14), (5, 18), (6, 2), (6, 23),
   (7, 6), (7, 10), (8, 14), (9, 18), (10, 22), (11, 1), (11, 5), (11, 9), (12, 13), (13, 17),
   (14, 21), (15, 0), (15, 4), (15, 8), (16, 12), (17, 16), (18, 20), (19, 3), (19, 7), (19, 24),
   (20, 11), (21, 15), (22, 19), (23, 2), (23, 6), (23, 23), (24, 10)]

def checkQBoundB (p : Nat) (Q : List (Nat × Nat)) : Bool :=
  Q.all (fun q => q.1 < p && q.2 < p)

def checkQIndepB (p : Nat) (Q : List (Nat × Nat)) : Bool :=
  checkPairwiseB (fun a b => !(cycDist p a.1 b.1 ≤ 3 && cycDist p a.2 b.2 ≤ 3)) Q

theorem checkQBoundB_sound (p : Nat) (Q : List (Nat × Nat)) (h : checkQBoundB p Q = true) :
    ∀ q ∈ Q, q.1 < p ∧ q.2 < p := by
  intro q hq
  have h1 := List.all_eq_true.mp h q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1

theorem checkQIndepB_sound (p : Nat) (Q : List (Nat × Nat)) (h : checkQIndepB p Q = true) :
    Q.Pairwise (fun q1 q2 => ¬ (cycDist p q1.1 q2.1 ≤ 3 ∧ cycDist p q1.2 q2.2 ≤ 3)) := by
  apply List.Pairwise.imp _ (checkPairwiseB_sound _ Q h)
  intro a b hab ⟨h1, h2⟩
  have h3 : (cycDist p a.1 b.1 ≤ 3 && cycDist p a.2 b.2 ≤ 3) = true := by simp [h1, h2]
  rw [h3] at hab; exact Bool.noConfusion hab

theorem q29_bound_ok : checkQBoundB 29 q29HBPZ = true := by decide
theorem q29_indep_ok : checkQIndepB 29 q29HBPZ = true := by decide
theorem q25_bound_ok : checkQBoundB 25 q25HBPZ = true := by decide
theorem q25_indep_ok : checkQIndepB 25 q25HBPZ = true := by decide

/-- **Theorem T2c (`C₂₉` World Record: `α(C₂₉^{⊠ 4}) ≥ 42,050`, `Θ(C₂₉) ≥ 14.319949949077991`).** -/
theorem t2c_c29_world_record :
    HasIndepSetOfSize (strongPow (cycleGraph 29) 4) 42050 ∧
    14319949949077991 ^ 4 ≤ 42050 * (10 ^ 15) ^ 4 := by
  have hQ50 : HasIndepSetOfSize (qGraphHBPZ 29) 50 := by
    have hlen : q29HBPZ.length = 50 := by decide
    have hbd := checkQBoundB_sound 29 q29HBPZ q29_bound_ok
    have hind := checkQIndepB_sound 29 q29HBPZ q29_indep_ok
    refine ⟨fun i =>
      let q := q29HBPZ[i.val]'(by rw [hlen]; exact i.isLt)
      let hb := hbd q (List.getElem_mem _)
      (⟨q.1, hb.1⟩, ⟨q.2, hb.2⟩), ?_⟩
    intro i j hij hconf
    rw [qGraphHBPZ, conflict_strongProd_iff, conflict_cycPowGraph_iff, conflict_cycPowGraph_iff] at hconf
    have hpw : ∀ (L : List (Nat × Nat)),
        L.Pairwise (fun a b => ¬ (cycDist 29 a.1 b.1 ≤ 3 ∧ cycDist 29 a.2 b.2 ≤ 3)) →
        ∀ (a b : Nat) (ha : a < L.length) (hb : b < L.length), a ≠ b →
          ¬ (cycDist 29 L[a].1 L[b].1 ≤ 3 ∧ cycDist 29 L[a].2 L[b].2 ≤ 3) := by
      intro L hL
      induction L with
      | nil => intro _ _ ha; exact nomatch ha
      | cons hd tl ih =>
        rw [List.pairwise_cons] at hL
        intro a b ha hb hab
        cases a with
        | zero =>
          cases b with
          | zero => exact False.elim (hab rfl)
          | succ b' => exact hL.1 (tl[b']'(by simp at hb; omega)) (List.getElem_mem _)
        | succ a' =>
          cases b with
          | zero =>
            intro ⟨h1, h2⟩
            exact hL.1 (tl[a']'(by simp at ha; omega)) (List.getElem_mem _)
              ⟨by rw [cycDist_symm]; exact h1, by rw [cycDist_symm]; exact h2⟩
          | succ b' =>
            exact ih hL.2 a' b' (by simp at ha; omega) (by simp at hb; omega) (fun h => hab (congrArg Nat.succ h))
    exact hpw q29HBPZ hind i.val j.val (by rw [hlen]; exact i.isLt) (by rw [hlen]; exact j.isLt)
      (fun h => hij (Fin.ext h)) hconf
  have h42050 := t1a_coset_quotient_compression.1 29 50 (by omega) hQ50
  exact ⟨h42050, by decide⟩

/-! ### 5. Local 81-Ball Baumert `RichPortSystem` Builder & `C₂₇`, `C₃₁` World Records (T2b, T2d) -/

def enc4 (np : Nat) (w : Fin 4 → Fin np) : Nat :=
  (((w ⟨0, by omega⟩).val * np + (w ⟨1, by omega⟩).val) * np + (w ⟨2, by omega⟩).val) * np + (w ⟨3, by omega⟩).val

def dec4 (np : Nat) (hnp : 0 < np) (c : Nat) : Fin 4 → Fin np :=
  let c3 := c % np; let r3 := c / np
  let c2 := r3 % np; let r2 := r3 / np
  let c1 := r2 % np; let c0 := (r2 / np) % np
  fun i => match i with
    | ⟨0, _⟩ => ⟨c0, Nat.mod_lt _ hnp⟩
    | ⟨1, _⟩ => ⟨c1, Nat.mod_lt _ hnp⟩
    | ⟨2, _⟩ => ⟨c2, Nat.mod_lt _ hnp⟩
    | ⟨3, _⟩ => ⟨c3, Nat.mod_lt _ hnp⟩

theorem enc4_lt (np : Nat) (w : Fin 4 → Fin np) :
    enc4 np w < np * np * np * np := by
  unfold enc4
  have h0 := (w ⟨0, by omega⟩).isLt
  have h1 := (w ⟨1, by omega⟩).isLt
  have h2 := (w ⟨2, by omega⟩).isLt
  have h3 := (w ⟨3, by omega⟩).isLt
  have s1 : (w ⟨0, by omega⟩).val * np + (w ⟨1, by omega⟩).val < np * np := by
    have := Nat.mul_le_mul_right np (Nat.succ_le_of_lt h0); rw [Nat.succ_mul] at this; omega
  have s2 : ((w ⟨0, by omega⟩).val * np + (w ⟨1, by omega⟩).val) * np + (w ⟨2, by omega⟩).val < np * np * np := by
    have := Nat.mul_le_mul_right np (Nat.succ_le_of_lt s1); rw [Nat.succ_mul] at this; omega
  have s3 := Nat.mul_le_mul_right np (Nat.succ_le_of_lt s2); rw [Nat.succ_mul] at s3; omega

theorem dec4_enc4 (np : Nat) (hnp : 0 < np) (w : Fin 4 → Fin np) :
    dec4 np hnp (enc4 np w) = w := by
  have hd : ∀ a b : Nat, b < np → (a * np + b) / np = a := fun a b hb => by
    rw [Nat.mul_comm a np, Nat.mul_add_div hnp, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hm : ∀ a b : Nat, b < np → (a * np + b) % np = b := fun a b hb => by
    rw [Nat.mul_comm a np, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have h0 : (w 0).val < np := (w 0).isLt
  have h1 : (w 1).val < np := (w 1).isLt
  have h2 : (w 2).val < np := (w 2).isLt
  have h3 : (w 3).val < np := (w 3).isLt
  funext i
  match i with
  | ⟨3, _⟩ => apply Fin.ext; dsimp [dec4, enc4]; exact hm _ _ h3
  | ⟨2, _⟩ => apply Fin.ext; dsimp [dec4, enc4]; rw [hd _ _ h3]; exact hm _ _ h2
  | ⟨1, _⟩ => apply Fin.ext; dsimp [dec4, enc4]; rw [hd _ _ h3, hd _ _ h2]; exact hm _ _ h1
  | ⟨0, _⟩ =>
    apply Fin.ext; dsimp [dec4, enc4]
    rw [hd _ _ h3, hd _ _ h2, hd _ _ h1]
    exact Nat.mod_eq_of_lt h0

theorem enc4_dec4 (np : Nat) (hnp : 0 < np) (c : Nat) (hc : c < np * np * np * np) :
    enc4 np (dec4 np hnp c) = c := by
  dsimp [enc4, dec4]
  have h1 := Nat.div_add_mod c np
  have h2 := Nat.div_add_mod (c / np) np
  have h3 := Nat.div_add_mod (c / np / np) np
  have hc0 : c / np / np / np < np := by
    have a1 : c / np < np * np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact hc)
    have a2 : c / np / np < np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a1)
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a2)
  rw [Nat.mod_eq_of_lt hc0]
  rw [Nat.mul_comm (c / np / np / np) np, h3, Nat.mul_comm (c / np / np) np, h2, Nat.mul_comm (c / np) np, h1]

theorem enc4_inj (np : Nat) (hnp : 0 < np) {u v : Fin 4 → Fin np} (h : enc4 np u = enc4 np v) : u = v := by
  rw [← dec4_enc4 np hnp u, ← dec4_enc4 np hnp v, h]

/-- Componentwise cyclic translation on `(Fin np)^4` and its inverse. -/
def shiftVec4 (np : Nat) (hnp : 0 < np) (s0 s1 s2 s3 : Nat) (w : Fin 4 → Fin np) : Fin 4 → Fin np
  | ⟨0, _⟩ => ⟨((w ⟨0, by omega⟩).val + s0) % np, Nat.mod_lt _ hnp⟩
  | ⟨1, _⟩ => ⟨((w ⟨1, by omega⟩).val + s1) % np, Nat.mod_lt _ hnp⟩
  | ⟨2, _⟩ => ⟨((w ⟨2, by omega⟩).val + s2) % np, Nat.mod_lt _ hnp⟩
  | ⟨3, _⟩ => ⟨((w ⟨3, by omega⟩).val + s3) % np, Nat.mod_lt _ hnp⟩

theorem shiftVec4_inv (np : Nat) (hnp : 0 < np) (s0 s1 s2 s3 : Nat) (w : Fin 4 → Fin np) :
    shiftVec4 np hnp (np - s0 % np) (np - s1 % np) (np - s2 % np) (np - s3 % np)
      (shiftVec4 np hnp s0 s1 s2 s3 w) = w := by
  have hb : ∀ (z s : Nat), z < np → ((z + s) % np + (np - s % np)) % np = z := by
    intro z s hz
    rw [Nat.mod_add_mod]
    have hsum : z + s + (np - s % np) = z + (s / np + 1) * np := by
      have hsm := Nat.div_add_mod s np
      have hml := Nat.mod_lt s hnp
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (s / np) np]; omega
    rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
  funext i; match i with
  | ⟨0, _⟩ => apply Fin.ext; exact hb _ s0 (w ⟨0, by omega⟩).isLt
  | ⟨1, _⟩ => apply Fin.ext; exact hb _ s1 (w ⟨1, by omega⟩).isLt
  | ⟨2, _⟩ => apply Fin.ext; exact hb _ s2 (w ⟨2, by omega⟩).isLt
  | ⟨3, _⟩ => apply Fin.ext; exact hb _ s3 (w ⟨3, by omega⟩).isLt

theorem shiftVec4_conflict_iff (np : Nat) (hnp : 0 < np) (s0 s1 s2 s3 : Nat)
    (u v : Fin 4 → Fin np) :
    conflict (strongPow (cycleGraph np) 4) (shiftVec4 np hnp s0 s1 s2 s3 u) (shiftVec4 np hnp s0 s1 s2 s3 v) ↔
    conflict (strongPow (cycleGraph np) 4) u v := by
  rw [conflict_strongPow_iff, conflict_strongPow_iff]
  constructor <;> (
    intro h i
    have hi := (conflict_cycleGraph_iff np _ _).mp (h i)
    rw [conflict_cycleGraph_iff]
    match i with
    | ⟨0, _⟩ => dsimp [shiftVec4] at hi ⊢; rw [cycDist_shift_eq np _ _ s0 (u _).isLt (v _).isLt hnp] at *; exact hi
    | ⟨1, _⟩ => dsimp [shiftVec4] at hi ⊢; rw [cycDist_shift_eq np _ _ s1 (u _).isLt (v _).isLt hnp] at *; exact hi
    | ⟨2, _⟩ => dsimp [shiftVec4] at hi ⊢; rw [cycDist_shift_eq np _ _ s2 (u _).isLt (v _).isLt hnp] at *; exact hi
    | ⟨3, _⟩ => dsimp [shiftVec4] at hi ⊢; rw [cycDist_shift_eq np _ _ s3 (u _).isLt (v _).isLt hnp] at *; exact hi)

/-- Strict-sortedness and `O(n + m)` two-pointer disjointness checks on `List Nat`. -/
def strictSortedB : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: tl => (a < b) && strictSortedB (b :: tl)

theorem strictSortedB_lt : ∀ (a : Nat) (tl : List Nat),
    strictSortedB (a :: tl) = true → ∀ x ∈ tl, a < x := by
  intro a tl
  induction tl generalizing a with
  | nil => intro _ _ hx; exact nomatch hx
  | cons b rest ih =>
    intro h x hx
    simp only [strictSortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hmem
    · exact h.1
    · exact Nat.lt_trans h.1 (ih b h.2 x hmem)

theorem strictSortedB_nodup : ∀ (L : List Nat), strictSortedB L = true → L.Nodup
  | [] => fun _ => List.nodup_nil
  | [_] => fun _ => by simp
  | a :: b :: tl => fun h => by
    rw [List.nodup_cons]
    have hlt := strictSortedB_lt a (b :: tl) h
    simp only [strictSortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fun hm => Nat.lt_irrefl a (hlt a hm), strictSortedB_nodup (b :: tl) h.2⟩

def dropWhileLt (a : Nat) : List Nat → List Nat
  | [] => []
  | b :: bs => if b < a then dropWhileLt a bs else b :: bs

theorem dropWhileLt_sorted (a : Nat) : ∀ (L : List Nat),
    strictSortedB L = true → strictSortedB (dropWhileLt a L) = true
  | [] => fun _ => rfl
  | b :: bs => fun h => by
    unfold dropWhileLt
    split
    · have hbs : strictSortedB bs = true := by
        cases bs with | nil => rfl | cons c cs => simp only [strictSortedB, Bool.and_eq_true] at h; exact h.2
      exact dropWhileLt_sorted a bs hbs
    · exact h

theorem dropWhileLt_mem (a : Nat) : ∀ (L : List Nat) (x : Nat),
    x ∈ L → x < a ∨ x ∈ dropWhileLt a L
  | [] => fun _ hx => nomatch hx
  | b :: bs => fun x hx => by
    unfold dropWhileLt
    split
    · rename_i hba
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hxs
      · exact Or.inl hba
      · exact dropWhileLt_mem a bs x hxs
    · exact Or.inr hx

/-- Purely structurally recursive `O(|L1| + |L2|)` disjointness check on strictly sorted lists! -/
def mergeDisjointB : List Nat → List Nat → Bool
  | [], _ => true
  | a :: as, L2 =>
    match dropWhileLt a L2 with
    | [] => true
    | b :: bs => (a < b) && mergeDisjointB as (b :: bs)

theorem mergeDisjointB_sound : ∀ (L1 L2 : List Nat),
    strictSortedB L1 = true → strictSortedB L2 = true → mergeDisjointB L1 L2 = true →
    ∀ x ∈ L1, x ∉ L2 := by
  intro L1
  induction L1 with
  | nil => intro _ _ _ _ _ hx; exact nomatch hx
  | cons a as ihas =>
    intro L2 hs1 hs2 hm x hx1 hx2
    have ha_le_x : a ≤ x := by
      simp only [List.mem_cons] at hx1
      rcases hx1 with rfl | hxa
      · exact Nat.le_refl x
      · exact Nat.le_of_lt (strictSortedB_lt a as hs1 x hxa)
    have hx_in_drop : x ∈ dropWhileLt a L2 := by
      rcases dropWhileLt_mem a L2 x hx2 with hlt | hmem
      · omega
      · exact hmem
    unfold mergeDisjointB at hm
    cases hdrop : dropWhileLt a L2 with
    | nil => rw [hdrop] at hx_in_drop; exact nomatch hx_in_drop
    | cons b bs =>
      rw [hdrop] at hm hx_in_drop
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      have hs_drop : strictSortedB (b :: bs) = true := hdrop ▸ dropWhileLt_sorted a L2 hs2
      simp only [List.mem_cons] at hx1
      rcases hx1 with rfl | hxa
      · simp only [List.mem_cons] at hx_in_drop
        rcases hx_in_drop with heq | hxb
        · omega
        · have := strictSortedB_lt b bs hs_drop x hxb; omega
      · have hs1' : strictSortedB as = true := by
          cases as with | nil => rfl | cons c cs => simp only [strictSortedB, Bool.and_eq_true] at hs1; exact hs1.2
        exact ihas (b :: bs) hs1' hs_drop hm.2 x hxa hx_in_drop

theorem list_nodup_filter {α : Type} (p : α → Bool) : ∀ {L : List α}, L.Nodup → (L.filter p).Nodup
  | [], _ => List.nodup_nil
  | a :: tl, h => by
    rw [List.nodup_cons] at h
    rw [List.filter_cons]
    cases p a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact list_nodup_filter p h.2
    · simp only [↓reduceIte]
      rw [List.nodup_cons]
      exact ⟨fun hm => h.1 (List.mem_filter.mp hm).1, list_nodup_filter p h.2⟩

/-- Exact symbolic length of filtering out a `Nodup` subset `S` from a `Nodup` list `L`! -/
theorem list_filter_not_mem_len {α : Type} (L : List α) (eqb : α → α → Bool)
    (heqb : ∀ a b, eqb a b = true ↔ a = b) (hL : L.Nodup) :
    ∀ (S : List α), S.Nodup → (∀ x ∈ S, x ∈ L) →
      (L.filter (fun x => !S.any (fun y => eqb x y))).length = L.length - S.length := by
  intro S
  induction S generalizing L with
  | nil => intro _ _; simp
  | cons s tl ih =>
    intro hS hsub
    rw [List.nodup_cons] at hS
    have hsL : s ∈ L := hsub s (List.mem_cons_self ..)
    let L1 := L.filter (fun x => !eqb x s)
    have hL1_nodup : L1.Nodup := list_nodup_filter _ hL
    have hrem1 : ∀ (M : List α), M.Nodup → s ∈ M → (M.filter (fun x => !eqb x s)).length = M.length - 1 := by
      intro M
      induction M with
      | nil => intro _ hmem; exact nomatch hmem
      | cons a rest ihr =>
        intro hM hmem
        rw [List.nodup_cons] at hM
        simp only [List.mem_cons] at hmem
        rw [List.filter_cons]
        rcases hmem with hEq | hmem
        · subst hEq
          have heq : eqb s s = true := (heqb s s).mpr rfl
          simp only [heq, Bool.not_true]
          have hno : rest.filter (fun x => !eqb x s) = rest := by
            rw [List.filter_eq_self]
            intro x hx
            cases hb : eqb x s
            · rfl
            · exact False.elim (hM.1 ((heqb x s).mp hb ▸ hx))
          rw [hno]; simp
        · have hne : eqb a s = false := by
            cases hb : eqb a s
            · rfl
            · exact False.elim (hM.1 ((heqb a s).mp hb ▸ hmem))
          simp only [hne, Bool.not_false, ↓reduceIte, List.length_cons]
          have hr := ihr hM.2 hmem
          have hpos : 1 ≤ rest.length := by
            cases rest with | nil => exact nomatch hmem | cons _ _ => simp
          omega
    have hL1_len : L1.length = L.length - 1 := hrem1 L hL hsL
    have hsub1 : ∀ x ∈ tl, x ∈ L1 := by
      intro x hx
      dsimp [L1]; rw [List.mem_filter]
      refine ⟨hsub x (List.mem_cons_of_mem s hx), ?_⟩
      cases hb : eqb x s
      · rfl
      · exact False.elim (hS.1 ((heqb x s).mp hb ▸ hx))
    have hfeq : L.filter (fun x => !(s :: tl).any (fun y => eqb x y)) =
                L1.filter (fun x => !tl.any (fun y => eqb x y)) := by
      dsimp [L1]; rw [List.filter_filter]
      congr 1; funext x
      simp only [Bool.not_or, Bool.and_comm]
    rw [hfeq, ih L1 hL1_nodup hS.2 hsub1, hL1_len]
    simp only [List.length_cons]; omega

/-- Fast `O(1)` bitmask Baumert-`H_BPZ` membership oracle on explicit 4-coordinates `(w0,w1,w2,w3)`. -/
def inMaskHBPZ4 (p : Nat) (qMask : Nat → Nat) (w0 w1 w2 w3 : Nat) : Bool :=
  let p0 := if w0 < 2 then w0 else w0 - 2
  let p1 := if w1 < 2 then w1 else w1 - 2
  let p2 := if w2 < 2 then w2 else w2 - 2
  let p3 := if w3 < 2 then w3 else w3 - 2
  let qy := (p2 + 2 * p - 2 * p1) % p
  let qz := (p3 + 2 * p - 2 * p0) % p
  (((qMask qy) >>> qz) &&& 1) == 1

def inMaskHBPZ (p : Nat) (qMask : Nat → Nat) (c : Nat) : Bool :=
  let np := p + 2
  let w3 := c % np; let r3 := c / np
  let w2 := r3 % np; let r2 := r3 / np
  let w1 := r2 % np; let w0 := r2 / np
  inMaskHBPZ4 p qMask w0 w1 w2 w3

def unshiftCode (np is0 is1 is2 is3 c : Nat) : Nat :=
  let w3 := c % np; let r3 := c / np
  let w2 := r3 % np; let r2 := r3 / np
  let w1 := r2 % np; let w0 := r2 / np
  ((((w0 + is0) % np) * np + (w1 + is1) % np) * np + (w2 + is2) % np) * np + (w3 + is3) % np

/-- Fast 81-ball neighborhood checker passing explicit coordinates `(x0,x1,x2,x3)` with zero redundant div/mod! -/
def step3 (np x : Nat) : List Nat :=
  [x, (x + 1) % np, (x + np - 1) % np]

def check81Ball4 (np : Nat) (pred : Nat → Nat → Nat → Nat → Bool) (c : Nat) : Bool :=
  let w3 := c % np; let r3 := c / np
  let w2 := r3 % np; let r2 := r3 / np
  let w1 := r2 % np; let w0 := r2 / np
  (step3 np w0).all fun x0 =>
  (step3 np w1).all fun x1 =>
  (step3 np w2).all fun x2 =>
  (step3 np w3).all fun x3 =>
    pred x0 x1 x2 x3

theorem step3_complete (np : Nat) (hnp : 3 ≤ np) (a b : Nat) (ha : a < np) (hb : b < np)
    (hd : cycDist np a b ≤ 1) : b ∈ step3 np a := by
  rw [cycDist_le_iff np a b 1 ha hb] at hd
  unfold step3
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases hd with ⟨hge, hle⟩ | ⟨hge, hle⟩ | hle | hle
  · by_cases heq : b = a
    · left; exact heq
    · right; right
      have hba : b = a - 1 := by omega
      have : a + np - 1 = (a - 1) + np := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; exact hba
  · by_cases heq : b = a
    · left; exact heq
    · right; left
      have hba : b = a + 1 := by omega
      rw [Nat.mod_eq_of_lt (by omega)]; exact hba
  · right; right
    have ha0 : a = 0 := by omega
    have hb1 : b = np - 1 := by omega
    rw [ha0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; exact hb1
  · right; left
    have ha1 : a = np - 1 := by omega
    have hb0 : b = 0 := by omega
    have : a + 1 = np := by omega
    rw [this, Nat.mod_self]; exact hb0

theorem check81Ball4_sound (np : Nat) (hnp : 3 ≤ np) (pred : Nat → Nat → Nat → Nat → Bool) (c : Nat)
    (hc : c < np * np * np * np) (hok : check81Ball4 np pred c = true)
    (u : Fin 4 → Fin np)
    (hconf : conflict (strongPow (cycleGraph np) 4) (dec4 np (by omega) c) u) :
    pred (u ⟨0, by omega⟩).val (u ⟨1, by omega⟩).val (u ⟨2, by omega⟩).val (u ⟨3, by omega⟩).val = true := by
  rw [conflict_strongPow_iff] at hconf
  have h0 := (conflict_cycleGraph_iff np _ _).mp (hconf ⟨0, by omega⟩)
  have h1 := (conflict_cycleGraph_iff np _ _).mp (hconf ⟨1, by omega⟩)
  have h2 := (conflict_cycleGraph_iff np _ _).mp (hconf ⟨2, by omega⟩)
  have h3 := (conflict_cycleGraph_iff np _ _).mp (hconf ⟨3, by omega⟩)
  have hc0 : c / np / np / np < np := by
    have a1 : c / np < np * np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact hc)
    have a2 : c / np / np < np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a1)
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a2)
  dsimp [dec4] at h0 h1 h2 h3
  rw [Nat.mod_eq_of_lt hc0] at h0
  have m0 := step3_complete np hnp _ (u ⟨0, by omega⟩).val hc0 (u _).isLt h0
  have m1 := step3_complete np hnp _ (u ⟨1, by omega⟩).val (Nat.mod_lt _ (by omega)) (u _).isLt h1
  have m2 := step3_complete np hnp _ (u ⟨2, by omega⟩).val (Nat.mod_lt _ (by omega)) (u _).isLt h2
  have m3 := step3_complete np hnp _ (u ⟨3, by omega⟩).val (Nat.mod_lt _ (by omega)) (u _).isLt h3
  unfold check81Ball4 at hok
  have s0 := List.all_eq_true.mp hok (u ⟨0, by omega⟩).val m0
  have s1 := List.all_eq_true.mp s0 (u ⟨1, by omega⟩).val m1
  have s2 := List.all_eq_true.mp s1 (u ⟨2, by omega⟩).val m2
  exact List.all_eq_true.mp s2 (u ⟨3, by omega⟩).val m3

def conflictCodeB (np c1 c2 : Nat) : Bool :=
  let a3 := c1 % np; let r1 := c1 / np; let a2 := r1 % np; let r2 := r1 / np; let a1 := r2 % np; let a0 := r2 / np
  let b3 := c2 % np; let s1 := c2 / np; let b2 := s1 % np; let s2 := s1 / np; let b1 := s2 % np; let b0 := s2 / np
  (cycDist np a0 b0 ≤ 1) && (cycDist np a1 b1 ≤ 1) && (cycDist np a2 b2 ≤ 1) && (cycDist np a3 b3 ≤ 1)

theorem conflictCodeB_iff (np : Nat) (hnp : 0 < np) (u v : Fin 4 → Fin np) :
    conflictCodeB np (enc4 np u) (enc4 np v) = true ↔
    conflict (strongPow (cycleGraph np) 4) u v := by
  have hde_u := dec4_enc4 np hnp u
  have hde_v := dec4_enc4 np hnp v
  have hcu := enc4_lt np u
  have hcv := enc4_lt np v
  have hc0u : enc4 np u / np / np / np = (u ⟨0, by omega⟩).val := by
    have h0 := congrArg (fun f => (f ⟨0, by omega⟩).val) hde_u
    dsimp [dec4] at h0
    have hlt : enc4 np u / np / np / np < np := by
      have a1 : enc4 np u / np < np * np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact hcu)
      have a2 : enc4 np u / np / np < np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a1)
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a2)
    rw [Nat.mod_eq_of_lt hlt] at h0; exact h0
  have hc0v : enc4 np v / np / np / np = (v ⟨0, by omega⟩).val := by
    have h0 := congrArg (fun f => (f ⟨0, by omega⟩).val) hde_v
    dsimp [dec4] at h0
    have hlt : enc4 np v / np / np / np < np := by
      have a1 : enc4 np v / np < np * np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact hcv)
      have a2 : enc4 np v / np / np < np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a1)
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a2)
    rw [Nat.mod_eq_of_lt hlt] at h0; exact h0
  have hc1u : enc4 np u / np / np % np = (u ⟨1, by omega⟩).val := congrArg (fun f => (f ⟨1, by omega⟩).val) hde_u
  have hc1v : enc4 np v / np / np % np = (v ⟨1, by omega⟩).val := congrArg (fun f => (f ⟨1, by omega⟩).val) hde_v
  have hc2u : enc4 np u / np % np = (u ⟨2, by omega⟩).val := congrArg (fun f => (f ⟨2, by omega⟩).val) hde_u
  have hc2v : enc4 np v / np % np = (v ⟨2, by omega⟩).val := congrArg (fun f => (f ⟨2, by omega⟩).val) hde_v
  have hc3u : enc4 np u % np = (u ⟨3, by omega⟩).val := congrArg (fun f => (f ⟨3, by omega⟩).val) hde_u
  have hc3v : enc4 np v % np = (v ⟨3, by omega⟩).val := congrArg (fun f => (f ⟨3, by omega⟩).val) hde_v
  unfold conflictCodeB
  dsimp only
  rw [hc0u, hc0v, hc1u, hc1v, hc2u, hc2v, hc3u, hc3v, conflict_strongPow_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨⟨⟨d0, d1⟩, d2⟩, d3⟩ i
    rw [conflict_cycleGraph_iff]
    match i with
    | ⟨0, _⟩ => exact d0 | ⟨1, _⟩ => exact d1 | ⟨2, _⟩ => exact d2 | ⟨3, _⟩ => exact d3
  · intro h
    exact ⟨⟨⟨(conflict_cycleGraph_iff np _ _).mp (h ⟨0, by omega⟩),
             (conflict_cycleGraph_iff np _ _).mp (h ⟨1, by omega⟩)⟩,
             (conflict_cycleGraph_iff np _ _).mp (h ⟨2, by omega⟩)⟩,
             (conflict_cycleGraph_iff np _ _).mp (h ⟨3, by omega⟩)⟩

/-- Check that `qMask` agrees with `Q` on all `(y, z) ∈ [0, p) × [0, p)`. -/
def checkQMaskEqB (p : Nat) (Q : List (Nat × Nat)) (qMask : Nat → Nat) : Bool :=
  (List.range p).all fun y =>
  (List.range p).all fun z =>
    ((((qMask y) >>> z) &&& 1) == 1) == Q.any (fun q => q.1 == y && q.2 == z)

theorem inMaskHBPZ4_eq_inBaumert (p : Nat) (hp : 2 ≤ p) (Q : List (Nat × Nat)) (qMask : Nat → Nat)
    (heq : checkQMaskEqB p Q qMask = true) (w : Fin 4 → Fin (p + 2)) :
    inMaskHBPZ4 p qMask (w ⟨0, by omega⟩).val (w ⟨1, by omega⟩).val (w ⟨2, by omega⟩).val (w ⟨3, by omega⟩).val =
    inBaumertHBPZ p hp Q w := by
  unfold inMaskHBPZ4 inBaumertHBPZ
  dsimp only
  have hpull : ∀ x : Fin (p + 2), (if x.val < 2 then x.val else x.val - 2) = (pull1 p hp x).val := by
    intro x; unfold pull1; split <;> rfl
  rw [hpull, hpull, hpull, hpull]
  let qy := ((pull1 p hp (w ⟨2, by omega⟩)).val + 2 * p - 2 * (pull1 p hp (w ⟨1, by omega⟩)).val) % p
  let qz := ((pull1 p hp (w ⟨3, by omega⟩)).val + 2 * p - 2 * (pull1 p hp (w ⟨0, by omega⟩)).val) % p
  have hmy := List.all_eq_true.mp heq qy (List.mem_range.mpr (Nat.mod_lt _ (show 0 < p by omega)))
  have hmz := List.all_eq_true.mp hmy qz (List.mem_range.mpr (Nat.mod_lt _ (show 0 < p by omega)))
  exact beq_iff_eq.mp hmz

theorem inMaskHBPZ_eq_inMaskHBPZ4 (p : Nat) (qMask : Nat → Nat) (w : Fin 4 → Fin (p + 2)) :
    inMaskHBPZ p qMask (enc4 (p + 2) w) =
    inMaskHBPZ4 p qMask (w ⟨0, by omega⟩).val (w ⟨1, by omega⟩).val (w ⟨2, by omega⟩).val (w ⟨3, by omega⟩).val := by
  have hnp : 0 < p + 2 := by omega
  have hde := dec4_enc4 (p + 2) hnp w
  have hc := enc4_lt (p + 2) w
  have hlt : enc4 (p + 2) w / (p + 2) / (p + 2) / (p + 2) < p + 2 := by
    have a1 : enc4 (p + 2) w / (p + 2) < (p + 2) * (p + 2) * (p + 2) :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (p + 2)]; exact hc)
    have a2 : enc4 (p + 2) w / (p + 2) / (p + 2) < (p + 2) * (p + 2) :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (p + 2)]; exact a1)
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (p + 2)]; exact a2)
  have h0 : enc4 (p + 2) w / (p + 2) / (p + 2) / (p + 2) = (w ⟨0, by omega⟩).val := by
    have x := congrArg (fun f => (f ⟨0, by omega⟩).val) hde; dsimp [dec4] at x; rw [Nat.mod_eq_of_lt hlt] at x; exact x
  have h1 : enc4 (p + 2) w / (p + 2) / (p + 2) % (p + 2) = (w ⟨1, by omega⟩).val := congrArg (fun f => (f ⟨1, by omega⟩).val) hde
  have h2 : enc4 (p + 2) w / (p + 2) % (p + 2) = (w ⟨2, by omega⟩).val := congrArg (fun f => (f ⟨2, by omega⟩).val) hde
  have h3 : enc4 (p + 2) w % (p + 2) = (w ⟨3, by omega⟩).val := congrArg (fun f => (f ⟨3, by omega⟩).val) hde
  unfold inMaskHBPZ; dsimp only; rw [h0, h1, h2, h3]

theorem inMaskHBPZ_eq_inBaumert (p : Nat) (hp : 2 ≤ p) (Q : List (Nat × Nat)) (qMask : Nat → Nat)
    (heq : checkQMaskEqB p Q qMask = true) (w : Fin 4 → Fin (p + 2)) :
    inMaskHBPZ p qMask (enc4 (p + 2) w) = inBaumertHBPZ p hp Q w := by
  rw [inMaskHBPZ_eq_inMaskHBPZ4, inMaskHBPZ4_eq_inBaumert p hp Q qMask heq w]

/-- Chunked list helpers keeping every kernel `decide` recursion depth `≤ 65` (well below `512`). -/
def totalLen {α : Type} : List (List α) → Nat
  | [] => 0
  | c :: cs => c.length + totalLen cs

theorem flatten_length_eq_totalLen {α : Type} : ∀ (C : List (List α)), C.flatten.length = totalLen C
  | [] => rfl
  | c :: cs => by simp [List.flatten_cons, totalLen, flatten_length_eq_totalLen cs]

def allChunks {α : Type} (p : α → Bool) (C : List (List α)) : Bool :=
  C.all (fun ch => ch.all p)

theorem allChunks_sound {α : Type} (p : α → Bool) (C : List (List α)) (h : allChunks p C = true) :
    ∀ x ∈ C.flatten, p x = true := by
  intro x hx
  rw [List.mem_flatten] at hx
  rcases hx with ⟨ch, hch, hxch⟩
  exact List.all_eq_true.mp (List.all_eq_true.mp h ch hch) x hxch

/-- Range-pruned sorted-chunk membership (`u ∈ [head, last]` skips 95% of chunks in 2 comparisons!). -/
def elemSortedChunks (u : Nat) (C : List (List Nat)) : Bool :=
  C.any fun ch =>
    match ch with
    | [] => false
    | a :: tl => (a ≤ u) && (u ≤ (a :: tl).getLast (by simp)) && (a :: tl).elem u

theorem elemSortedChunks_sound (u : Nat) (C : List (List Nat)) (h : elemSortedChunks u C = true) :
    u ∈ C.flatten := by
  rw [elemSortedChunks, List.any_eq_true] at h
  rcases h with ⟨ch, hch, hmem⟩
  cases ch with
  | nil => exact Bool.noConfusion hmem
  | cons a tl =>
    simp only [Bool.and_eq_true] at hmem
    exact List.mem_flatten.mpr ⟨a :: tl, hch, List.elem_iff.mp hmem.2⟩

def strictSortedRangeB (lo : Nat) : List Nat → Option Nat
  | [] => some lo
  | a :: tl => if lo ≤ a then strictSortedRangeB (a + 1) tl else none

theorem strictSortedRangeB_sound : ∀ (c : List Nat) (lo hi : Nat),
    strictSortedRangeB lo c = some hi →
    lo ≤ hi ∧ (∀ x ∈ c, lo ≤ x ∧ x < hi) ∧ c.Nodup
  | [], lo, hi, h => by
    simp only [strictSortedRangeB, Option.some.injEq] at h; subst h
    refine ⟨Nat.le_refl _, ?_, List.nodup_nil⟩
    intro _ hx; exact nomatch hx
  | a :: tl, lo, hi, h => by
    unfold strictSortedRangeB at h
    split at h
    · rename_i hle
      have ⟨hhi, hmem, hnd⟩ := strictSortedRangeB_sound tl (a + 1) hi h
      refine ⟨by omega, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hxt
        · omega
        · have := hmem x hxt; omega
      · rw [List.nodup_cons]
        exact ⟨fun ha => by have := hmem a ha; omega, hnd⟩
    · exact nomatch h

theorem strictSortedRangeB_last : ∀ (a : Nat) (tl : List Nat) (lo hi : Nat),
    strictSortedRangeB lo (a :: tl) = some hi → (a :: tl).getLast (by simp) + 1 = hi
  | a, [], lo, hi, h => by
    unfold strictSortedRangeB at h
    split at h
    · simp only [strictSortedRangeB, Option.some.injEq] at h; simp [h]
    · exact nomatch h
  | a, b :: rest, lo, hi, h => by
    unfold strictSortedRangeB at h
    split at h
    · have ih := strictSortedRangeB_last b rest (a + 1) hi h
      simpa using ih
    · exact nomatch h

def strictSortedChunksAux (lo : Nat) : List (List Nat) → Bool
  | [] => true
  | c :: cs =>
    match strictSortedRangeB lo c with
    | none => false
    | some hi => strictSortedChunksAux hi cs

theorem strictSortedChunksAux_sound : ∀ (C : List (List Nat)) (lo : Nat),
    strictSortedChunksAux lo C = true →
    (∀ x ∈ C.flatten, lo ≤ x) ∧
    C.flatten.Nodup ∧
    (∀ a tl, (a :: tl) ∈ C → ∀ x ∈ (a :: tl), a ≤ x ∧ x ≤ (a :: tl).getLast (by simp))
  | [], _, _ => by
    refine ⟨?_, List.nodup_nil, ?_⟩
    · intro _ hx; exact nomatch hx
    · intro _ _ hc; exact nomatch hc
  | c :: cs, lo, h => by
    unfold strictSortedChunksAux at h
    cases hr : strictSortedRangeB lo c with
    | none => rw [hr] at h; exact Bool.noConfusion h
    | some hi =>
      rw [hr] at h
      have ⟨hlo_hi, hc_bd, hc_nd⟩ := strictSortedRangeB_sound c lo hi hr
      have ⟨hcs_bd, hcs_nd, hcs_rng⟩ := strictSortedChunksAux_sound cs hi h
      rw [List.flatten_cons]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [List.mem_append] at hx
        rcases hx with h1 | h2
        · exact (hc_bd x h1).1
        · exact Nat.le_trans hlo_hi (hcs_bd x h2)
      · rw [List.nodup_append]
        refine ⟨hc_nd, hcs_nd, fun a ha b hb heq => by
          subst heq; have h1 := (hc_bd a ha).2; have h2 := hcs_bd a hb; omega⟩
      · intro a tl hch x hx
        simp only [List.mem_cons] at hch
        rcases hch with hEq | hrest
        · subst hEq
          have hlast := strictSortedRangeB_last a tl lo hi hr
          have hxhi := (hc_bd x hx).2
          have hage : a ≤ x := by
            unfold strictSortedRangeB at hr
            split at hr
            · simp only [List.mem_cons] at hx
              rcases hx with rfl | hxt
              · exact Nat.le_refl _
              · have := (strictSortedRangeB_sound tl (a + 1) hi hr).2.1 x hxt; omega
            · exact nomatch hr
          omega
        · exact hcs_rng a tl hrest x hx

def disjointChunksB (C1 C2 : List (List Nat)) : Bool :=
  C1.all fun c1 =>
    C2.all fun c2 =>
      match c1, c2 with
      | a1 :: t1, a2 :: t2 =>
        ((a1 :: t1).getLast (by simp) < a2) ||
        ((a2 :: t2).getLast (by simp) < a1) ||
        (a1 :: t1).all (fun x => !(a2 :: t2).elem x)
      | _, _ => true

theorem disjointChunksB_sound (C1 C2 : List (List Nat))
    (h1 : strictSortedChunksAux 0 C1 = true) (h2 : strictSortedChunksAux 0 C2 = true)
    (hdisj : disjointChunksB C1 C2 = true) :
    ∀ x ∈ C1.flatten, x ∉ C2.flatten := by
  have hr1 := (strictSortedChunksAux_sound C1 0 h1).2.2
  have hr2 := (strictSortedChunksAux_sound C2 0 h2).2.2
  intro x hx1 hx2
  rw [List.mem_flatten] at hx1 hx2
  rcases hx1 with ⟨c1, hc1, hxc1⟩
  rcases hx2 with ⟨c2, hc2, hxc2⟩
  have hp := List.all_eq_true.mp (List.all_eq_true.mp hdisj c1 hc1) c2 hc2
  cases c1 with
  | nil => exact nomatch hxc1
  | cons a1 t1 =>
    cases c2 with
    | nil => exact nomatch hxc2
    | cons a2 t2 =>
      dsimp only at hp
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hp
      have hb1 := hr1 a1 t1 hc1 x hxc1
      have hb2 := hr2 a2 t2 hc2 x hxc2
      rcases hp with (hgt1 | hgt2) | hall
      · omega
      · omega
      · have hne := List.all_eq_true.mp hall x hxc1
        have hmem : (a2 :: t2).elem x = true := List.elem_iff.mpr hxc2
        rw [hmem] at hne; exact Bool.noConfusion hne

def checkPairwiseChunks {α : Type} (rel : α → α → Bool) : List (List α) → Bool
  | [] => true
  | c :: cs =>
    checkPairwiseB rel c &&
    cs.all (fun c2 => c.all (fun x => c2.all (fun y => rel x y))) &&
    checkPairwiseChunks rel cs

theorem checkPairwiseChunks_sound {α : Type} (rel : α → α → Bool) : ∀ (C : List (List α)),
    checkPairwiseChunks rel C = true → C.flatten.Pairwise (fun a b => rel a b = true)
  | [], _ => List.Pairwise.nil
  | c :: cs, h => by
    unfold checkPairwiseChunks at h
    simp only [Bool.and_eq_true] at h
    rw [List.flatten_cons, List.pairwise_append]
    refine ⟨checkPairwiseB_sound rel c h.1.1, checkPairwiseChunks_sound rel cs h.2, ?_⟩
    intro a ha b hb
    rw [List.mem_flatten] at hb
    rcases hb with ⟨c2, hc2, hbc2⟩
    exact List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h.1.2 c2 hc2) a ha) b hbc2

/-- Bundled chunked Boolean certificate using zero-division `check81Ball4` & `inMaskHBPZ4`! -/
structure BaumertChunkCert (p : Nat) (qMask : Nat → Nat) (is0 is1 is2 is3 : Nat)
    (portsC : List (List (Nat × Nat))) (footAC footDC : List (List Nat)) : Prop where
  hAsort : strictSortedChunksAux 0 footAC = true
  hDsort : strictSortedChunksAux 0 footDC = true
  hADdisj : disjointChunksB footAC footDC = true
  hOnodup : checkPairwiseChunks (fun a b => a.1 != b.1) portsC = true
  hHindep : checkPairwiseChunks (fun a b => !conflictCodeB (p + 2) a.2 b.2) portsC = true
  hPbd : allChunks (fun pr => pr.1 < (p + 2) * (p + 2) * (p + 2) * (p + 2) &&
           pr.2 < (p + 2) * (p + 2) * (p + 2) * (p + 2) && inMaskHBPZ p qMask pr.1) portsC = true
  hAbd : allChunks (fun c => c < (p + 2) * (p + 2) * (p + 2) * (p + 2) &&
           inMaskHBPZ p qMask (unshiftCode (p + 2) is0 is1 is2 is3 c)) footAC = true
  hDbd : allChunks (fun c => c < (p + 2) * (p + 2) * (p + 2) * (p + 2) &&
           inMaskHBPZ p qMask (unshiftCode (p + 2) is0 is1 is2 is3 c)) footDC = true
  hPriv : allChunks (fun pr => check81Ball4 (p + 2) (fun x0 x1 x2 x3 =>
            !inMaskHBPZ4 p qMask x0 x1 x2 x3 ||
            ((((x0 * (p + 2) + x1) * (p + 2) + x2) * (p + 2) + x3) == pr.1)) pr.2) portsC = true
  hAcomp : allChunks (fun pr => check81Ball4 (p + 2) (fun x0 x1 x2 x3 =>
             !inMaskHBPZ4 p qMask ((x0 + is0) % (p + 2)) ((x1 + is1) % (p + 2))
                                  ((x2 + is2) % (p + 2)) ((x3 + is3) % (p + 2)) ||
             elemSortedChunks (((x0 * (p + 2) + x1) * (p + 2) + x2) * (p + 2) + x3) footAC) pr.1) portsC = true
  hDcomp : allChunks (fun pr => check81Ball4 (p + 2) (fun x0 x1 x2 x3 =>
             !inMaskHBPZ4 p qMask ((x0 + is0) % (p + 2)) ((x1 + is1) % (p + 2))
                                  ((x2 + is2) % (p + 2)) ((x3 + is3) % (p + 2)) ||
             elemSortedChunks (((x0 * (p + 2) + x1) * (p + 2) + x2) * (p + 2) + x3) footDC) pr.2) portsC = true

def eqbVec4 (np : Nat) (u v : Fin 4 → Fin np) : Bool :=
  enc4 np u == enc4 np v

theorem eqbVec4_iff (np : Nat) (hnp : 0 < np) (u v : Fin 4 → Fin np) :
    eqbVec4 np u v = true ↔ u = v := by
  unfold eqbVec4
  rw [beq_iff_eq]
  exact ⟨enc4_inj np hnp, fun h => by rw [h]⟩

theorem list_nodup_getElem_ne {α : Type} : ∀ (L : List α), L.Nodup →
    ∀ (a b : Nat) (ha : a < L.length) (hb : b < L.length), a ≠ b → L[a] ≠ L[b]
  | [], _, _, _, ha, _, _, _ => nomatch ha
  | hd :: tl, hl, a, b, ha, hb, hab, h => by
    rw [List.nodup_cons] at hl
    cases a with
    | zero => cases b with
      | zero => exact hab rfl
      | succ b' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
        exact hl.1 (h ▸ List.getElem_mem (by simp at hb; omega))
    | succ a' => cases b with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
        exact hl.1 (h.symm ▸ List.getElem_mem (by simp at ha; omega))
      | succ b' =>
        simp only [List.getElem_cons_succ] at h
        exact list_nodup_getElem_ne tl hl.2 a' b' (by simp at ha; omega) (by simp at hb; omega)
                     (fun hEq => hab (congrArg Nat.succ hEq)) h

theorem dec4_map_nodup (np : Nat) (hnp : 0 < np) : ∀ (L : List Nat),
    L.Nodup → (∀ c ∈ L, c < np * np * np * np) → (L.map (dec4 np hnp)).Nodup
  | [], _, _ => List.nodup_nil
  | a :: tl, hnd, hbd => by
    rw [List.nodup_cons] at hnd; rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, dec4_map_nodup np hnp tl hnd.2 (fun c hc => hbd c (List.mem_cons_of_mem a hc))⟩
    intro hm; rw [List.mem_map] at hm; rcases hm with ⟨b, hb, heq⟩
    have ha_lt := hbd a (List.mem_cons_self ..)
    have hb_lt := hbd b (List.mem_cons_of_mem a hb)
    have hce := congrArg (enc4 np) heq
    rw [enc4_dec4 np hnp b hb_lt, enc4_dec4 np hnp a ha_lt] at hce
    exact hnd.1 (hce ▸ hb)

theorem dec4_pairwise_indep (np : Nat) (hnp : 0 < np) : ∀ (L : List Nat),
    L.Pairwise (fun a b => !conflictCodeB np a b = true) →
    (∀ c ∈ L, c < np * np * np * np) →
    ∀ (a b : Nat) (ha : a < L.length) (hb : b < L.length), a ≠ b →
      ¬ conflict (strongPow (cycleGraph np) 4) (dec4 np hnp L[a]) (dec4 np hnp L[b])
  | [], _, _, _, _, ha, _, _, _ => nomatch ha
  | hd :: tl, hL, hbd, a, b, ha, hb, hab, hc => by
    rw [List.pairwise_cons] at hL
    have hcheck : ∀ c1 c2, c1 < np * np * np * np → c2 < np * np * np * np →
        (!conflictCodeB np c1 c2 = true) →
        ¬ conflict (strongPow (cycleGraph np) 4) (dec4 np hnp c1) (dec4 np hnp c2) := by
      intro c1 c2 h1 h2 hnb hcc
      have hcb := (conflictCodeB_iff np hnp (dec4 np hnp c1) (dec4 np hnp c2)).mpr hcc
      rw [enc4_dec4 np hnp c1 h1, enc4_dec4 np hnp c2 h2] at hcb
      rw [hcb] at hnb; exact Bool.noConfusion hnb
    cases a with
    | zero => cases b with
      | zero => exact hab rfl
      | succ b' =>
        exact hcheck hd (tl[b']'(by simp at hb; omega)) (hbd hd (List.mem_cons_self ..))
          (hbd _ (List.mem_cons_of_mem hd (List.getElem_mem _))) (hL.1 _ (List.getElem_mem _)) hc
    | succ a' => cases b with
      | zero =>
        exact hcheck hd (tl[a']'(by simp at ha; omega)) (hbd hd (List.mem_cons_self ..))
          (hbd _ (List.mem_cons_of_mem hd (List.getElem_mem _))) (hL.1 _ (List.getElem_mem _)) (conflict_symm _ hc)
      | succ b' =>
        exact dec4_pairwise_indep np hnp tl hL.2 (fun c hc => hbd c (List.mem_cons_of_mem hd hc)) a' b'
          (by simp at ha; omega) (by simp at hb; omega) (fun h => hab (congrArg Nat.succ h)) hc

theorem unshiftCode_enc4_eq (np : Nat) (hnp : 0 < np) (is0 is1 is2 is3 : Nat) (w : Fin 4 → Fin np) :
    unshiftCode np is0 is1 is2 is3 (enc4 np w) = enc4 np (shiftVec4 np hnp is0 is1 is2 is3 w) := by
  have hde := dec4_enc4 np hnp w
  have hcu := enc4_lt np w
  have hlt : enc4 np w / np / np / np < np := by
    have a1 : enc4 np w / np < np * np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact hcu)
    have a2 : enc4 np w / np / np < np * np := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a1)
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm np]; exact a2)
  have h0 : enc4 np w / np / np / np = (w ⟨0, by omega⟩).val := by
    have x := congrArg (fun f => (f ⟨0, by omega⟩).val) hde; dsimp [dec4] at x; rw [Nat.mod_eq_of_lt hlt] at x; exact x
  have h1 : enc4 np w / np / np % np = (w ⟨1, by omega⟩).val := congrArg (fun f => (f ⟨1, by omega⟩).val) hde
  have h2 : enc4 np w / np % np = (w ⟨2, by omega⟩).val := congrArg (fun f => (f ⟨2, by omega⟩).val) hde
  have h3 : enc4 np w % np = (w ⟨3, by omega⟩).val := congrArg (fun f => (f ⟨3, by omega⟩).val) hde
  unfold unshiftCode; dsimp only; rw [h0, h1, h2, h3]; rfl

theorem shiftVec4_unshift_inv (np : Nat) (hnp : 0 < np) (s0 s1 s2 s3 : Nat) (w : Fin 4 → Fin np) :
    shiftVec4 np hnp s0 s1 s2 s3
      (shiftVec4 np hnp (np - s0 % np) (np - s1 % np) (np - s2 % np) (np - s3 % np) w) = w := by
  have hback : ∀ (z s : Nat), z < np → ((z + (np - s % np)) % np + s) % np = z := by
    intro z s hz
    rw [Nat.mod_add_mod]
    have hsum : z + (np - s % np) + s = z + (s / np + 1) * np := by
      have hsm := Nat.div_add_mod s np; have hml := Nat.mod_lt s hnp
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (s / np) np]; omega
    rw [hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
  funext i; match i with
  | ⟨0, _⟩ => apply Fin.ext; exact hback _ s0 (w ⟨0, by omega⟩).isLt
  | ⟨1, _⟩ => apply Fin.ext; exact hback _ s1 (w ⟨1, by omega⟩).isLt
  | ⟨2, _⟩ => apply Fin.ext; exact hback _ s2 (w ⟨2, by omega⟩).isLt
  | ⟨3, _⟩ => apply Fin.ext; exact hback _ s3 (w ⟨3, by omega⟩).isLt

/-- General soundness theorem: ANY chunked Baumert certificate constructs a verified
`RichPortSystem (strongPow (cycleGraph (p + 2)) 4)` with exact symbolic counts
`(N - d, N - |A| - |D|, |A|, |D|, d)` and ZERO `N`-element kernel enumeration! -/
def buildBaumertRichPortSystem (p : Nat) (hp : 9 ≤ p)
    (Q : List (Nat × Nat)) (qMask : Nat → Nat)
    (s0 s1 s2 s3 : Nat)
    (portsC : List (List (Nat × Nat))) (footAC footDC : List (List Nat))
    (hQbd : checkQBoundB p Q = true)
    (hQind : checkQIndepB p Q = true)
    (hMask : checkQMaskEqB p Q qMask = true)
    (hCert : BaumertChunkCert p qMask ((p + 2) - s0 % (p + 2)) ((p + 2) - s1 % (p + 2))
               ((p + 2) - s2 % (p + 2)) ((p + 2) - s3 % (p + 2)) portsC footAC footDC) :
    RichPortSystem (strongPow (cycleGraph (p + 2)) 4) := by
  have hnp : 0 < p + 2 := by omega
  have hnp3 : 3 ≤ p + 2 := by omega
  let is0 := (p + 2) - s0 % (p + 2)
  let is1 := (p + 2) - s1 % (p + 2)
  let is2 := (p + 2) - s2 % (p + 2)
  let is3 := (p + 2) - s3 % (p + 2)
  let ports := portsC.flatten
  let footA := footAC.flatten
  let footD := footDC.flatten
  let Ilist := baumertExpandList p (by omega) Q
  let Xlist := Ilist.map (shiftVec4 (p + 2) hnp s0 s1 s2 s3)
  have hQb := checkQBoundB_sound p Q hQbd
  have hQi := checkQIndepB_sound p Q hQind
  have ⟨hI_nodup, hI_indep⟩ := baumertExpandList_nodup_and_indep p hp Q hQb hQi
  have hX_nodup : Xlist.Nodup :=
    list_nodup_map (fun u v huv => by
      have := congrArg (shiftVec4 (p + 2) hnp is0 is1 is2 is3) huv
      rw [shiftVec4_inv, shiftVec4_inv] at this; exact this) hI_nodup
  have hX_indep : ∀ u v, u ∈ Xlist → v ∈ Xlist → u ≠ v → ¬ conflict (strongPow (cycleGraph (p + 2)) 4) u v := by
    intro u v hu hv huv hconf
    dsimp [Xlist] at hu hv; rw [List.mem_map] at hu hv
    rcases hu with ⟨a, ha, rfl⟩; rcases hv with ⟨b, hb, rfl⟩
    have hab : a ≠ b := fun h => huv (by rw [h])
    rw [shiftVec4_conflict_iff] at hconf
    exact hI_indep a b ha hb hab hconf
  have hI_mem : ∀ w : Fin 4 → Fin (p + 2), w ∈ Ilist ↔ inMaskHBPZ p qMask (enc4 (p + 2) w) = true := fun w => by
    rw [baumertExpandList_mem_iff p (by omega) Q hQb w, inMaskHBPZ_eq_inBaumert p (by omega) Q qMask hMask w]
  have hI_mem4 : ∀ w : Fin 4 → Fin (p + 2),
      w ∈ Ilist ↔ inMaskHBPZ4 p qMask (w ⟨0, by omega⟩).val (w ⟨1, by omega⟩).val (w ⟨2, by omega⟩).val (w ⟨3, by omega⟩).val = true := fun w => by
    rw [hI_mem w, inMaskHBPZ_eq_inMaskHBPZ4]
  have hX_mem : ∀ w : Fin 4 → Fin (p + 2),
      w ∈ Xlist ↔ inMaskHBPZ p qMask (unshiftCode (p + 2) is0 is1 is2 is3 (enc4 (p + 2) w)) = true := by
    intro w
    rw [unshiftCode_enc4_eq (p + 2) hnp is0 is1 is2 is3 w, ← hI_mem]
    constructor
    · intro hw; dsimp [Xlist] at hw; rw [List.mem_map] at hw
      rcases hw with ⟨a, ha, rfl⟩; rw [shiftVec4_inv]; exact ha
    · intro hu; dsimp [Xlist]; rw [List.mem_map]
      exact ⟨shiftVec4 (p + 2) hnp is0 is1 is2 is3 w, hu, shiftVec4_unshift_inv (p + 2) hnp s0 s1 s2 s3 w⟩
  have hX_mem4 : ∀ w : Fin 4 → Fin (p + 2),
      w ∈ Xlist ↔
      inMaskHBPZ4 p qMask
        (((w ⟨0, by omega⟩).val + is0) % (p + 2))
        (((w ⟨1, by omega⟩).val + is1) % (p + 2))
        (((w ⟨2, by omega⟩).val + is2) % (p + 2))
        (((w ⟨3, by omega⟩).val + is3) % (p + 2)) = true := by
    intro w
    rw [hX_mem w, unshiftCode_enc4_eq (p + 2) hnp is0 is1 is2 is3 w, inMaskHBPZ_eq_inMaskHBPZ4]
    rfl
  let Olist := (ports.map Prod.fst).map (dec4 (p + 2) hnp)
  let Hlist := (ports.map Prod.snd).map (dec4 (p + 2) hnp)
  let Alist := footA.map (dec4 (p + 2) hnp)
  let Dlist := footD.map (dec4 (p + 2) hnp)
  let Blist := Ilist.filter (fun w => !Olist.any (fun y => eqbVec4 (p + 2) w y))
  let Nlist := Xlist.filter (fun w => !(Alist ++ Dlist).any (fun y => eqbVec4 (p + 2) w y))
  have hO_nodup_codes : (ports.map Prod.fst).Nodup := by
    have hpw := checkPairwiseChunks_sound (fun a b : Nat × Nat => a.1 != b.1) portsC hCert.hOnodup
    unfold List.Nodup
    rw [List.pairwise_map]
    exact List.Pairwise.imp (fun {a b} h heq => by rw [heq] at h; simp at h) hpw
  have hPbd_all := allChunks_sound _ portsC hCert.hPbd
  have hAbd_all := allChunks_sound _ footAC hCert.hAbd
  have hDbd_all := allChunks_sound _ footDC hCert.hDbd
  have hP_lt1 : ∀ c ∈ ports.map Prod.fst, c < (p + 2) * (p + 2) * (p + 2) * (p + 2) := by
    intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨pr, hpr, rfl⟩
    have := hPbd_all pr hpr; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1.1
  have hP_lt2 : ∀ c ∈ ports.map Prod.snd, c < (p + 2) * (p + 2) * (p + 2) * (p + 2) := by
    intro c hc; rw [List.mem_map] at hc; rcases hc with ⟨pr, hpr, rfl⟩
    have := hPbd_all pr hpr; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1.2
  have hA_lt : ∀ c ∈ footA, c < (p + 2) * (p + 2) * (p + 2) * (p + 2) := by
    intro c hc; have := hAbd_all c hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have hD_lt : ∀ c ∈ footD, c < (p + 2) * (p + 2) * (p + 2) * (p + 2) := by
    intro c hc; have := hDbd_all c hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have hO_nodup : Olist.Nodup := dec4_map_nodup (p + 2) hnp _ hO_nodup_codes hP_lt1
  have hA_nodup : Alist.Nodup := dec4_map_nodup (p + 2) hnp _ (strictSortedChunksAux_sound footAC 0 hCert.hAsort).2.1 hA_lt
  have hD_nodup : Dlist.Nodup := dec4_map_nodup (p + 2) hnp _ (strictSortedChunksAux_sound footDC 0 hCert.hDsort).2.1 hD_lt
  have hAD_disj_codes := disjointChunksB_sound footAC footDC hCert.hAsort hCert.hDsort hCert.hADdisj
  have hAD_nodup : (Alist ++ Dlist).Nodup := by
    rw [List.nodup_append]; refine ⟨hA_nodup, hD_nodup, ?_⟩
    intro u hu v hv heq; subst heq
    dsimp [Alist] at hu; dsimp [Dlist] at hv; rw [List.mem_map] at hu hv
    rcases hu with ⟨ca, hca, rfl⟩; rcases hv with ⟨cd, hcd, hdec⟩
    have hce := congrArg (enc4 (p + 2)) hdec
    rw [enc4_dec4 (p + 2) hnp cd (hD_lt cd hcd), enc4_dec4 (p + 2) hnp ca (hA_lt ca hca)] at hce
    exact hAD_disj_codes ca hca (hce ▸ hcd)
  have hO_sub_I : ∀ w ∈ Olist, w ∈ Ilist := by
    intro w hw; dsimp [Olist] at hw; rw [List.mem_map] at hw
    rcases hw with ⟨c, hc, rfl⟩; rw [List.mem_map] at hc; rcases hc with ⟨pr, hpr, rfl⟩
    have h1 := hPbd_all pr hpr; simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    rw [hI_mem, enc4_dec4 (p + 2) hnp pr.1 h1.1.1]; exact h1.2
  have hA_sub_X : ∀ w ∈ Alist, w ∈ Xlist := by
    intro w hw; dsimp [Alist] at hw; rw [List.mem_map] at hw; rcases hw with ⟨c, hc, rfl⟩
    have h1 := hAbd_all c hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    rw [hX_mem, enc4_dec4 (p + 2) hnp c h1.1]; exact h1.2
  have hD_sub_X : ∀ w ∈ Dlist, w ∈ Xlist := by
    intro w hw; dsimp [Dlist] at hw; rw [List.mem_map] at hw; rcases hw with ⟨c, hc, rfl⟩
    have h1 := hDbd_all c hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    rw [hX_mem, enc4_dec4 (p + 2) hnp c h1.1]; exact h1.2
  have hAD_sub_X : ∀ w ∈ Alist ++ Dlist, w ∈ Xlist := fun w hw => by
    rw [List.mem_append] at hw; rcases hw with h | h; exact hA_sub_X w h; exact hD_sub_X w h
  have hPlen : ports.length = totalLen portsC := flatten_length_eq_totalLen portsC
  have hAlen : footA.length = totalLen footAC := flatten_length_eq_totalLen footAC
  have hDlen : footD.length = totalLen footDC := flatten_length_eq_totalLen footDC
  have hB_len : Blist.length = baumertFactoredCard p Q - totalLen portsC := by
    dsimp [Blist]
    rw [list_filter_not_mem_len Ilist (eqbVec4 (p + 2)) (eqbVec4_iff (p + 2) hnp) hI_nodup Olist hO_nodup hO_sub_I]
    dsimp [Ilist, Olist]; rw [baumertExpandList_len, List.length_map, List.length_map, hPlen]
  have hN_len : Nlist.length = baumertFactoredCard p Q - (totalLen footAC + totalLen footDC) := by
    dsimp [Nlist]
    rw [list_filter_not_mem_len Xlist (eqbVec4 (p + 2)) (eqbVec4_iff (p + 2) hnp) hX_nodup (Alist ++ Dlist) hAD_nodup hAD_sub_X]
    dsimp [Xlist, Ilist, Alist, Dlist]
    rw [List.length_map, baumertExpandList_len, List.length_append, List.length_map, List.length_map, hAlen, hDlen]
  have hA_len : Alist.length = totalLen footAC := by rw [List.length_map, hAlen]
  have hD_len : Dlist.length = totalLen footDC := by rw [List.length_map, hDlen]
  have hO_len : Olist.length = totalLen portsC := by dsimp [Olist]; rw [List.length_map, List.length_map, hPlen]
  have hH_len : Hlist.length = totalLen portsC := by dsimp [Hlist]; rw [List.length_map, List.length_map, hPlen]
  have hB_nodup : Blist.Nodup := list_nodup_filter _ hI_nodup
  have hN_nodup : Nlist.Nodup := list_nodup_filter _ hX_nodup
  have hB_sub_I : ∀ w ∈ Blist, w ∈ Ilist := fun w hw => (List.mem_filter.mp hw).1
  have hB_not_O : ∀ w ∈ Blist, w ∉ Olist := fun w hw hO => by
    have h2 := (List.mem_filter.mp hw).2
    have hany : Olist.any (fun y => eqbVec4 (p + 2) w y) = true :=
      List.any_eq_true.mpr ⟨w, hO, (eqbVec4_iff (p + 2) hnp w w).mpr rfl⟩
    rw [hany] at h2; exact Bool.noConfusion h2
  have hN_sub_X : ∀ w ∈ Nlist, w ∈ Xlist := fun w hw => (List.mem_filter.mp hw).1
  have hN_not_A : ∀ w ∈ Nlist, w ∉ Alist := fun w hw hA => by
    have h2 := (List.mem_filter.mp hw).2
    have hany : (Alist ++ Dlist).any (fun y => eqbVec4 (p + 2) w y) = true :=
      List.any_eq_true.mpr ⟨w, List.mem_append_left Dlist hA, (eqbVec4_iff (p + 2) hnp w w).mpr rfl⟩
    rw [hany] at h2; exact Bool.noConfusion h2
  have hN_not_D : ∀ w ∈ Nlist, w ∉ Dlist := fun w hw hD => by
    have h2 := (List.mem_filter.mp hw).2
    have hany : (Alist ++ Dlist).any (fun y => eqbVec4 (p + 2) w y) = true :=
      List.any_eq_true.mpr ⟨w, List.mem_append_right Alist hD, (eqbVec4_iff (p + 2) hnp w w).mpr rfl⟩
    rw [hany] at h2; exact Bool.noConfusion h2
  have hPriv_all := allChunks_sound _ portsC hCert.hPriv
  have hAcomp_all := allChunks_sound _ portsC hCert.hAcomp
  have hDcomp_all := allChunks_sound _ portsC hCert.hDcomp
  have hpriv_H : ∀ (j : Fin (totalLen portsC)) (w : Fin 4 → Fin (p + 2)),
      w ∈ Ilist → conflict (strongPow (cycleGraph (p + 2)) 4) (Hlist[j.val]'(by rw [hH_len]; exact j.isLt)) w →
      w = Olist[j.val]'(by rw [hO_len]; exact j.isLt) := by
    intro j w hw hconf
    have hj_p : j.val < ports.length := by rw [hPlen]; exact j.isLt
    let pr := ports[j.val]'hj_p
    have hpr_mem : pr ∈ ports := List.getElem_mem hj_p
    have hpr_bd := hPbd_all pr hpr_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpr_bd
    have hpr_ok := hPriv_all pr hpr_mem
    have hHj : Hlist[j.val]'(by rw [hH_len]; exact j.isLt) = dec4 (p + 2) hnp pr.2 := by dsimp [Hlist, pr]; simp
    have hOj : Olist[j.val]'(by rw [hO_len]; exact j.isLt) = dec4 (p + 2) hnp pr.1 := by dsimp [Olist, pr]; simp
    rw [hHj] at hconf; rw [hOj]
    have hpred := check81Ball4_sound (p + 2) hnp3 _ pr.2 hpr_bd.1.2 hpr_ok w hconf
    have hwin := (hI_mem4 w).mp hw
    simp only [hwin, Bool.not_true, Bool.false_or, beq_iff_eq] at hpred
    change enc4 (p + 2) w = pr.1 at hpred
    rw [← dec4_enc4 (p + 2) hnp w, hpred]
  have hfoot_O : ∀ (j : Fin (totalLen portsC)) (w : Fin 4 → Fin (p + 2)),
      w ∈ Xlist → conflict (strongPow (cycleGraph (p + 2)) 4) (Olist[j.val]'(by rw [hO_len]; exact j.isLt)) w →
      w ∈ Alist := by
    intro j w hw hconf
    have hj_p : j.val < ports.length := by rw [hPlen]; exact j.isLt
    let pr := ports[j.val]'hj_p
    have hpr_mem : pr ∈ ports := List.getElem_mem hj_p
    have hpr_bd := hPbd_all pr hpr_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpr_bd
    have hpr_ok := hAcomp_all pr hpr_mem
    have hOj : Olist[j.val]'(by rw [hO_len]; exact j.isLt) = dec4 (p + 2) hnp pr.1 := by dsimp [Olist, pr]; simp
    rw [hOj] at hconf
    have hpred := check81Ball4_sound (p + 2) hnp3 _ pr.1 hpr_bd.1.1 hpr_ok w hconf
    have hwx := (hX_mem4 w).mp hw
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hpred
    have hmem_c : enc4 (p + 2) w ∈ footA :=
      match hpred with
      | Or.inl hfalse => Bool.noConfusion (hfalse.symm.trans hwx)
      | Or.inr hgood => elemSortedChunks_sound (enc4 (p + 2) w) footAC hgood
    dsimp [Alist]; rw [List.mem_map]
    exact ⟨enc4 (p + 2) w, hmem_c, dec4_enc4 (p + 2) hnp w⟩
  have hfoot_H : ∀ (j : Fin (totalLen portsC)) (w : Fin 4 → Fin (p + 2)),
      w ∈ Xlist → conflict (strongPow (cycleGraph (p + 2)) 4) (Hlist[j.val]'(by rw [hH_len]; exact j.isLt)) w →
      w ∈ Dlist := by
    intro j w hw hconf
    have hj_p : j.val < ports.length := by rw [hPlen]; exact j.isLt
    let pr := ports[j.val]'hj_p
    have hpr_mem : pr ∈ ports := List.getElem_mem hj_p
    have hpr_bd := hPbd_all pr hpr_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpr_bd
    have hpr_ok := hDcomp_all pr hpr_mem
    have hHj : Hlist[j.val]'(by rw [hH_len]; exact j.isLt) = dec4 (p + 2) hnp pr.2 := by dsimp [Hlist, pr]; simp
    rw [hHj] at hconf
    have hpred := check81Ball4_sound (p + 2) hnp3 _ pr.2 hpr_bd.1.2 hpr_ok w hconf
    have hwx := (hX_mem4 w).mp hw
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hpred
    have hmem_c : enc4 (p + 2) w ∈ footD :=
      match hpred with
      | Or.inl hfalse => Bool.noConfusion (hfalse.symm.trans hwx)
      | Or.inr hgood => elemSortedChunks_sound (enc4 (p + 2) w) footDC hgood
    dsimp [Dlist]; rw [List.mem_map]
    exact ⟨enc4 (p + 2) w, hmem_c, dec4_enc4 (p + 2) hnp w⟩
  have hH_indep_proof : ∀ (i j : Fin (totalLen portsC)), i ≠ j →
      ¬ conflict (strongPow (cycleGraph (p + 2)) 4)
          (Hlist[i.val]'(by rw [hH_len]; exact i.isLt))
          (Hlist[j.val]'(by rw [hH_len]; exact j.isLt)) := by
    have hpw : (ports.map Prod.snd).Pairwise (fun a b => !conflictCodeB (p + 2) a b = true) := by
      rw [List.pairwise_map]
      exact checkPairwiseChunks_sound (fun a b : Nat × Nat => !conflictCodeB (p + 2) a.2 b.2) portsC hCert.hHindep
    intro i j hij hc
    have hi_m : i.val < (ports.map Prod.snd).length := by rw [List.length_map, hPlen]; exact i.isLt
    have hj_m : j.val < (ports.map Prod.snd).length := by rw [List.length_map, hPlen]; exact j.isLt
    have hhi : Hlist[i.val]'(by rw [hH_len]; exact i.isLt) = dec4 (p + 2) hnp ((ports.map Prod.snd)[i.val]'hi_m) := by
      dsimp [Hlist]; simp
    have hhj : Hlist[j.val]'(by rw [hH_len]; exact j.isLt) = dec4 (p + 2) hnp ((ports.map Prod.snd)[j.val]'hj_m) := by
      dsimp [Hlist]; simp
    rw [hhi, hhj] at hc
    exact dec4_pairwise_indep (p + 2) hnp (ports.map Prod.snd) hpw hP_lt2 i.val j.val hi_m hj_m (fun h => hij (Fin.ext h)) hc
  refine
  { nB := baumertFactoredCard p Q - totalLen portsC
    nN := baumertFactoredCard p Q - (totalLen footAC + totalLen footDC)
    nA := totalLen footAC
    nD := totalLen footDC
    d  := totalLen portsC
    embB := fun i => Blist[i.val]'(by rw [hB_len]; exact i.isLt)
    embN := fun i => Nlist[i.val]'(by rw [hN_len]; exact i.isLt)
    embA := fun i => Alist[i.val]'(by rw [hA_len]; exact i.isLt)
    embD := fun i => Dlist[i.val]'(by rw [hD_len]; exact i.isLt)
    embO := fun i => Olist[i.val]'(by rw [hO_len]; exact i.isLt)
    embH := fun i => Hlist[i.val]'(by rw [hH_len]; exact i.isLt)
    embV := fun i => Olist[i.val]'(by rw [hO_len]; exact i.isLt)
    hB_indep := fun i j hij => hI_indep _ _ (hB_sub_I _ (List.getElem_mem _)) (hB_sub_I _ (List.getElem_mem _))
      (list_nodup_getElem_ne Blist hB_nodup i.val j.val (by rw [hB_len]; exact i.isLt) (by rw [hB_len]; exact j.isLt) (fun h => hij (Fin.ext h)))
    hN_indep := fun i j hij => hX_indep _ _ (hN_sub_X _ (List.getElem_mem _)) (hN_sub_X _ (List.getElem_mem _))
      (list_nodup_getElem_ne Nlist hN_nodup i.val j.val (by rw [hN_len]; exact i.isLt) (by rw [hN_len]; exact j.isLt) (fun h => hij (Fin.ext h)))
    hA_indep := fun i j hij => hX_indep _ _ (hA_sub_X _ (List.getElem_mem _)) (hA_sub_X _ (List.getElem_mem _))
      (list_nodup_getElem_ne Alist hA_nodup i.val j.val (by rw [hA_len]; exact i.isLt) (by rw [hA_len]; exact j.isLt) (fun h => hij (Fin.ext h)))
    hD_indep := fun i j hij => hX_indep _ _ (hD_sub_X _ (List.getElem_mem _)) (hD_sub_X _ (List.getElem_mem _))
      (list_nodup_getElem_ne Dlist hD_nodup i.val j.val (by rw [hD_len]; exact i.isLt) (by rw [hD_len]; exact j.isLt) (fun h => hij (Fin.ext h)))
    hO_indep := fun i j hij => hI_indep _ _ (hO_sub_I _ (List.getElem_mem _)) (hO_sub_I _ (List.getElem_mem _))
      (list_nodup_getElem_ne Olist hO_nodup i.val j.val (by rw [hO_len]; exact i.isLt) (by rw [hO_len]; exact j.isLt) (fun h => hij (Fin.ext h)))
    hH_indep := hH_indep_proof
    hV_indep := fun i j hij => hI_indep _ _ (hO_sub_I _ (List.getElem_mem _)) (hO_sub_I _ (List.getElem_mem _))
      (list_nodup_getElem_ne Olist hO_nodup i.val j.val (by rw [hO_len]; exact i.isLt) (by rw [hO_len]; exact j.isLt) (fun h => hij (Fin.ext h)))
    hBO := fun i j => hI_indep _ _ (hB_sub_I _ (List.getElem_mem _)) (hO_sub_I _ (List.getElem_mem _))
      (fun heq => hB_not_O (Blist[i.val]'(by rw [hB_len]; exact i.isLt)) (List.getElem_mem _) (by rw [heq]; exact List.getElem_mem _))
    hBH := fun i j hc =>
      hB_not_O (Blist[i.val]'(by rw [hB_len]; exact i.isLt)) (List.getElem_mem _)
        (by rw [hpriv_H j _ (hB_sub_I _ (List.getElem_mem _)) (conflict_symm _ hc)]; exact List.getElem_mem _)
    hBV := fun i j => hI_indep _ _ (hB_sub_I _ (List.getElem_mem _)) (hO_sub_I _ (List.getElem_mem _))
      (fun heq => hB_not_O (Blist[i.val]'(by rw [hB_len]; exact i.isLt)) (List.getElem_mem _) (by rw [heq]; exact List.getElem_mem _))
    hNA := fun i j => hX_indep _ _ (hN_sub_X _ (List.getElem_mem _)) (hA_sub_X _ (List.getElem_mem _))
      (fun heq => hN_not_A (Nlist[i.val]'(by rw [hN_len]; exact i.isLt)) (List.getElem_mem _) (by rw [heq]; exact List.getElem_mem _))
    hND := fun i j => hX_indep _ _ (hN_sub_X _ (List.getElem_mem _)) (hD_sub_X _ (List.getElem_mem _))
      (fun heq => hN_not_D (Nlist[i.val]'(by rw [hN_len]; exact i.isLt)) (List.getElem_mem _) (by rw [heq]; exact List.getElem_mem _))
    hNO := fun i j hc => hN_not_A _ (List.getElem_mem _) (hfoot_O j _ (hN_sub_X _ (List.getElem_mem _)) (conflict_symm _ hc))
    hNH := fun i j hc => hN_not_D _ (List.getElem_mem _) (hfoot_H j _ (hN_sub_X _ (List.getElem_mem _)) (conflict_symm _ hc))
    hNV := fun i j hc => hN_not_A _ (List.getElem_mem _) (hfoot_O j _ (hN_sub_X _ (List.getElem_mem _)) (conflict_symm _ hc))
    hAD := fun i j => hX_indep _ _ (hA_sub_X _ (List.getElem_mem _)) (hD_sub_X _ (List.getElem_mem _))
      (fun heq => by
        have hdisj := (List.nodup_append.mp hAD_nodup).2.2
        exact hdisj _ (List.getElem_mem _) _ (List.getElem_mem _) heq)
    hAH := fun i j hc => by
      have hD := hfoot_H j _ (hA_sub_X _ (List.getElem_mem _)) (conflict_symm _ hc)
      exact (List.nodup_append.mp hAD_nodup).2.2 _ (List.getElem_mem _) _ hD rfl
    hDV := fun i j hc => by
      have hA := hfoot_O j _ (hD_sub_X _ (List.getElem_mem _)) (conflict_symm _ hc)
      exact (List.nodup_append.mp hAD_nodup).2.2 _ hA _ (List.getElem_mem _) rfl }

theorem buildBaumertRichPortSystem_sz (p : Nat) (hp : 9 ≤ p)
    (Q : List (Nat × Nat)) (qMask : Nat → Nat)
    (s0 s1 s2 s3 : Nat)
    (portsC : List (List (Nat × Nat))) (footAC footDC : List (List Nat))
    (hQbd : checkQBoundB p Q = true)
    (hQind : checkQIndepB p Q = true)
    (hMask : checkQMaskEqB p Q qMask = true)
    (hCert : BaumertChunkCert p qMask ((p + 2) - s0 % (p + 2)) ((p + 2) - s1 % (p + 2))
               ((p + 2) - s2 % (p + 2)) ((p + 2) - s3 % (p + 2)) portsC footAC footDC)
    (c : Letter) :
    (buildBaumertRichPortSystem p hp Q qMask s0 s1 s2 s3 portsC footAC footDC hQbd hQind hMask hCert).toSepRealisation.sz c =
    match c with
    | .B => baumertFactoredCard p Q - totalLen portsC
    | .N => baumertFactoredCard p Q - (totalLen footAC + totalLen footDC)
    | .A => totalLen footAC
    | .D => totalLen footDC
    | .O => totalLen portsC
    | .H => totalLen portsC
    | .V => totalLen portsC := by
  cases c <;> rfl

/-! #### Bitmasks, Chunked Port Witnesses, and 28-Digit Certificates for `C₂₇` and `C₃₁` -/

def qMask25 : Nat → Nat
  | 0 => 16384 | 1 => 524288 | 2 => 8388676 | 3 => 1024 | 4 => 16384 | 5 => 262144
  | 6 => 8388612 | 7 => 1088 | 8 => 16384 | 9 => 262144 | 10 => 4194304 | 11 => 546
  | 12 => 8192 | 13 => 131072 | 14 => 2097152 | 15 => 273 | 16 => 4096 | 17 => 65536
  | 18 => 1048576 | 19 => 16777352 | 20 => 2048 | 21 => 32768 | 22 => 524288 | 23 => 8388676
  | 24 => 1024 | _ => 0

def qMask29 : Nat → Nat
  | 0 => 35651585 | 1 => 131072 | 2 => 8192 | 3 => 544 | 4 => 35651586 | 5 => 131072
  | 6 => 8192 | 7 => 544 | 8 => 71303170 | 9 => 262144 | 10 => 16384 | 11 => 1088
  | 12 => 142606340 | 13 => 524288 | 14 => 32768 | 15 => 1024 | 16 => 142606404 | 17 => 524288
  | 18 => 32768 | 19 => 2048 | 20 => 285212808 | 21 => 1048576 | 22 => 32768 | 23 => 2048
  | 24 => 285212808 | 25 => 1048576 | 26 => 65536 | 27 => 4096 | 28 => 272 | _ => 0

def ports27C : List (List (Nat × Nat)) := [
  [(39468, 39467), (39607, 39606), (40926, 40925), (41065, 41064), (41709, 41708), (41848, 41847), (42492, 42491), (42631, 42630), (43275, 43274), (43414, 43413), (44058, 44057), (44197, 44196)],
  [(44841, 44840), (44980, 44979), (45624, 45623), (45763, 45762), (46407, 46406), (46546, 46545), (47190, 47189), (47329, 47328), (47973, 47972), (48112, 48111), (48220, 48219), (48756, 48755)],
  [(49003, 49002), (49539, 49538), (49647, 49646), (49786, 49785), (50430, 50429), (50569, 50568), (51213, 51212), (51352, 51351), (51996, 51995), (52135, 52134), (52779, 52778), (52918, 52917)],
  [(53562, 53561), (53701, 53700), (54345, 54344), (54484, 54483), (55128, 55127), (55267, 55266), (55911, 55910), (56050, 56049), (56694, 56693), (56833, 56832), (56941, 56940), (57477, 57476)],
  [(57724, 57723), (58260, 58259), (58507, 58506), (59043, 59042), (276564, 276591), (20684, 20711), (49593, 49592), (56887, 56886), (237090, 237117), (473285, 473312), (512759, 512786), (1003, 1030)],
  [(20688, 20715), (40369, 40396), (60054, 60081), (79739, 79766), (99424, 99451), (119109, 119136), (138794, 138821), (158479, 158506), (178164, 178191), (197849, 197876), (217534, 217561), (237219, 237246)],
  [(256904, 256931), (276562, 276589), (296249, 296276), (315934, 315961), (335619, 335646), (355304, 355331), (374989, 375016), (394674, 394701), (414359, 414386), (434044, 434071), (453729, 453756), (473414, 473441)],
  [(493099, 493126), (512757, 512784), (39414, 39413), (20584, 20611)]
]

def footA27C : List (List Nat) := [
  [144, 248, 269, 1602, 1706, 1727, 19829, 19927, 19929, 19933, 21287, 21385, 21387, 21391, 39496, 39510],
  [39527, 39614, 39635, 40063, 40117, 40171, 40310, 40954, 40968, 41072, 41093, 41629, 41737, 41768, 41876, 42412],
  [42520, 42551, 42659, 43195, 43303, 43334, 43442, 43978, 44086, 44117, 44225, 44761, 44869, 44900, 45008, 45544],
  [45652, 45683, 45791, 46327, 46435, 46466, 46574, 47110, 47218, 47249, 47357, 47411, 47465, 47893, 48001, 48032],
  [48248, 48676, 48784, 48815, 48892, 48923, 49031, 49459, 49567, 49675, 49706, 49814, 50242, 50350, 50458, 50489],
  [50597, 51025, 51133, 51241, 51272, 51380, 51916, 52024, 52055, 52163, 52699, 52807, 52838, 52946, 53482, 53590],
  [53621, 53729, 54265, 54373, 54404, 54512, 55048, 55156, 55187, 55295, 55831, 55939, 55970, 56078, 56186, 56614],
  [56722, 56753, 56861, 56969, 57397, 57505, 57536, 57644, 57752, 58180, 58288, 58319, 58342, 58396, 58427, 58535],
  [58963, 59295, 59299, 60753, 60757, 78980, 78984, 80438, 80442, 98665, 98669, 100123, 100127, 118350, 118354, 119808],
  [119812, 138035, 138039, 139493, 139497, 157720, 157724, 159178, 159182, 177405, 177409, 178863, 178867, 197090, 197094, 198548],
  [198552, 216775, 216779, 218233, 218237, 236333, 236335, 236460, 236464, 237791, 237793, 237918, 237922, 256122, 256145, 257580],
  [257603, 275807, 275809, 275830, 277265, 277267, 277288, 295488, 295494, 296946, 296952, 315175, 315179, 316633, 316637, 334860],
  [334864, 336318, 336322, 354545, 354549, 356003, 356007, 374230, 374234, 375688, 375692, 393915, 393919, 395373, 395377, 413600],
  [413604, 415058, 415062, 433285, 433289, 434743, 434747, 452970, 452974, 454428, 454432, 472528, 472530, 472655, 472659, 473986],
  [473988, 474113, 474117, 492340, 492344, 493798, 493802, 512002, 512004, 512025, 513460, 513462, 513483]
]

def footD27C : List (List Nat) := [
  [954, 1055, 1057, 19783, 19922, 20458, 20639, 20742, 21241, 21380, 22024, 22163, 22807, 22946, 23590, 23729],
  [24373, 24512, 25156, 25295, 25939, 26078, 26722, 26861, 27505, 27644, 28288, 28427, 28535, 29071, 29318, 29854],
  [29908, 29962, 30101, 30745, 30884, 31528, 31667, 32311, 32450, 33094, 33233, 33877, 34016, 34660, 34799, 35443],
  [35582, 36226, 36365, 37009, 37148, 37202, 37256, 37792, 38039, 38575, 38683, 38822, 39358, 40320, 40421, 40423],
  [59149, 59288, 59824, 60108, 60607, 60746, 61390, 61529, 62173, 62312, 62956, 63095, 63739, 63878, 64522, 64661],
  [65305, 65444, 66088, 66227, 66871, 67010, 67654, 67793, 67901, 68437, 68684, 69220, 69274, 69328, 69467, 70111],
  [70250, 70894, 71033, 71677, 71816, 72460, 72599, 73243, 73382, 74026, 74165, 74809, 74948, 75592, 75731, 76375],
  [76514, 76568, 76622, 77158, 77405, 77941, 78049, 78188, 78724, 79793, 99478, 119163, 138848, 158533, 178218, 197903],
  [217588, 237143, 237145, 237273, 256958, 276616, 276618, 296303, 315988, 335673, 355358, 375043, 394728, 414413, 434098, 453783],
  [473338, 473340, 473468, 493130, 493153, 512811]
]

def ports31C : List (List (Nat × Nat)) := [
  [(30332, 30333), (30554, 30555), (32254, 32255), (32476, 32477), (33277, 33278), (33499, 33500), (34300, 34301), (34522, 34523), (35323, 35324), (35545, 35546), (35669, 35670), (36346, 36347)],
  [(36692, 36693), (37369, 37370), (37715, 37716), (38392, 38393), (38516, 38517), (38738, 38739), (39539, 39540), (39761, 39762), (40562, 40563), (40784, 40785), (41585, 41586), (41807, 41808)],
  [(42608, 42609), (42830, 42831), (43631, 43632), (43853, 43854), (44654, 44655), (44876, 44877), (45677, 45678), (45899, 45900), (46700, 46701), (46922, 46923), (47723, 47724), (47945, 47946)],
  [(48746, 48747), (48968, 48969), (49092, 49093), (49769, 49770), (50115, 50116), (50792, 50793), (51138, 51139), (51815, 51816), (52161, 52162), (52838, 52839), (52962, 52963), (53184, 53185)],
  [(53985, 53986), (54207, 54208), (55008, 55009), (55230, 55231), (56031, 56032), (56253, 56254), (57054, 57055), (57276, 57277), (58077, 58078), (58299, 58300), (59100, 59101), (59322, 59323)],
  [(508276, 508307), (567858, 567889), (31621, 31652), (38454, 38455), (49030, 49031), (91203, 91234), (150785, 150816), (418501, 418532), (835574, 835605), (1855, 1886), (1859, 1890), (31623, 31654)],
  [(31648, 31679), (61437, 61468), (61441, 61472), (91205, 91236), (91230, 91261), (120998, 121029), (121023, 121054), (150787, 150818), (150791, 150822), (180580, 180611), (180584, 180615), (210373, 210404)],
  [(210377, 210408), (240166, 240197), (240170, 240201), (269959, 269990), (269963, 269994), (299752, 299783), (299756, 299787), (329545, 329576), (329549, 329580), (359338, 359369), (359342, 359373), (389131, 389162)],
  [(389135, 389166), (418924, 418955), (418928, 418959), (448717, 448748), (448721, 448752), (478510, 478541), (478514, 478545), (508278, 508309), (508303, 508334), (538071, 538102), (538096, 538127), (567860, 567891)],
  [(567864, 567895), (597653, 597684), (597657, 597688), (627446, 627477), (627450, 627481), (657239, 657270), (657243, 657274), (687032, 687063), (687036, 687067), (716825, 716856), (716829, 716860), (746618, 746649)],
  [(746622, 746653), (776411, 776442), (776415, 776446), (806204, 806235), (806208, 806239), (835997, 836028), (836001, 836032), (865790, 865821), (865794, 865825), (895583, 895614), (895587, 895618), (30006, 30007)],
  [(61016, 61047)]
]

def footA31C : List (List Nat) := [
  [841, 862, 866, 2763, 2784, 2788, 30036, 30234, 30238, 30362, 30460, 30584, 30628, 30630, 30655, 30935],
  [31261, 31483, 32156, 32284, 32506, 32550, 32552, 32577, 33183, 33307, 33405, 33529, 34206, 34330, 34428, 34552],
  [34614, 34676, 35229, 35353, 35451, 35699, 36252, 36376, 36474, 36598, 36722, 37275, 37399, 37523, 37621, 37745],
  [38298, 38422, 38546, 38644, 38768, 39321, 39445, 39569, 39667, 39791, 40344, 40468, 40592, 40690, 40814, 41491],
  [41615, 41713, 41837, 42514, 42638, 42736, 42860, 43537, 43661, 43759, 43883, 44560, 44684, 44782, 44906, 45583],
  [45707, 45805, 45929, 46606, 46730, 46828, 46952, 47629, 47753, 47851, 47975, 48099, 48652, 48776, 48874, 48998],
  [49122, 49675, 49799, 49897, 50021, 50145, 50698, 50822, 50920, 51044, 51168, 51721, 51845, 51907, 51969, 52067],
  [52191, 52744, 52992, 53090, 53214, 53767, 53891, 54015, 54113, 54237, 54914, 55038, 55136, 55260, 55937, 56061],
  [56159, 56283, 56960, 57084, 57182, 57306, 57983, 58107, 58205, 58329, 58804, 59006, 59130, 59228, 59352, 60023],
  [60423, 60444, 60448, 61945, 62345, 62366, 62370, 89816, 90210, 90212, 90216, 90237, 91738, 92132, 92134, 92138],
  [92159, 120005, 120009, 120030, 121927, 121931, 121952, 149792, 149794, 149798, 149802, 151714, 151716, 151720, 151724, 179587],
  [179591, 179595, 181509, 181513, 181517, 209380, 209384, 209388, 211302, 211306, 211310, 239173, 239177, 239181, 241095, 241099],
  [241103, 268966, 268970, 268974, 270888, 270892, 270896, 298759, 298763, 298767, 300681, 300685, 300689, 328552, 328556, 328560],
  [330474, 330478, 330482, 358345, 358349, 358353, 360267, 360271, 360275, 388138, 388142, 388146, 390060, 390064, 390068, 417508],
  [417510, 417931, 417935, 417939, 419430, 419432, 419853, 419857, 419861, 447724, 447728, 447732, 449646, 449650, 449654, 477496],
  [477517, 477521, 479418, 479439, 479443, 507285, 507289, 507310, 507314, 509207, 509211, 509232, 509236, 537078, 537082, 537103],
  [539000, 539004, 539025, 566867, 566871, 566875, 566896, 568789, 568793, 568797, 568818, 596660, 596664, 596668, 598582, 598586],
  [598590, 626453, 626457, 626461, 628375, 628379, 628383, 656246, 656250, 656254, 658168, 658172, 658176, 686039, 686043, 686047],
  [687961, 687965, 687969, 715832, 715836, 715840, 717754, 717758, 717762, 745625, 745629, 745633, 747547, 747551, 747555, 775418],
  [775422, 775426, 777340, 777344, 777348, 805211, 805215, 805219, 807133, 807137, 807141, 834583, 834612, 835004, 835008, 835012],
  [836505, 836534, 836926, 836930, 836934, 864797, 864801, 864805, 866719, 866723, 866727, 894567, 894590, 894594, 896489, 896512],
  [896516]
]

def footD31C : List (List Nat) := [
  [217, 543, 765, 1116, 1892, 1917, 1921, 2465, 2687, 3488, 3710, 4511, 4733, 5534, 5756, 5880],
  [6557, 6903, 7580, 7926, 8603, 8665, 8727, 8949, 9750, 9972, 10773, 10995, 11796, 12018, 12819, 13041],
  [13842, 14064, 14865, 15087, 15888, 16110, 16911, 17133, 17934, 18156, 18957, 19179, 19241, 19303, 19980, 20326],
  [21003, 21349, 22026, 22372, 23049, 23173, 23395, 24196, 24418, 25219, 25441, 26242, 26464, 27265, 27487, 28288],
  [28510, 28985, 29311, 29533, 31288, 31685, 31710, 59799, 60125, 60347, 60698, 61077, 61474, 61499, 61503, 62047],
  [62269, 63070, 63292, 64093, 64315, 65116, 65338, 65462, 66139, 66485, 67162, 67508, 68185, 68247, 68309, 68531],
  [69332, 69554, 70355, 70577, 71378, 71600, 72401, 72623, 73424, 73646, 74447, 74669, 75470, 75692, 76493, 76715],
  [77516, 77738, 78539, 78761, 78823, 78885, 79562, 79908, 80585, 80931, 81608, 81954, 82631, 82755, 82977, 83778],
  [84000, 84801, 85023, 85824, 86046, 86847, 87069, 87870, 88092, 88567, 88893, 89115, 90870, 91267, 91292, 121056],
  [121060, 121085, 150849, 150853, 180638, 180642, 180646, 210435, 210439, 240228, 240232, 270021, 270025, 299814, 299818, 329607],
  [329611, 359400, 359404, 389193, 389197, 418562, 418564, 418986, 418990, 448779, 448783, 478572, 478576, 508338, 508340, 508365],
  [538133, 538158, 567920, 567922, 567926, 597715, 597719, 627508, 627512, 657301, 657305, 687094, 687098, 716887, 716891, 746680],
  [746684, 776473, 776477, 806266, 806270, 835637, 835666, 836059, 836063, 865852, 865856, 895645, 895649]
]

theorem qMask25_eq_ok : checkQMaskEqB 25 q25HBPZ qMask25 = true := by decide
theorem qMask29_eq_ok : checkQMaskEqB 29 q29HBPZ qMask29 = true := by decide

theorem cert27_Asort : strictSortedChunksAux 0 footA27C = true := by decide
theorem cert27_Dsort : strictSortedChunksAux 0 footD27C = true := by decide
theorem cert27_ADdisj : disjointChunksB footA27C footD27C = true := by decide
theorem cert27_Onodup : checkPairwiseChunks (fun a b => a.1 != b.1) ports27C = true := by decide
theorem cert27_Hindep : checkPairwiseChunks (fun a b => !conflictCodeB 27 a.2 b.2) ports27C = true := by decide
theorem cert27_Pbd : allChunks (fun pr => pr.1 < 27 * 27 * 27 * 27 && pr.2 < 27 * 27 * 27 * 27 && inMaskHBPZ 25 qMask25 pr.1) ports27C = true := by decide
theorem cert27_Abd : allChunks (fun c => c < 27 * 27 * 27 * 27 && inMaskHBPZ 25 qMask25 (unshiftCode 27 27 1 1 26 c)) footA27C = true := by decide
theorem cert27_Dbd : allChunks (fun c => c < 27 * 27 * 27 * 27 && inMaskHBPZ 25 qMask25 (unshiftCode 27 27 1 1 26 c)) footD27C = true := by decide
theorem cert27_Priv : allChunks (fun pr => check81Ball4 27 (fun x0 x1 x2 x3 => !inMaskHBPZ4 25 qMask25 x0 x1 x2 x3 || ((((x0 * 27 + x1) * 27 + x2) * 27 + x3) == pr.1)) pr.2) ports27C = true := by decide
theorem cert27_Acomp : allChunks (fun pr => check81Ball4 27 (fun x0 x1 x2 x3 => !inMaskHBPZ4 25 qMask25 ((x0 + 27) % 27) ((x1 + 1) % 27) ((x2 + 1) % 27) ((x3 + 26) % 27) || elemSortedChunks (((x0 * 27 + x1) * 27 + x2) * 27 + x3) footA27C) pr.1) ports27C = true := by decide
theorem cert27_Dcomp : allChunks (fun pr => check81Ball4 27 (fun x0 x1 x2 x3 => !inMaskHBPZ4 25 qMask25 ((x0 + 27) % 27) ((x1 + 1) % 27) ((x2 + 1) % 27) ((x3 + 26) % 27) || elemSortedChunks (((x0 * 27 + x1) * 27 + x2) * 27 + x3) footD27C) pr.2) ports27C = true := by decide

theorem cert27_ok : BaumertChunkCert 25 qMask25 27 1 1 26 ports27C footA27C footD27C :=
  ⟨cert27_Asort, cert27_Dsort, cert27_ADdisj, cert27_Onodup, cert27_Hindep,
   cert27_Pbd, cert27_Abd, cert27_Dbd, cert27_Priv, cert27_Acomp, cert27_Dcomp⟩

theorem cert31_Asort : strictSortedChunksAux 0 footA31C = true := by decide
theorem cert31_Dsort : strictSortedChunksAux 0 footD31C = true := by decide
theorem cert31_ADdisj : disjointChunksB footA31C footD31C = true := by decide
theorem cert31_Onodup : checkPairwiseChunks (fun a b => a.1 != b.1) ports31C = true := by decide
theorem cert31_Hindep : checkPairwiseChunks (fun a b => !conflictCodeB 31 a.2 b.2) ports31C = true := by decide
theorem cert31_Pbd : allChunks (fun pr => pr.1 < 31 * 31 * 31 * 31 && pr.2 < 31 * 31 * 31 * 31 && inMaskHBPZ 29 qMask29 pr.1) ports31C = true := by decide
theorem cert31_Abd : allChunks (fun c => c < 31 * 31 * 31 * 31 && inMaskHBPZ 29 qMask29 (unshiftCode 31 31 1 1 1 c)) footA31C = true := by decide
theorem cert31_Dbd : allChunks (fun c => c < 31 * 31 * 31 * 31 && inMaskHBPZ 29 qMask29 (unshiftCode 31 31 1 1 1 c)) footD31C = true := by decide
theorem cert31_Priv : allChunks (fun pr => check81Ball4 31 (fun x0 x1 x2 x3 => !inMaskHBPZ4 29 qMask29 x0 x1 x2 x3 || ((((x0 * 31 + x1) * 31 + x2) * 31 + x3) == pr.1)) pr.2) ports31C = true := by decide
theorem cert31_Acomp : allChunks (fun pr => check81Ball4 31 (fun x0 x1 x2 x3 => !inMaskHBPZ4 29 qMask29 ((x0 + 31) % 31) ((x1 + 1) % 31) ((x2 + 1) % 31) ((x3 + 1) % 31) || elemSortedChunks (((x0 * 31 + x1) * 31 + x2) * 31 + x3) footA31C) pr.1) ports31C = true := by decide
theorem cert31_Dcomp : allChunks (fun pr => check81Ball4 31 (fun x0 x1 x2 x3 => !inMaskHBPZ4 29 qMask29 ((x0 + 31) % 31) ((x1 + 1) % 31) ((x2 + 1) % 31) ((x3 + 1) % 31) || elemSortedChunks (((x0 * 31 + x1) * 31 + x2) * 31 + x3) footD31C) pr.2) ports31C = true := by decide

theorem cert31_ok : BaumertChunkCert 29 qMask29 31 1 1 1 ports31C footA31C footD31C :=
  ⟨cert31_Asort, cert31_Dsort, cert31_ADdisj, cert31_Onodup, cert31_Hindep,
   cert31_Pbd, cert31_Abd, cert31_Dbd, cert31_Priv, cert31_Acomp, cert31_Dcomp⟩

/-! #### 28-Digit Monotone Certificates for `C₂₇` (`p = 2048`) and `C₃₁` (`p = 2048`) -/

def lo_c27_0 : Letter → Nat
  | .B => 31378 | .N => 31079 | .A => 237 | .D => 150 | .O => 88 | .H => 88 | .V => 88
def lo_c27_1 : Letter → Nat
  | .B => 984646996 | .N => 966054010 | .A => 12027573 | .D => 12027573
  | .O => 5469904 | .H => 5469904 | .V => 5469904
def lo_c27_2 : Letter → Nat
  | .B => 969792865410475984 | .N => 933839000286161416 | .A => 23238570254435460 | .D => 23238570254435460
  | .O => 10568445387030080 | .H => 10568445387030080 | .V => 10568445387030080
def lo_c27_3 : Letter → Nat
  | .B => 9414805840434882377214767591 | .N => 8742154030453387114344235692
  | .A => 434021664289634754015294630  | .D => 434021664289634754015294630
  | .O => 197384529496061283479823914  | .H => 197384529496061283479823914 | .V => 197384529496061283479823914
def lo_c27_4 : Letter → Nat
  | .B => 8898124566107439996701409743 | .N => 7717875631246337852528976561
  | .A => 758856848354743476395605348  | .D => 758856848354743476395605348
  | .O => 345113192016627524148905790  | .H => 345113192016627524148905790 | .V => 345113192016627524148905790
def lo_c27_5 : Letter → Nat
  | .B => 8022418683084225082425766956 | .N => 6186905912456563452638562572
  | .A => 1171352555504294457226096191 | .D => 1171352555504294457226096191
  | .O => 532708138937353551606700074  | .H => 532708138937353551606700074 | .V => 532708138937353551606700074
def lo_c27_6 : Letter → Nat
  | .B => 6685515768622765555625914557 | .N => 4376607200673574690144401922
  | .A => 1449409610244124857159801964 | .D => 1449409610244124857159801964
  | .O => 659163026881049030646318203  | .H => 659163026881049030646318203 | .V => 659163026881049030646318203
def lo_c27_7 : Letter → Nat
  | .B => 4851770999601964319492577034 | .N => 2755784346205988738999796180
  | .A => 1268699307383983247331413116 | .D => 1268699307383983247331413116
  | .O => 576979529973077652533149115  | .H => 576979529973077652533149115 | .V => 576979529973077652533149115

def lo_c31_0 : Letter → Nat
  | .B => 54780 | .N => 54371 | .A => 337 | .D => 205 | .O => 133 | .H => 133 | .V => 133
def lo_c31_1 : Letter → Nat
  | .B => 3000992572 | .N => 2956499405 | .A => 29469082 | .D => 29469082
  | .O => 14462686 | .H => 14462686 | .V => 14462686
def lo_c31_2 : Letter → Nat
  | .B => 9007661225517872192 | .N => 8744362438941044921 | .A => 174250646797792420 | .D => 174250646797792420
  | .O => 85517845107403660 | .H => 85517845107403660 | .V => 85517845107403660
def lo_c31_3 : Letter → Nat
  | .B => 8119756691298900921499324235 | .N => 7658532761520077558722883788
  | .A => 304742162163959740983829486  | .D => 304742162163959740983829486
  | .O => 149559806523271754800181998  | .H => 149559806523271754800181998 | .V => 149559806523271754800181998
def lo_c31_4 : Letter → Nat
  | .B => 6611275744114417629571170369 | .N => 5902459520087780570844520311
  | .A => 466775566549829977909579567  | .D => 466775566549829977909579567
  | .O => 229081735613016188420568568  | .H => 229081735613016188420568568 | .V => 229081735613016188420568568
def lo_c31_5 : Letter → Nat
  | .B => 4413668599242358250994786846 | .N => 3571054610438653195046159613
  | .A => 551024777305282266636361213  | .D => 551024777305282266636361213
  | .O => 270429134249455872555852549  | .H => 270429134249455872555852549 | .V => 270429134249455872555852549
def lo_c31_6 : Letter → Nat
  | .B => 2007652311784466761976568707 | .N => 1396694425155250478844968439
  | .A => 393547914292392078947517510  | .D => 393547914292392078947517510
  | .O => 193143441331690577490848075  | .H => 193143441331690577490848075 | .V => 193143441331690577490848075
def lo_c31_7 : Letter → Nat
  | .B => 4334712598994881021629396292 | .N => 2570275160635323507848121590
  | .A => 1099332355847320677444980085 | .D => 1099332355847320677444980085
  | .O => 539524735526544834318016051  | .H => 539524735526544834318016051 | .V => 539524735526544834318016051

/-- **Theorem T2b (`C₂₇` World Record: `Θ(C₂₇) ≥ 13.319390984674515`).** -/
theorem t2b_c27_world_record :
    ∃ M : Nat, HasIndepSetOfSize (strongPow (cycleGraph 27) 2048) M ∧
      13319390984674515 ^ 2048 ≤ M * (10 ^ 15) ^ 2048 := by
  let S27 := buildBaumertRichPortSystem 25 (by decide) q25HBPZ qMask25 0 26 26 1 ports27C footA27C footD27C
    q25_bound_ok q25_indep_ok qMask25_eq_ok cert27_ok
  let R0 := S27.toSepRealisation
  let R1 := repackSep (a := 4)   (b := 2) (by decide) (liftT2a R0)
  let R2 := repackSep (a := 8)   (b := 2) (by decide) (liftT2a R1)
  let R3 := repackSep (a := 16)  (b := 2) (by decide) (liftT2a R2)
  let R4 := repackSep (a := 32)  (b := 2) (by decide) (liftT2a R3)
  let R5 := repackSep (a := 64)  (b := 2) (by decide) (liftT2a R4)
  let R6 := repackSep (a := 128) (b := 2) (by decide) (liftT2a R5)
  let R7 := repackSep (a := 256) (b := 2) (by decide) (liftT2a R6)
  have hM : HasIndepSetOfSize (strongPow (cycleGraph 27) 2048) (sumListSizes codeC4a (tupleSz R7.sz 4)) :=
    hasIndepSet_repackPow (cycleGraph 27) 512 4 _ (by decide) (liftC4a R7)
  have h0 : ∀ c, lo_c27_0 c * 10 ^ 0 ≤ R0.sz c := by
    intro c; dsimp only [R0, S27]; rw [buildBaumertRichPortSystem_sz]; cases c <;> decide
  have h1 := stepLo_tbl tblT2a lo_c27_0 lo_c27_1 R0.sz 0   0  0   (by decide) h0 (by intro c; cases c <;> decide)
  have h2 := stepLo_tbl tblT2a lo_c27_1 lo_c27_2 R1.sz 0   0  0   (by decide) h1 (by intro c; cases c <;> decide)
  have h3 := stepLo_tbl tblT2a lo_c27_2 lo_c27_3 R2.sz 0   8  8   (by decide) h2 (by intro c; cases c <;> decide)
  have h4 := stepLo_tbl tblT2a lo_c27_3 lo_c27_4 R3.sz 8   28 44  (by decide) h3 (by intro c; cases c <;> decide)
  have h5 := stepLo_tbl tblT2a lo_c27_4 lo_c27_5 R4.sz 44  28 116 (by decide) h4 (by intro c; cases c <;> decide)
  have h6 := stepLo_tbl tblT2a lo_c27_5 lo_c27_6 R5.sz 116 28 260 (by decide) h5 (by intro c; cases c <;> decide)
  have h7 := stepLo_tbl tblT2a lo_c27_6 lo_c27_7 R6.sz 260 28 548 (by decide) h6 (by intro c; cases c <;> decide)
  have hM_lo : sumListSizes codeC4a (tupleSz lo_c27_7 4) * 10 ^ 2192 ≤ sumListSizes codeC4a (tupleSz R7.sz 4) :=
    stepFinal_code codeC4a lo_c27_7 R7.sz 548 2192 (by decide) h7
  have hu0  := powLe_base 13319390984674515
  have hu1  := powLe_sq hu0  (sh := 25) (by decide) (U' := 1774061762026287462756004905) (by decide)
  have hu2  := powLe_sq hu1  (sh := 27) (by decide) (U' := 3147295135483815808991545907) (by decide)
  have hu3  := powLe_sq hu2  (sh := 27) (by decide) (U' := 9905466669840090508984441116) (by decide)
  have hu4  := powLe_sq hu3  (sh := 28) (by decide) (U' := 9811826994731293263308300510) (by decide)
  have hu5  := powLe_sq hu4  (sh := 28) (by decide) (U' := 9627194897453772199945225522) (by decide)
  have hu6  := powLe_sq hu5  (sh := 28) (by decide) (U' := 9268288159355994742463218686) (by decide)
  have hu7  := powLe_sq hu6  (sh := 28) (by decide) (U' := 8590116540485853299360294074) (by decide)
  have hu8  := powLe_sq hu7  (sh := 28) (by decide) (U' := 7379010217912864452593292052) (by decide)
  have hu9  := powLe_sq hu8  (sh := 28) (by decide) (U' := 5444979179606245933467734991) (by decide)
  have hu10 := powLe_sq hu9  (sh := 28) (by decide) (U' := 2964779826634550701153800673) (by decide)
  have hu11 := powLe_sq hu10 (sh := 27) (by decide) (U' := 8789919420419196511112540910) (by decide)
  exact ⟨sumListSizes codeC4a (tupleSz R7.sz 4), hM,
    powLe_finish (powLe_cast_p (p' := 2048) (by decide) hu11) hM_lo (by decide) (by decide)⟩

/-- **Theorem T2d (`C₃₁` World Record: `Θ(C₃₁) ≥ 15.308776193986504`).** -/
theorem t2d_c31_world_record :
    ∃ M : Nat, HasIndepSetOfSize (strongPow (cycleGraph 31) 2048) M ∧
      15308776193986504 ^ 2048 ≤ M * (10 ^ 15) ^ 2048 := by
  let S31 := buildBaumertRichPortSystem 29 (by decide) q29HBPZ qMask29 0 30 30 30 ports31C footA31C footD31C
    q29_bound_ok q29_indep_ok qMask29_eq_ok cert31_ok
  let R0 := S31.toSepRealisation
  let R1 := repackSep (a := 4)   (b := 2) (by decide) (liftT2a R0)
  let R2 := repackSep (a := 8)   (b := 2) (by decide) (liftT2a R1)
  let R3 := repackSep (a := 16)  (b := 2) (by decide) (liftT2a R2)
  let R4 := repackSep (a := 32)  (b := 2) (by decide) (liftT2a R3)
  let R5 := repackSep (a := 64)  (b := 2) (by decide) (liftT2a R4)
  let R6 := repackSep (a := 128) (b := 2) (by decide) (liftT2a R5)
  let R7 := repackSep (a := 256) (b := 2) (by decide) (liftT2a R6)
  have hM : HasIndepSetOfSize (strongPow (cycleGraph 31) 2048) (sumListSizes codeC4a (tupleSz R7.sz 4)) :=
    hasIndepSet_repackPow (cycleGraph 31) 512 4 _ (by decide) (liftC4a R7)
  have h0 : ∀ c, lo_c31_0 c * 10 ^ 0 ≤ R0.sz c := by
    intro c; dsimp only [R0, S31]; rw [buildBaumertRichPortSystem_sz]; cases c <;> decide
  have h1 := stepLo_tbl tblT2a lo_c31_0 lo_c31_1 R0.sz 0   0  0   (by decide) h0 (by intro c; cases c <;> decide)
  have h2 := stepLo_tbl tblT2a lo_c31_1 lo_c31_2 R1.sz 0   0  0   (by decide) h1 (by intro c; cases c <;> decide)
  have h3 := stepLo_tbl tblT2a lo_c31_2 lo_c31_3 R2.sz 0   10 10  (by decide) h2 (by intro c; cases c <;> decide)
  have h4 := stepLo_tbl tblT2a lo_c31_3 lo_c31_4 R3.sz 10  28 48  (by decide) h3 (by intro c; cases c <;> decide)
  have h5 := stepLo_tbl tblT2a lo_c31_4 lo_c31_5 R4.sz 48  28 124 (by decide) h4 (by intro c; cases c <;> decide)
  have h6 := stepLo_tbl tblT2a lo_c31_5 lo_c31_6 R5.sz 124 28 276 (by decide) h5 (by intro c; cases c <;> decide)
  have h7 := stepLo_tbl tblT2a lo_c31_6 lo_c31_7 R6.sz 276 27 579 (by decide) h6 (by intro c; cases c <;> decide)
  have hM_lo : sumListSizes codeC4a (tupleSz lo_c31_7 4) * 10 ^ 2316 ≤ sumListSizes codeC4a (tupleSz R7.sz 4) :=
    stepFinal_code codeC4a lo_c31_7 R7.sz 579 2316 (by decide) h7
  have hu0  := powLe_base 15308776193986504
  have hu1  := powLe_sq hu0  (sh := 25) (by decide) (U' := 2343586285575679111489717342) (by decide)
  have hu2  := powLe_sq hu1  (sh := 27) (by decide) (U' := 5492396677938408565827981402) (by decide)
  have hu3  := powLe_sq hu2  (sh := 28) (by decide) (U' := 3016642126782886650712449225) (by decide)
  have hu4  := powLe_sq hu3  (sh := 27) (by decide) (U' := 9100129721081177577457355998) (by decide)
  have hu5  := powLe_sq hu4  (sh := 28) (by decide) (U' := 8281236094050499081160351966) (by decide)
  have hu6  := powLe_sq hu5  (sh := 28) (by decide) (U' := 6857887124540476646324043437) (by decide)
  have hu7  := powLe_sq hu6  (sh := 28) (by decide) (U' := 4703061581293804704358883385) (by decide)
  have hu8  := powLe_sq hu7  (sh := 28) (by decide) (U' := 2211878823744178279586097658) (by decide)
  have hu9  := powLe_sq hu8  (sh := 27) (by decide) (U' := 4892407930927929683859926542) (by decide)
  have hu10 := powLe_sq hu9  (sh := 28) (by decide) (U' := 2393565536260650598845844875) (by decide)
  have hu11 := powLe_sq hu10 (sh := 27) (by decide) (U' := 5729155976374735876738290074) (by decide)
  exact ⟨sumListSizes codeC4a (tupleSz R7.sz 4), hM,
    powLe_finish (powLe_cast_p (p' := 2048) (by decide) hu11) hM_lo (by decide) (by decide)⟩

end
end ZeroErrorFrontier.WorldRecords
