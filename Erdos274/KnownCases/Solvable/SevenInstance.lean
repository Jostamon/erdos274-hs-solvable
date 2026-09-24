/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.SevenClosure
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The `p = 7` instance of the apex-charging criterion

`DECISION_LOG` D98 §14.  The coordinates are the primes `q = (2, 3, 5, 7)` of
`|G|`, with ratios `r_q = 1/q`, so that `w(v(d)) = 1/d`.

* `j` is the prime `7`, with the exact-7 shift `δ₇`.
* `i` is the prime `2`, with the exact-8 shift `t·δ₂`, where
  `t = ord₇(2) = 3` (`orderOf_two`).
* `F` holds the other cyclotomic witnesses `ord₇(3)·δ₃` and `ord₇(5)·δ₅`,
  both of length `6` (`orderOf_three`, `orderOf_five`).

No constant is an input.  `Π = W(ℕ⁴) = ∏ q/(q−1) = 35/8` comes from
`ExpWeight.W_univ_fin`, and `a = 1/7`, `b = 1/8`, `γ = 1/2 + 1/4`, and
`ε = 3⁻⁶ + 5⁻⁶` from the ratios and the orders.  `seven` feeds the
group-theoretic hypotheses into `SevenClosure.closure_ineq` and shows that
its conclusion fails.  The inequality it contradicts is
`2b + 1 + Πab² + Πab ≤ Π(ab + b² + a + b + ε)`, which reads
`1.3379 ≤ 1.3246`.
-/

namespace Erdos274

namespace SevenInstance

open Set ExpWeight ApexCharging SevenClosure
open scoped ENNReal NNReal

/-- The multiplicative orders modulo `7` that fix the witness lengths. -/
theorem orderOf_two : orderOf (2 : ZMod 7) = 3 :=
  orderOf_eq_prime_pow (p := 3) (n := 0) (by decide) (by decide) |>.trans (by norm_num)

theorem orderOf_three : orderOf (3 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

theorem orderOf_five : orderOf (5 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

/-- The primes of `|G|`, in coordinate order. -/
def q : Fin 4 → ℕ := ![2, 3, 5, 7]

/-- The ratios `1/q` as `ℝ≥0`. -/
noncomputable def rN (k : Fin 4) : ℝ≥0 := (q k : ℝ≥0)⁻¹

/-- The ratios `1/q` as `ℝ≥0∞`. -/
noncomputable def r (k : Fin 4) : ℝ≥0∞ := (rN k : ℝ≥0∞)

theorem q_pos (k : Fin 4) : 2 ≤ q k := by fin_cases k <;> decide

theorem rN_lt_one (k : Fin 4) : rN k < 1 := by
  rw [rN]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (q_pos k))

theorem r_ne_top (k : Fin 4) : r k ≠ ⊤ := ENNReal.coe_ne_top

theorem r_ne_zero (k : Fin 4) : r k ≠ 0 := by
  rw [r, ENNReal.coe_ne_zero, rN]
  exact inv_ne_zero (by exact_mod_cast (by have := q_pos k; omega : q k ≠ 0))

/-- `Π = W(ℕ⁴)` as an `ℝ≥0`: `∏ (1 − 1/q)⁻¹`. -/
noncomputable def PiN : ℝ≥0 := ∏ k, (1 - rN k)⁻¹

theorem W_univ_eq : W r univ = (PiN : ℝ≥0∞) := by
  rw [W_univ_fin, PiN, ENNReal.ofNNReal_finsetProd]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have h1 : (1 : ℝ≥0) - rN k ≠ 0 := (tsub_pos_of_lt (rN_lt_one k)).ne'
  rw [r, ← ENNReal.coe_one, ← ENNReal.coe_sub, ← ENNReal.coe_inv h1]

theorem PiN_real : (PiN : ℝ) = 35 / 8 := by
  have hsub : ∀ k, ((1 - rN k : ℝ≥0) : ℝ) = 1 - (q k : ℝ)⁻¹ := fun k ↦ by
    rw [NNReal.coe_sub (rN_lt_one k).le]
    simp [rN]
  rw [PiN, NNReal.coe_prod]
  simp only [NNReal.coe_inv, hsub, Fin.prod_univ_four, q]
  norm_num

theorem rN_real (k : Fin 4) : (rN k : ℝ) = (q k : ℝ)⁻¹ := by simp [rN]

/-- **The residual `p = 7` configuration of step 4 does not exist.**  The
hypotheses are those `closure_ineq` needs, at the `p = 7` data. -/
theorem seven {κ : Type*} {t t₃ t₅ : ℕ}
    (ht : t = orderOf (2 : ZMod 7)) (ht₃ : t₃ = orderOf (3 : ZMod 7))
    (ht₅ : t₅ = orderOf (5 : ZMod 7))
    {H₀ A B : Finset (Fin 4 → ℕ)} (hH₀ : IsAntichain (· ≤ ·) (H₀ : Set (Fin 4 → ℕ)))
    (hne : H₀.Nonempty)
    {J J₇₈ : Finset κ} (hJ : J₇₈ ⊆ J) (hd l : κ → Fin 4 → ℕ)
    (hhd : ∀ p ∈ J, hd p ∈ up (H₀ : Set (Fin 4 → ℕ)))
    (hCB : ∀ p ∈ J, Pi.single 3 1 ≤ l p ∨ Pi.single 0 t ≤ l p ∨
      ∃ f ∈ ({Pi.single 1 t₃, Pi.single 2 t₅} : Finset (Fin 4 → ℕ)), f ≤ l p)
    (h78 : ∀ p ∈ J₇₈, Pi.single 3 1 ≤ l p ∨ Pi.single 0 t ≤ l p)
    (hinj : Set.InjOn (fun p ↦ hd p + l p) J)
    (hA : ∀ p ∈ J, hd p ∈ H₀ → l p = Pi.single 3 1 → hd p ∈ A)
    (hB : ∀ p ∈ J, hd p ∈ H₀ → l p = Pi.single 0 t → hd p ∈ B)
    (ν a₇ a₈ : ℝ≥0∞)
    (hν : ν ≤ ∑ p ∈ J, w r (hd p + l p))
    (ha : a₇ + a₈ ≤ ∑ p ∈ J₇₈, w r (hd p + l p))
    (hLO : W r (up (H₀ : Set (Fin 4 → ℕ))) ≤ W r univ * ν)
    (hLOA : W r (up (A : Set (Fin 4 → ℕ))) ≤ W r univ * a₇)
    (hLOB : W r (up (B : Set (Fin 4 → ℕ))) ≤ W r univ * a₈) : False := by
  rw [orderOf_two] at ht
  rw [orderOf_three] at ht₃
  rw [orderOf_five] at ht₅
  subst ht ht₃ ht₅
  have hPm : W r univ ≠ ⊤ := by rw [W_univ_eq]; exact ENNReal.coe_ne_top
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  have hγ1 : ∑ m ∈ Finset.Ico 1 3, r 0 ^ m ≤ 1 := by
    rw [hIco, Finset.sum_pair (by norm_num), r, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
      ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast [rN_real]
    norm_num [q]
  have hγ : r 0 ^ 3 ≤ r 3 * r 0 ^ 3 + r 3 * ∑ m ∈ Finset.Ico 1 3, r 0 ^ m := by
    rw [hIco, Finset.sum_pair (by norm_num)]
    simp only [r, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_add, ENNReal.coe_le_coe,
      ← NNReal.coe_le_coe]
    push_cast [rN_real]
    norm_num [q]
  have hmain := closure_ineq (r := r) r_ne_top r_ne_zero hPm (i := 0) (j := 3) (by decide)
    (t := 3) (by norm_num) ({Pi.single 1 6, Pi.single 2 6}) hH₀ hne hJ hd l hhd hCB h78 hinj
    hA hB ν a₇ a₈ hν ha hLO hLOA hLOB hγ1 hγ
  have hF : ∑ f ∈ ({Pi.single 1 6, Pi.single 2 6} : Finset (Fin 4 → ℕ)), w r f
      = r 1 ^ 6 + r 2 ^ 6 := by
    rw [Finset.sum_pair (fun h ↦ by simpa using congrFun h 1), w_single, w_single]
  rw [hF, W_univ_eq] at hmain
  simp only [r, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_add, ← ENNReal.coe_one,
    ← ENNReal.coe_ofNat, ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hmain
  push_cast [rN_real, PiN_real] at hmain
  norm_num [q] at hmain

end SevenInstance

end Erdos274
