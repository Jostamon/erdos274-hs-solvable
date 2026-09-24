/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.SevenClosure
import Erdos274.KnownCases.Solvable.DivisorWeight
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime

/-!
# The `p = 7` instance of the apex-charging criterion

`DECISION_LOG` D98 §14.  The coordinates are the primes `q = (2, 3, 5, 7)` of
`|G|`, with the ratios `1/q` of `DivisorWeight.ratio`, so that `w(v(d)) = 1/d`.

* `j` is the prime `7`, with the exact-7 shift `δ₇`.
* `i` is the prime `2`, with the exact-8 shift `t·δ₂`, where
  `t = ord₇(2) = 3` (`orderOf_two`).
* `F` holds the other cyclotomic witnesses `ord₇(3)·δ₃` and `ord₇(5)·δ₅`,
  both of length `6` (`orderOf_three`, `orderOf_five`).

No constant is an input.  `Π = W(ℕ⁴) = ∏ q/(q−1) = 35/8` comes from
`DivisorWeight.W_univ_ratio`, and `a = 1/7`, `b = 1/8`, `γ = 1/2 + 1/4`, and
`ε = 3⁻⁶ + 5⁻⁶` from the ratios and the orders.  `seven` feeds the
group-theoretic hypotheses into `SevenClosure.closure_ineq` and shows that
its conclusion fails.  The inequality it contradicts is
`2b + 1 + Πab² + Πab ≤ Π(ab + b² + a + b + ε)`, which reads
`1.3379 ≤ 1.3246`.
-/

namespace Erdos274

namespace SevenInstance

open Set ExpWeight ApexCharging SevenClosure DivisorWeight
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

theorem q_prime (k : Fin 4) : (q k).Prime := by
  fin_cases k <;> norm_num [q]

theorem q_injective : Function.Injective q := fun a b h ↦ by
  fin_cases a <;> fin_cases b <;> simp_all [q]

theorem PiN_real : (PiN q : ℝ) = 35 / 8 := by
  rw [PiN, NNReal.coe_prod]
  simp only [NNReal.coe_inv, coe_one_sub_ratioN q_prime, Fin.prod_univ_four]
  norm_num [q]

theorem ratioN_real (k : Fin 4) : (ratioN q k : ℝ) = (q k : ℝ)⁻¹ := by simp [ratioN]

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
    (hν : ν ≤ ∑ p ∈ J, w (ratio q) (hd p + l p))
    (ha : a₇ + a₈ ≤ ∑ p ∈ J₇₈, w (ratio q) (hd p + l p))
    (hLO : W (ratio q) (up (H₀ : Set (Fin 4 → ℕ))) ≤ W (ratio q) univ * ν)
    (hLOA : W (ratio q) (up (A : Set (Fin 4 → ℕ))) ≤ W (ratio q) univ * a₇)
    (hLOB : W (ratio q) (up (B : Set (Fin 4 → ℕ))) ≤ W (ratio q) univ * a₈) : False := by
  rw [orderOf_two] at ht
  rw [orderOf_three] at ht₃
  rw [orderOf_five] at ht₅
  subst ht ht₃ ht₅
  have hWu : W (ratio q) univ = (PiN q : ℝ≥0∞) := W_univ_ratio q_prime
  have hPm : W (ratio q) univ ≠ ⊤ := by rw [hWu]; exact ENNReal.coe_ne_top
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  have hγ1 : ∑ m ∈ Finset.Ico 1 3, ratio q 0 ^ m ≤ 1 := by
    rw [hIco, Finset.sum_pair (by norm_num), ratio, ← ENNReal.coe_pow, ← ENNReal.coe_pow,
      ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast [ratioN_real]
    norm_num [q]
  have hγ : ratio q 0 ^ 3 ≤
      ratio q 3 * ratio q 0 ^ 3 + ratio q 3 * ∑ m ∈ Finset.Ico 1 3, ratio q 0 ^ m := by
    rw [hIco, Finset.sum_pair (by norm_num)]
    simp only [ratio, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_add,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast [ratioN_real]
    norm_num [q]
  have hmain := closure_ineq (r := ratio q) ratio_ne_top (ratio_ne_zero q_prime) hPm (i := 0)
    (j := 3) (by decide) (t := 3) (by norm_num) ({Pi.single 1 6, Pi.single 2 6}) hH₀ hne hJ
    hd l hhd hCB h78 hinj hA hB ν a₇ a₈ hν ha hLO hLOA hLOB hγ1 hγ
  have hF : ∑ f ∈ ({Pi.single 1 6, Pi.single 2 6} : Finset (Fin 4 → ℕ)), w (ratio q) f
      = ratio q 1 ^ 6 + ratio q 2 ^ 6 := by
    rw [Finset.sum_pair (fun h ↦ by simpa using congrFun h 1), w_single, w_single]
  rw [hF, hWu] at hmain
  simp only [ratio, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_add, ← ENNReal.coe_one,
    ← ENNReal.coe_ofNat, ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hmain
  push_cast [ratioN_real, PiN_real] at hmain
  norm_num [q] at hmain

end SevenInstance

end Erdos274
