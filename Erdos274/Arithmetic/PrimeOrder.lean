/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon, Claude Opus 5
-/
import Erdos274.Arithmetic.Efficiency
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.FieldTheory.Finite.Basic

/-!
# `Π_p` and `S_p` from the multiplicative order

`SOLVABLE_HS_TRACK.md` §9.22 addendum 2.  The coupled criterion (CE′) is
stated in two constants,

    Π_p = ∏_{q < p} q/(q−1),      S_p = ∑_{q < p} q^{−ord_p q},

where `ord_p q` is the multiplicative order of `q` modulo `p`.  This file
defines both and evaluates them at every prime `5 ≤ p ≤ 31`.

Until now `CoupledCriterion.lean` carried those two numbers as *displayed
rationals*: `cePrime_eleven` asserted an inequality between `35/8` and
`1/180` and said nothing about `Π₁₁` or `S₁₁`.  The identification was prose.
Here `ordMod` is `orderOf` in `ZMod p`, so the order facts are kernel-checked
by `decide`, and `piBelow`/`sOrd` are the constants themselves.

For `p ≤ 13` the displayed `Π_p` is exact; for `p ≥ 17` it is a strict upper
bound, which is what `CoupledCriterion.coupledCriterion_of_Pi_le` consumes.
`S_p` is exact at `p = 5, 7` and bounded above elsewhere.

`Nat.primesBelow` is Mathlib's; `mertensProd` is `Arithmetic/Efficiency.lean`'s.

No research axiom occurs in this file.
-/

namespace Erdos274

namespace PrimeOrder

open Finset

/-! ### Definitions -/

/-- `ord_p q`: the multiplicative order of `q` modulo `p`. -/
noncomputable def ordMod (p q : ℕ) : ℕ := orderOf (q : ZMod p)

/-- `Π_p = ∏_{q < p} q/(q−1)`, over the primes `q < p`. -/
noncomputable def piBelow (p : ℕ) : ℚ := mertensProd p.primesBelow

/-- `S_p = ∑_{q < p} q^{−ord_p q}`, over the primes `q < p`. -/
noncomputable def sOrd (p : ℕ) : ℚ := ∑ q ∈ p.primesBelow, ((q : ℚ) ^ ordMod p q)⁻¹

/-- `S_p⁽²⁾ = ∑_{q < p} q^{−2·ord_p q}`, the second moment. -/
noncomputable def sOrdSq (p : ℕ) : ℚ :=
  ∑ q ∈ p.primesBelow, ((q : ℚ) ^ (2 * ordMod p q))⁻¹

/-- `λ_p = ∏_{q < p} q/(q+1)`, the down-set constant of (DL). -/
noncomputable def lambdaBelow (p : ℕ) : ℚ := ∏ q ∈ p.primesBelow, (q : ℚ) / (q + 1)

/-- `τ_p = S_p − λ_p·S_p⁽²⁾`, the tail constant of (EUC). -/
noncomputable def tauOrd (p : ℕ) : ℚ := sOrd p - lambdaBelow p * sOrdSq p

theorem piBelow_def (p : ℕ) : piBelow p = mertensProd p.primesBelow := rfl

theorem sOrd_def (p : ℕ) :
    sOrd p = ∑ q ∈ p.primesBelow, ((q : ℚ) ^ ordMod p q)⁻¹ := rfl

theorem sOrdSq_def (p : ℕ) :
    sOrdSq p = ∑ q ∈ p.primesBelow, ((q : ℚ) ^ (2 * ordMod p q))⁻¹ := rfl

theorem lambdaBelow_def (p : ℕ) :
    lambdaBelow p = ∏ q ∈ p.primesBelow, (q : ℚ) / (q + 1) := rfl

theorem sOrd_nonneg (p : ℕ) : 0 ≤ sOrd p :=
  Finset.sum_nonneg fun q _ ↦ inv_nonneg.mpr (by positivity)

theorem sOrdSq_nonneg (p : ℕ) : 0 ≤ sOrdSq p :=
  Finset.sum_nonneg fun q _ ↦ inv_nonneg.mpr (by positivity)

theorem piBelow_nonneg (p : ℕ) : 0 ≤ piBelow p :=
  mertensProd_nonneg fun _ hq ↦ Nat.prime_of_mem_primesBelow hq

/-! ### The order is positive, and how to pin it down -/

/-- `ord_p q > 0` whenever `q` is a unit mod the prime `p`: its order divides
`p − 1 ≠ 0` by Fermat. -/
theorem ordMod_pos {p q : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) : 0 < ordMod p q := by
  have : Fact p.Prime := ⟨hp⟩
  have hne : (q : ZMod p) ≠ 0 := fun h ↦ hq ((ZMod.natCast_eq_zero_iff q p).mp h)
  have hdvd : ordMod p q ∣ p - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hne)
  have h2 := hp.two_le
  rcases Nat.eq_zero_or_pos (ordMod p q) with h0 | h
  · rw [h0] at hdvd
    have := Nat.eq_zero_of_zero_dvd hdvd
    omega
  · exact h

theorem ordMod_pos_of_mem {p q : ℕ} (hp : p.Prime) (hq : q ∈ p.primesBelow) :
    0 < ordMod p q := by
  refine ordMod_pos hp fun hdvd ↦ ?_
  have hqp : q < p := Nat.lt_of_mem_primesBelow hq
  have hq0 : 0 < q := (Nat.prime_of_mem_primesBelow hq).pos
  have := Nat.le_of_dvd hq0 hdvd
  omega

/-- `ord_p q = k`, in the form `decide` discharges for literal `p`, `q`, `k`. -/
theorem ordMod_eq_of {p q k : ℕ} (hk : 0 < k) (h1 : (q : ZMod p) ^ k = 1)
    (h2 : ∀ m, m < k → 0 < m → (q : ZMod p) ^ m ≠ 1) : ordMod p q = k :=
  (orderOf_eq_iff hk).mpr ⟨h1, h2⟩

/-- A lower bound on every order gives an upper bound on `S_p`.  Useful when
the exact orders are not worth carrying: only `k q ≤ ord_p q` is needed. -/
theorem sOrd_le_sum {p : ℕ} (k : ℕ → ℕ) (hk : ∀ q ∈ p.primesBelow, k q ≤ ordMod p q) :
    sOrd p ≤ ∑ q ∈ p.primesBelow, ((q : ℚ) ^ k q)⁻¹ := by
  refine Finset.sum_le_sum fun q hq ↦ ?_
  have hq0 : (0 : ℚ) < (q : ℚ) := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow hq).pos
  have h1 : (1 : ℚ) ≤ (q : ℚ) := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow hq).one_lt.le
  have hle : (q : ℚ) ^ k q ≤ (q : ℚ) ^ ordMod p q := pow_le_pow_right₀ h1 (hk q hq)
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  exact hle

/-! ### The bridge to `M_G′`

`MassForm.MG G p` is `mertensProd` over the primes of `|G|` other than `p`.
When `p` is the largest prime divisor of `|G|` that set sits inside the primes
below `p`, so `M_G′ ≤ Π_p`: this is what lets a criterion stated in `Π_p` be
applied to `M_G′`. -/

theorem mertensProd_le_piBelow {p : ℕ} {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime)
    (hlt : ∀ q ∈ Q, q < p) : mertensProd Q ≤ piBelow p :=
  mertensProd_le_of_subset (fun _ hq ↦ Nat.prime_of_mem_primesBelow hq)
    (fun q hq ↦ Nat.mem_primesBelow.mpr ⟨hlt q hq, hQ q hq⟩)

/-! ### `p = 5` -/

theorem primesBelow_five : Nat.primesBelow 5 = {2, 3} := by decide

theorem ordMod_five_two : ordMod 5 2 = 4 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_five_three : ordMod 5 3 = 4 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_five : piBelow 5 = 3 := by
  simp only [piBelow_def, primesBelow_five, mertensProd]
  norm_num

/-- `S₅ = 1/16 + 1/81 = 97/1296`, exactly the constant of `cePrime_five`. -/
theorem sOrd_five : sOrd 5 = 97 / 1296 := by
  simp only [sOrd_def, primesBelow_five]
  norm_num [ordMod_five_two, ordMod_five_three]

/-! ### `p = 7` -/

theorem primesBelow_seven : Nat.primesBelow 7 = {2, 3, 5} := by decide

theorem ordMod_seven_two : ordMod 7 2 = 3 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_seven_three : ordMod 7 3 = 6 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_seven_five : ordMod 7 5 = 6 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_seven : piBelow 7 = 15 / 4 := by
  simp only [piBelow_def, primesBelow_seven, mertensProd]
  norm_num

/-- `S₇ = 1/8 + 1/729 + 1/15625`, exactly the constant of `not_cePrime_seven`
and of `eucCriterion_seven`. -/
theorem sOrd_seven : sOrd 7 = 1 / 8 + 1 / 729 + 1 / 15625 := by
  simp only [sOrd_def, primesBelow_seven]
  norm_num [ordMod_seven_two, ordMod_seven_three, ordMod_seven_five]

/-- `λ₇ = (2/3)(3/4)(5/6) = 5/12`, the down-set constant at `p = 7`. -/
theorem lambdaBelow_seven : lambdaBelow 7 = 5 / 12 := by
  simp only [lambdaBelow_def, primesBelow_seven]
  norm_num

/-- `S₇⁽²⁾ = 1/64 + 1/531441 + 1/244140625`. -/
theorem sOrdSq_seven : sOrdSq 7 = 1 / 64 + 1 / 531441 + 1 / 244140625 := by
  simp only [sOrdSq_def, primesBelow_seven]
  norm_num [ordMod_seven_two, ordMod_seven_three, ordMod_seven_five]

/-- `τ₇ ≤ S₇ − 5/768`: the bound `eucCriterion_seven` is stated with, obtained
by keeping only the `q = 2` term `2⁻⁶` of `S₇⁽²⁾` and `λ₇ = 5/12`. -/
theorem tauOrd_seven_le : tauOrd 7 ≤ sOrd 7 - 5 / 768 := by
  rw [tauOrd, lambdaBelow_seven, sOrdSq_seven]
  have h : (5 : ℚ) / 768 ≤ 5 / 12 * (1 / 64 + 1 / 531441 + 1 / 244140625) := by norm_num
  linarith

/-! ### `p = 11` -/

theorem primesBelow_eleven : Nat.primesBelow 11 = {2, 3, 5, 7} := by decide

theorem ordMod_eleven_two : ordMod 11 2 = 10 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_eleven_three : ordMod 11 3 = 5 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_eleven_five : ordMod 11 5 = 5 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_eleven_seven : ordMod 11 7 = 10 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_eleven : piBelow 11 = 35 / 8 := by
  simp only [piBelow_def, primesBelow_eleven, mertensProd]
  norm_num

/-- `S₁₁ < 1/180`, the constant of `cePrime_eleven`. -/
theorem sOrd_eleven_le : sOrd 11 ≤ 1 / 180 := by
  simp only [sOrd_def, primesBelow_eleven]
  norm_num [ordMod_eleven_two, ordMod_eleven_three, ordMod_eleven_five,
    ordMod_eleven_seven]

/-! ### `p = 13` -/

theorem primesBelow_thirteen : Nat.primesBelow 13 = {2, 3, 5, 7, 11} := by decide

theorem ordMod_thirteen_two : ordMod 13 2 = 12 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirteen_three : ordMod 13 3 = 3 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirteen_five : ordMod 13 5 = 4 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirteen_seven : ordMod 13 7 = 12 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirteen_eleven : ordMod 13 11 = 12 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_thirteen : piBelow 13 = 77 / 16 := by
  simp only [piBelow_def, primesBelow_thirteen, mertensProd]
  norm_num

/-- `S₁₃ < 389/10000`, the constant of `cePrime_thirteen`.  This is the prime
where the uncoupled criterion (CE) fails, so the margin matters. -/
theorem sOrd_thirteen_le : sOrd 13 ≤ 389 / 10000 := by
  simp only [sOrd_def, primesBelow_thirteen]
  norm_num [ordMod_thirteen_two, ordMod_thirteen_three, ordMod_thirteen_five,
    ordMod_thirteen_seven, ordMod_thirteen_eleven]

/-! ### `p = 17`

From here on the displayed `Π_p` of the (CE′) table is a strict upper bound,
not the exact product: `Π₁₇ = 1001/192 < 21/4`. -/

theorem primesBelow_seventeen : Nat.primesBelow 17 = {2, 3, 5, 7, 11, 13} := by decide

theorem ordMod_seventeen_two : ordMod 17 2 = 8 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_seventeen_three : ordMod 17 3 = 16 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_seventeen_five : ordMod 17 5 = 16 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_seventeen_seven : ordMod 17 7 = 16 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_seventeen_eleven : ordMod 17 11 = 16 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_seventeen_thirteen : ordMod 17 13 = 4 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_seventeen : piBelow 17 = 1001 / 192 := by
  simp only [piBelow_def, primesBelow_seventeen, mertensProd]
  norm_num

theorem piBelow_seventeen_le : piBelow 17 ≤ 21 / 4 := by
  rw [piBelow_seventeen]; norm_num

/-- `S₁₇ < 1/250`, the constant of `cePrime_seventeen`. -/
theorem sOrd_seventeen_le : sOrd 17 ≤ 1 / 250 := by
  simp only [sOrd_def, primesBelow_seventeen]
  norm_num [ordMod_seventeen_two, ordMod_seventeen_three, ordMod_seventeen_five,
    ordMod_seventeen_seven, ordMod_seventeen_eleven, ordMod_seventeen_thirteen]

/-! ### `p = 19` -/

theorem primesBelow_nineteen : Nat.primesBelow 19 = {2, 3, 5, 7, 11, 13, 17} := by decide

theorem ordMod_nineteen_two : ordMod 19 2 = 18 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_nineteen_three : ordMod 19 3 = 18 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_nineteen_five : ordMod 19 5 = 9 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_nineteen_seven : ordMod 19 7 = 3 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_nineteen_eleven : ordMod 19 11 = 3 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_nineteen_thirteen : ordMod 19 13 = 18 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_nineteen_seventeen : ordMod 19 17 = 9 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_nineteen : piBelow 19 = 17017 / 3072 := by
  simp only [piBelow_def, primesBelow_nineteen, mertensProd]
  norm_num

theorem piBelow_nineteen_le : piBelow 19 ≤ 28 / 5 := by
  rw [piBelow_nineteen]; norm_num

/-- `S₁₉ < 1/270`, the constant of `cePrime_nineteen`.  The two small orders
`ord₁₉ 7 = ord₁₉ 11 = 3` carry almost all of the mass. -/
theorem sOrd_nineteen_le : sOrd 19 ≤ 1 / 270 := by
  simp only [sOrd_def, primesBelow_nineteen]
  norm_num [ordMod_nineteen_two, ordMod_nineteen_three, ordMod_nineteen_five,
    ordMod_nineteen_seven, ordMod_nineteen_eleven, ordMod_nineteen_thirteen,
    ordMod_nineteen_seventeen]

/-! ### `p = 23` -/

theorem primesBelow_twentythree :
    Nat.primesBelow 23 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide

theorem ordMod_twentythree_two : ordMod 23 2 = 11 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentythree_three : ordMod 23 3 = 11 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentythree_five : ordMod 23 5 = 22 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentythree_seven : ordMod 23 7 = 22 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentythree_eleven : ordMod 23 11 = 22 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentythree_thirteen : ordMod 23 13 = 11 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentythree_seventeen : ordMod 23 17 = 22 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentythree_nineteen : ordMod 23 19 = 22 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_twentythree : piBelow 23 = 323323 / 55296 := by
  simp only [piBelow_def, primesBelow_twentythree, mertensProd]
  norm_num

theorem piBelow_twentythree_le : piBelow 23 ≤ 59 / 10 := by
  rw [piBelow_twentythree]; norm_num

/-- `S₂₃ < 1/2000`, the constant of `cePrime_twentythree`. -/
theorem sOrd_twentythree_le : sOrd 23 ≤ 1 / 2000 := by
  simp only [sOrd_def, primesBelow_twentythree]
  norm_num [ordMod_twentythree_two, ordMod_twentythree_three, ordMod_twentythree_five,
    ordMod_twentythree_seven, ordMod_twentythree_eleven, ordMod_twentythree_thirteen,
    ordMod_twentythree_seventeen, ordMod_twentythree_nineteen]

/-! ### `p = 29` -/

theorem primesBelow_twentynine :
    Nat.primesBelow 29 = {2, 3, 5, 7, 11, 13, 17, 19, 23} := by decide

theorem ordMod_twentynine_two : ordMod 29 2 = 28 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentynine_three : ordMod 29 3 = 28 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentynine_five : ordMod 29 5 = 14 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentynine_seven : ordMod 29 7 = 7 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentynine_eleven : ordMod 29 11 = 28 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentynine_thirteen : ordMod 29 13 = 14 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentynine_seventeen : ordMod 29 17 = 4 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentynine_nineteen : ordMod 29 19 = 28 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_twentynine_twentythree : ordMod 29 23 = 7 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_twentynine : piBelow 29 = 676039 / 110592 := by
  simp only [piBelow_def, primesBelow_twentynine, mertensProd]
  norm_num

theorem piBelow_twentynine_le : piBelow 29 ≤ 31 / 5 := by
  rw [piBelow_twentynine]; norm_num

/-- `S₂₉ < 1/70000`, the constant of `cePrime_twentynine`.  `ord₂₉ 17 = 4` is
the smallest order in the range and supplies most of the mass. -/
theorem sOrd_twentynine_le : sOrd 29 ≤ 1 / 70000 := by
  simp only [sOrd_def, primesBelow_twentynine]
  norm_num [ordMod_twentynine_two, ordMod_twentynine_three, ordMod_twentynine_five,
    ordMod_twentynine_seven, ordMod_twentynine_eleven, ordMod_twentynine_thirteen,
    ordMod_twentynine_seventeen, ordMod_twentynine_nineteen,
    ordMod_twentynine_twentythree]

/-! ### `p = 31` -/

theorem primesBelow_thirtyone :
    Nat.primesBelow 31 = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29} := by decide

theorem ordMod_thirtyone_two : ordMod 31 2 = 5 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_three : ordMod 31 3 = 30 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_five : ordMod 31 5 = 3 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_seven : ordMod 31 7 = 15 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_eleven : ordMod 31 11 = 30 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_thirteen : ordMod 31 13 = 30 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_seventeen : ordMod 31 17 = 30 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_nineteen : ordMod 31 19 = 15 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_twentythree : ordMod 31 23 = 10 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem ordMod_thirtyone_twentynine : ordMod 31 29 = 10 :=
  ordMod_eq_of (by norm_num) (by decide) (by decide)

theorem piBelow_thirtyone : piBelow 31 = 2800733 / 442368 := by
  simp only [piBelow_def, primesBelow_thirtyone, mertensProd]
  norm_num

theorem piBelow_thirtyone_le : piBelow 31 ≤ 317 / 50 := by
  rw [piBelow_thirtyone]; norm_num

/-- `S₃₁ < 1/32 + 1/125 + 1/7000`, the constant of `cePrime_thirtyone`.  The
two small orders here are `ord₃₁ 2 = 5` and `ord₃₁ 5 = 3`, giving the leading
`1/32 + 1/125`; the remaining eight orders are all at least `10`. -/
theorem sOrd_thirtyone_le : sOrd 31 ≤ 1 / 32 + 1 / 125 + 1 / 7000 := by
  simp only [sOrd_def, primesBelow_thirtyone]
  norm_num [ordMod_thirtyone_two, ordMod_thirtyone_three, ordMod_thirtyone_five,
    ordMod_thirtyone_seven, ordMod_thirtyone_eleven, ordMod_thirtyone_thirteen,
    ordMod_thirtyone_seventeen, ordMod_thirtyone_nineteen,
    ordMod_thirtyone_twentythree, ordMod_thirtyone_twentynine]

end PrimeOrder

end Erdos274
