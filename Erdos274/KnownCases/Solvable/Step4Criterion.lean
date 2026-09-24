/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.Arithmetic.PrimeOrder
import Mathlib.Tactic.NormNum.Prime

/-!
# The step-4 criterion `Π_p·(S_p + 1/(p−1)) < 1`: every prime `p ≥ 5` but `7`

`Step4Closure.false_of_covering` refutes a covering at `p` once
`Π_p·(S_p + 1/(p−1)) < 1` (`step4Crit`).  This file proves that, for a prime
`p ≥ 5`, the criterion holds **exactly** when `p ≠ 7`
(`step4Crit_iff_ne_seven`), with no Mertens estimate.  The failure at `7`
(`not_step4Crit_seven`) is what makes the separate `p = 7` closure necessary.

* `p ≤ 31`: the order table of `PrimeOrder`.
* `37 ≤ p ≤ 251`: one exact certificate per range, with the order-free bound
  `S_p ≤ ∑_{q<p} min(q⁻², (p+1)⁻¹)` (`PrimeOrder.sOrd_le_rangeBound`), as in
  `CELargePrimes`.
* `p ≥ tailStart²`: **the wheel-6 bounds**, proved by induction over blocks
  of six.  Every prime `q ≥ 5` is `6m ± 1`, so
  - `Π_p³ ≤ Π₈³(2p + 17)/17` (`mertensProd_wheel`), because the pair factor
    `f(m) = (6m−1)(6m+1)/((6m−2)·6m)` has `f(m)³ ≤ (12m+5)/(12m−7)`, which
    telescopes from `M = 1`, where the bound is an equality;
  - there are at most `2M + 2` primes below `6M + 2` (`card_primesBelow_le`);
  - `∑_{q ≥ 6m+5} q⁻² ≤ 1/(9(2m+1))` (`tail_sum_le`), because
    `(6M+5)⁻² + (6M+7)⁻² ≤ (1/(2M+1) − 1/(2M+3))/9`, which telescopes.

  Splitting `S_p` at `6m+5` with `m = ⌊√p⌋/6` gives
  `t·(S_p + 1/(p−1)) ≤ tailBound t` for `t = ⌊√p⌋`; `tailBound` and
  `(2(t+1)² + 17)/t³` decrease, so everything is controlled by one inequality
  at `t = tailStart` (`tail_closes`).

**Where the numbers come from.**  In the tail, every constant is a definition
evaluated (`Π₈ = piBelow 8`, `tailBound tailStart`) or comes from a telescoping
identity; the only chosen number is `tailStart`, the point where the tail takes
over from the ranges, and it enters only through `tail_closes`.  Below it the
work is finite and cannot be made uniform: the criterion **fails** at `p = 7`,
and at `p = 37` it holds with a margin of about 1% (`DECISION_LOG` D94, D95),
which no elementary bound on `Π_p` reaches.  The order table and the range
certificates are that finite part.  The range endpoints only partition
`[37, tailStart²)` into pieces on which one certificate closes; no statement
depends on them.
-/

namespace Erdos274

namespace Step4Criterion

open Finset PrimeOrder

/-- **The step-4 criterion** at `p`. -/
def step4Crit (p : ℕ) : Prop := piBelow p * (sOrd p + 1 / ((p : ℚ) - 1)) < 1

theorem step4Crit_of_bounds {p : ℕ} (hp : 2 ≤ p) {C S : ℚ} (hC : piBelow p ≤ C)
    (hS : sOrd p ≤ S) (h : C * (S + 1 / ((p : ℚ) - 1)) < 1) : step4Crit p := by
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp
    linarith
  have h0 : 0 ≤ sOrd p + 1 / ((p : ℚ) - 1) := by
    have := sOrd_nonneg p
    positivity
  refine lt_of_le_of_lt ?_ h
  exact mul_le_mul hC (by linarith) h0 ((piBelow_nonneg p).trans hC)

/-! ### `p ≤ 31` -/

theorem step4Crit_of_le_thirtyone {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h31 : p ≤ 31)
    (h7 : p ≠ 7) : step4Crit p := by
  interval_cases p
  · exact step4Crit_of_bounds (by norm_num) piBelow_five.le sOrd_five.le (by norm_num)
  · norm_num at hp
  · exact absurd rfl h7
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · exact step4Crit_of_bounds (by norm_num) piBelow_eleven.le sOrd_eleven_le (by norm_num)
  · norm_num at hp
  · exact step4Crit_of_bounds (by norm_num) piBelow_thirteen.le sOrd_thirteen_le (by norm_num)
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · exact step4Crit_of_bounds (by norm_num) piBelow_seventeen_le sOrd_seventeen_le
      (by norm_num)
  · norm_num at hp
  · exact step4Crit_of_bounds (by norm_num) piBelow_nineteen_le sOrd_nineteen_le (by norm_num)
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · exact step4Crit_of_bounds (by norm_num) piBelow_twentythree_le sOrd_twentythree_le
      (by norm_num)
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · exact step4Crit_of_bounds (by norm_num) piBelow_twentynine_le sOrd_twentynine_le
      (by norm_num)
  · norm_num at hp
  · exact step4Crit_of_bounds (by norm_num) piBelow_thirtyone_le sOrd_thirtyone_le
      (by norm_num)

/-! ### Ranges -/

/-- **One certificate for a range**: `Π_b·(rangeBound a b + 1/(a−1)) < 1`
gives the criterion at every prime in `[a, b]`. -/
theorem step4Crit_of_range {a b p : ℕ} (hp : p.Prime) (ha : 2 ≤ a) (hap : a ≤ p) (hpb : p ≤ b)
    (h : piBelow b * (rangeBound a b + 1 / ((a : ℚ) - 1)) < 1) : step4Crit p := by
  refine step4Crit_of_bounds (ha.trans hap) (piBelow_mono hpb) (sOrd_le_rangeBound hp hap hpb)
    (lt_of_le_of_lt ?_ h)
  have ha1 : (0 : ℚ) < (a : ℚ) - 1 := by
    have : (2 : ℚ) ≤ a := by exact_mod_cast ha
    linarith
  have hap' : (a : ℚ) - 1 ≤ (p : ℚ) - 1 := by
    have : (a : ℚ) ≤ p := by exact_mod_cast hap
    linarith
  have hinv : 1 / ((p : ℚ) - 1) ≤ 1 / ((a : ℚ) - 1) := one_div_le_one_div_of_le ha1 hap'
  have := rangeBound_nonneg a b
  have := piBelow_nonneg b
  gcongr

private theorem primesBelow_37 :
    Nat.primesBelow 37 = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by decide

private theorem primesBelow_43 :
    Nat.primesBelow 43 = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} := by decide

private theorem primesBelow_61 :
    Nat.primesBelow 61 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59} := by decide

private theorem primesBelow_97 :
    Nat.primesBelow 97 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89} := by decide

private theorem primesBelow_251 :
    Nat.primesBelow 251 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
        157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
        239, 241} := by decide +kernel

private theorem crit_37 {p : ℕ} (hp : p.Prime) (h1 : 37 ≤ p) (h2 : p ≤ 37) :
    step4Crit p := by
  refine step4Crit_of_range hp (by norm_num) h1 h2 ?_
  simp only [piBelow_def, rangeBound_def, primesBelow_37, mertensProd]
  norm_num [min_def]

private theorem crit_41 {p : ℕ} (hp : p.Prime) (h1 : 41 ≤ p) (h2 : p ≤ 43) :
    step4Crit p := by
  refine step4Crit_of_range hp (by norm_num) h1 h2 ?_
  simp only [piBelow_def, rangeBound_def, primesBelow_43, mertensProd]
  norm_num [min_def]

private theorem crit_47 {p : ℕ} (hp : p.Prime) (h1 : 47 ≤ p) (h2 : p ≤ 61) :
    step4Crit p := by
  refine step4Crit_of_range hp (by norm_num) h1 h2 ?_
  simp only [piBelow_def, rangeBound_def, primesBelow_61, mertensProd]
  norm_num [min_def]

private theorem crit_67 {p : ℕ} (hp : p.Prime) (h1 : 67 ≤ p) (h2 : p ≤ 97) :
    step4Crit p := by
  refine step4Crit_of_range hp (by norm_num) h1 h2 ?_
  simp only [piBelow_def, rangeBound_def, primesBelow_97, mertensProd]
  norm_num [min_def]

private theorem crit_101 {p : ℕ} (hp : p.Prime) (h1 : 101 ≤ p) (h2 : p ≤ 251) :
    step4Crit p := by
  refine step4Crit_of_range hp (by norm_num) h1 h2 ?_
  simp only [piBelow_def, rangeBound_def, primesBelow_251, mertensProd]
  norm_num [min_def]

/-- **The criterion at every prime `37 ≤ p ≤ 255`**: no prime lies in
`(37, 41)`, `(43, 47)`, `(61, 67)`, `(97, 101)` or `(251, 255]`. -/
theorem step4Crit_of_mid {p : ℕ} (hp : p.Prime) (h37 : 37 ≤ p) (h255 : p ≤ 255) :
    step4Crit p := by
  rcases le_or_gt p 37 with h | h
  · exact crit_37 hp h37 h
  rcases le_or_gt p 43 with h' | h'
  · refine crit_41 hp ?_ h'
    rcases Nat.lt_or_ge p 41 with hlt | hge
    · interval_cases p <;> norm_num at hp
    · exact hge
  rcases le_or_gt p 61 with h'' | h''
  · refine crit_47 hp ?_ h''
    rcases Nat.lt_or_ge p 47 with hlt | hge
    · interval_cases p <;> norm_num at hp
    · exact hge
  rcases le_or_gt p 97 with h₃ | h₃
  · refine crit_67 hp ?_ h₃
    rcases Nat.lt_or_ge p 67 with hlt | hge
    · interval_cases p <;> norm_num at hp
    · exact hge
  rcases le_or_gt p 251 with h₄ | h₄
  · refine crit_101 hp ?_ h₄
    rcases Nat.lt_or_ge p 101 with hlt | hge
    · interval_cases p <;> norm_num at hp
    · exact hge
  · interval_cases p <;> norm_num at hp

/-! ### The wheel -/

/-- The primes in a block of six above `5` are `6M+5` and `6M+7`. -/
theorem filter_primesBelow_step (M c : ℕ) (hc : 5 ≤ c) :
    ((6 * (M + 1) + 2).primesBelow.filter (c ≤ ·)) ⊆
      ((6 * M + 2).primesBelow.filter (c ≤ ·)) ∪ {6 * M + 5, 6 * M + 7} := by
  intro q hq
  obtain ⟨hq1, hcq⟩ := Finset.mem_filter.mp hq
  obtain ⟨hlt, hqp⟩ := Nat.mem_primesBelow.mp hq1
  by_cases hq2 : q < 6 * M + 2
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨hq2, hqp⟩, hcq⟩)
  refine Finset.mem_union_right _ ?_
  have hcases : q = 6 * M + 2 ∨ q = 6 * M + 3 ∨ q = 6 * M + 4 ∨ q = 6 * M + 5 ∨
      q = 6 * M + 6 ∨ q = 6 * M + 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hqp (Nat.not_prime_of_dvd_of_lt (m := 2) ⟨3 * M + 1, by ring⟩ le_rfl (by omega))
  · exact absurd hqp
      (Nat.not_prime_of_dvd_of_lt (m := 3) ⟨2 * M + 1, by ring⟩ (by norm_num) (by omega))
  · exact absurd hqp (Nat.not_prime_of_dvd_of_lt (m := 2) ⟨3 * M + 2, by ring⟩ le_rfl (by omega))
  · simp
  · exact absurd hqp (Nat.not_prime_of_dvd_of_lt (m := 2) ⟨3 * M + 3, by ring⟩ le_rfl (by omega))
  · simp

theorem primesBelow_step (M : ℕ) (hM : 1 ≤ M) :
    (6 * (M + 1) + 2).primesBelow ⊆ (6 * M + 2).primesBelow ∪ {6 * M + 5, 6 * M + 7} := by
  intro q hq
  have hq5 : 5 ≤ q ∨ q < 5 := by omega
  rcases hq5 with h5 | h5
  · have := filter_primesBelow_step M 5 le_rfl (Finset.mem_filter.mpr ⟨hq, h5⟩)
    rcases Finset.mem_union.mp this with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mp h).1
    · exact Finset.mem_union_right _ h
  · refine Finset.mem_union_left _ (Nat.mem_primesBelow.mpr
      ⟨by omega, (Nat.mem_primesBelow.mp hq).2⟩)

/-- **At most `2M + 2` primes below `6M + 2`.** -/
theorem card_primesBelow_le (M : ℕ) (hM : 1 ≤ M) :
    ((6 * M + 2).primesBelow).card ≤ 2 * M + 2 := by
  induction M, hM using Nat.le_induction with
  | base => decide
  | succ M hM ih =>
    calc ((6 * (M + 1) + 2).primesBelow).card
        ≤ ((6 * M + 2).primesBelow ∪ {6 * M + 5, 6 * M + 7}).card :=
          Finset.card_le_card (primesBelow_step M hM)
      _ ≤ ((6 * M + 2).primesBelow).card + ({6 * M + 5, 6 * M + 7} : Finset ℕ).card :=
          Finset.card_union_le _ _
      _ ≤ 2 * M + 2 + 2 := by
          gcongr
          exact Finset.card_le_two
      _ = 2 * (M + 1) + 2 := by ring

/-- A product of factors `q/(q−1) ≥ 1` over a larger set is larger. -/
theorem mertensProd_le_of_subset_two_le {Q Q' : Finset ℕ} (hQ' : ∀ q ∈ Q', 2 ≤ q)
    (hsub : Q ⊆ Q') : mertensProd Q ≤ mertensProd Q' := by
  have hf : ∀ q ∈ Q', 1 ≤ (q : ℚ) / (q - 1) := by
    intro q hq
    have h2 : (2 : ℚ) ≤ q := by exact_mod_cast hQ' q hq
    rw [le_div_iff₀ (by linarith)]
    linarith
  unfold mertensProd
  rw [← Finset.prod_sdiff hsub]
  have h1 : 1 ≤ ∏ q ∈ Q' \ Q, (q : ℚ) / (q - 1) :=
    Finset.prod_induction _ (fun x : ℚ ↦ 1 ≤ x)
      (fun a b ha hb ↦ one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      fun q hq ↦ hf q (Finset.mem_sdiff.mp hq).1
  have h0 : 0 ≤ ∏ q ∈ Q, (q : ℚ) / (q - 1) :=
    Finset.prod_nonneg fun q hq ↦ (zero_le_one.trans (hf q (hsub hq)))
  nlinarith

/-- The pair factor: `f(m)³ ≤ (12m+5)/(12m−7)` at `m = M + 1`, cleared of
denominators.  Cleared, the difference of the two sides is a polynomial in
`M` whose coefficients are all positive, so `ring_nf` and `positivity` close
it; no coefficient is written down. -/
theorem pair_cube (M : ℕ) :
    ((6 * ((M : ℚ) + 1) - 1) / (6 * ((M : ℚ) + 1) - 2) *
        ((6 * ((M : ℚ) + 1) + 1) / (6 * ((M : ℚ) + 1)))) ^ 3 * (12 * ((M : ℚ) + 1) - 7) ≤
      12 * ((M : ℚ) + 1) + 5 := by
  have hM : (0 : ℚ) ≤ M := Nat.cast_nonneg M
  have h1 : 0 < 6 * ((M : ℚ) + 1) - 2 := by linarith
  have h2 : 0 < 6 * ((M : ℚ) + 1) := by linarith
  rw [div_mul_div_comm, div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos (mul_pos h1 h2) 3)]
  have key : 0 ≤ (12 * ((M : ℚ) + 1) + 5) * ((6 * ((M : ℚ) + 1) - 2) * (6 * ((M : ℚ) + 1))) ^ 3 -
      ((6 * ((M : ℚ) + 1) - 1) * (6 * ((M : ℚ) + 1) + 1)) ^ 3 * (12 * ((M : ℚ) + 1) - 7) := by
    ring_nf
    positivity
  linarith

/-- **`Π³ ≤ Π₈³·(12M+5)/17` over the primes below `6M + 2`**: the pair
factors telescope from `M = 1`, where the bound is an equality.  The constant
is `Π₈ = piBelow 8` itself, not a chosen number. -/
theorem mertensProd_wheel (M : ℕ) (hM : 1 ≤ M) :
    mertensProd (6 * M + 2).primesBelow ^ 3 ≤ piBelow 8 ^ 3 * (12 * M + 5) / 17 := by
  have hc0 : 0 ≤ piBelow 8 ^ 3 := pow_nonneg (piBelow_nonneg 8) 3
  induction M, hM using Nat.le_induction with
  | base =>
    rw [piBelow_def]
    norm_num
  | succ M hM ih =>
    have hsub := primesBelow_step M hM
    have htwo : ∀ q ∈ (6 * M + 2).primesBelow ∪ {6 * M + 5, 6 * M + 7}, 2 ≤ q := by
      intro q hq
      rcases Finset.mem_union.mp hq with h | h
      · exact (Nat.prime_of_mem_primesBelow h).two_le
      · rcases Finset.mem_insert.mp h with rfl | h
        · omega
        · rw [Finset.mem_singleton] at h
          omega
    have hdisj : Disjoint (6 * M + 2).primesBelow {6 * M + 5, 6 * M + 7} := by
      rw [Finset.disjoint_left]
      intro q hq hq'
      have := Nat.lt_of_mem_primesBelow hq
      rcases Finset.mem_insert.mp hq' with rfl | h
      · omega
      · rw [Finset.mem_singleton] at h
        omega
    have hab : 6 * M + 5 ≠ 6 * M + 7 := by omega
    have hU : mertensProd ((6 * M + 2).primesBelow ∪ {6 * M + 5, 6 * M + 7}) =
        mertensProd (6 * M + 2).primesBelow *
          (((6 * M + 5 : ℕ) : ℚ) / ((6 * M + 5 : ℕ) - 1) *
            (((6 * M + 7 : ℕ) : ℚ) / ((6 * M + 7 : ℕ) - 1))) := by
      unfold mertensProd
      rw [Finset.prod_union hdisj, Finset.prod_pair hab]
    have hle := (mertensProd_le_of_subset_two_le htwo hsub).trans_eq hU
    set X := mertensProd (6 * M + 2).primesBelow with hX
    have hX0 : 0 ≤ X := by
      rw [hX]
      exact Finset.prod_nonneg fun q hq ↦ mertensProd_factor_nonneg
        (Nat.prime_of_mem_primesBelow hq)
    have hpair := pair_cube M
    have hA : ((6 * M + 5 : ℕ) : ℚ) = 6 * ((M : ℚ) + 1) - 1 := by push_cast; ring
    have hB : ((6 * M + 7 : ℕ) : ℚ) = 6 * ((M : ℚ) + 1) + 1 := by push_cast; ring
    have hA1 : ((6 * M + 5 : ℕ) : ℚ) - 1 = 6 * ((M : ℚ) + 1) - 2 := by rw [hA]; ring
    have hB1 : ((6 * M + 7 : ℕ) : ℚ) - 1 = 6 * ((M : ℚ) + 1) := by rw [hB]; ring
    rw [hA1, hB1, hA, hB] at hle
    set f := (6 * ((M : ℚ) + 1) - 1) / (6 * ((M : ℚ) + 1) - 2) *
      ((6 * ((M : ℚ) + 1) + 1) / (6 * ((M : ℚ) + 1))) with hf
    have hf0 : 0 ≤ f := by
      rw [hf]
      have : (0 : ℚ) ≤ M := Nat.cast_nonneg M
      apply mul_nonneg <;> apply div_nonneg <;> linarith
    have hle' : mertensProd (6 * (M + 1) + 2).primesBelow ≤ X * f := by
      rw [hf]
      exact hle
    have h0 : 0 ≤ mertensProd (6 * (M + 1) + 2).primesBelow :=
      Finset.prod_nonneg fun q hq ↦ mertensProd_factor_nonneg (Nat.prime_of_mem_primesBelow hq)
    have hden : (0 : ℚ) < 12 * ((M : ℚ) + 1) - 7 := by linarith
    have hf3 : f ^ 3 ≤ (12 * ((M : ℚ) + 1) + 5) / (12 * ((M : ℚ) + 1) - 7) := by
      rw [le_div_iff₀ hden]
      exact hpair
    calc mertensProd (6 * (M + 1) + 2).primesBelow ^ 3
        ≤ (X * f) ^ 3 := pow_le_pow_left₀ h0 hle' 3
      _ = X ^ 3 * f ^ 3 := by ring
      _ ≤ (piBelow 8 ^ 3 * (12 * M + 5) / 17) *
            ((12 * ((M : ℚ) + 1) + 5) / (12 * ((M : ℚ) + 1) - 7)) :=
          mul_le_mul ih hf3 (pow_nonneg hf0 3) (div_nonneg (mul_nonneg hc0 (by positivity))
            (by norm_num))
      _ = piBelow 8 ^ 3 * (12 * ((M + 1 : ℕ) : ℚ) + 5) / 17 := by
          have hne : (12 : ℚ) * M + 5 ≠ 0 := by positivity
          rw [show (12 : ℚ) * ((M : ℚ) + 1) - 7 = 12 * M + 5 by ring]
          push_cast
          field_simp

/-- The telescoping pair bound `(6M+5)⁻² + (6M+7)⁻² ≤ (1/(2M+1) − 1/(2M+3))/9`. -/
theorem pair_sq (M : ℚ) (hM : 0 ≤ M) :
    ((6 * M + 5) ^ 2)⁻¹ + ((6 * M + 7) ^ 2)⁻¹ ≤ (1 / (2 * M + 1) - 1 / (2 * M + 3)) / 9 := by
  have h1 : 0 < 6 * M + 5 := by linarith
  have h2 : 0 < 6 * M + 7 := by linarith
  have h3 : 0 < 2 * M + 1 := by linarith
  have h4 : 0 < 2 * M + 3 := by linarith
  rw [div_sub_div _ _ h3.ne' h4.ne', inv_eq_one_div, inv_eq_one_div, div_add_div _ _
    (by positivity) (by positivity), div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg M, mul_pos h1 h2, mul_pos h3 h4]

/-- **`∑_{6m+5 ≤ q < 6(m+k)+2} q⁻² ≤ (1/(2m+1) − 1/(2(m+k)+1))/9`.** -/
theorem tail_sum_le (m k : ℕ) :
    ∑ q ∈ (6 * (m + k) + 2).primesBelow.filter (6 * m + 5 ≤ ·), (((q : ℚ)) ^ 2)⁻¹ ≤
      (1 / (2 * (m : ℚ) + 1) - 1 / (2 * ((m + k : ℕ) : ℚ) + 1)) / 9 := by
  induction k with
  | zero =>
    have hempty : (6 * (m + 0) + 2).primesBelow.filter (6 * m + 5 ≤ ·) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro q hq
      have := Nat.lt_of_mem_primesBelow hq
      omega
    rw [hempty]
    simp
  | succ k ih =>
    set M := m + k with hM
    have hsub := filter_primesBelow_step M (6 * m + 5) (by omega)
    have hdisj : Disjoint ((6 * M + 2).primesBelow.filter (6 * m + 5 ≤ ·))
        {6 * M + 5, 6 * M + 7} := by
      rw [Finset.disjoint_left]
      intro q hq hq'
      have := Nat.lt_of_mem_primesBelow (Finset.mem_filter.mp hq).1
      rcases Finset.mem_insert.mp hq' with rfl | h
      · omega
      · rw [Finset.mem_singleton] at h
        omega
    have hne : 6 * M + 5 ≠ 6 * M + 7 := by omega
    have hM0 : (0 : ℚ) ≤ M := Nat.cast_nonneg M
    have hpair := pair_sq (M : ℚ) hM0
    have heq : m + (k + 1) = M + 1 := by omega
    rw [heq]
    calc ∑ q ∈ (6 * (M + 1) + 2).primesBelow.filter (6 * m + 5 ≤ ·), (((q : ℚ)) ^ 2)⁻¹
        ≤ ∑ q ∈ (6 * M + 2).primesBelow.filter (6 * m + 5 ≤ ·) ∪ {6 * M + 5, 6 * M + 7},
            (((q : ℚ)) ^ 2)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
      _ = ∑ q ∈ (6 * M + 2).primesBelow.filter (6 * m + 5 ≤ ·), (((q : ℚ)) ^ 2)⁻¹ +
            ((((6 * M + 5 : ℕ) : ℚ) ^ 2)⁻¹ + (((6 * M + 7 : ℕ) : ℚ) ^ 2)⁻¹) := by
          rw [Finset.sum_union hdisj, Finset.sum_pair hne]
      _ ≤ (1 / (2 * (m : ℚ) + 1) - 1 / (2 * (M : ℚ) + 1)) / 9 +
            (1 / (2 * (M : ℚ) + 1) - 1 / (2 * (M : ℚ) + 3)) / 9 := by
          refine add_le_add ih ?_
          push_cast
          exact hpair
      _ = (1 / (2 * (m : ℚ) + 1) - 1 / (2 * ((M + 1 : ℕ) : ℚ) + 1)) / 9 := by
          push_cast
          ring

/-! ### The tail `p ≥ tailStart²` -/

/-- `Π₈ = 35/8`, the definition evaluated. -/
theorem piBelow_eight : piBelow 8 = 35 / 8 := by
  rw [piBelow_def, show Nat.primesBelow 8 = ({2, 3, 5, 7} : Finset ℕ) by decide]
  simp only [mertensProd]
  norm_num

/-- **Where the analytic tail starts**: `step4Crit_of_ge` covers `p ≥ tailStart²`
and the range certificates cover the primes below.  The value matters only
through `tail_closes`, the one inequality it has to satisfy; no statement
depends on it. -/
def tailStart : ℕ := 16

/-- The bound on `t·(S_p + 1/(p−1))`, `t = ⌊√p⌋`, one term per piece of
`step4Crit_of_ge`: the small primes, the telescoped large primes, and
`1/(p−1)`. -/
def tailBound (t : ℚ) : ℚ :=
  (t / 3 + 4) * t / (t ^ 2 + 1) + t / (3 * (t - 2)) + t / (t ^ 2 - 1)

theorem three_le_tailStart : 3 ≤ tailStart := by decide

/-- `tailBound` is antitone from `3` on, so the tail is controlled by its value
at `tailStart`. -/
theorem tailBound_anti {s t : ℚ} (hs : 3 ≤ s) (hst : s ≤ t) : tailBound t ≤ tailBound s := by
  unfold tailBound
  have ht : 3 ≤ t := hs.trans hst
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  have e1 : (t / 3 + 4) * t / (t ^ 2 + 1) ≤ (s / 3 + 4) * s / (s ^ 2 + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hk : 0 ≤ 4 * t * s - (t + s) / 3 - 4 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ t - 3) (by linarith : (0 : ℚ) ≤ s - 3)]
    nlinarith [mul_nonneg hd hk]
  have e2 : t / (3 * (t - 2)) ≤ s / (3 * (s - 2)) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have e3 : t / (t ^ 2 - 1) ≤ s / (s ^ 2 - 1) := by
    rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
    nlinarith [mul_nonneg hd (by nlinarith : (0 : ℚ) ≤ t * s + 1)]
  linarith

/-- **The tail closes at `tailStart`**: with `Π³ ≤ Π₈³(2p+17)/17` and
`p < (t+1)²`, this is `(Π_p(S_p + 1/(p−1)))³ < 1` at `t = tailStart`.  The
one numerical fact of the tail: `Π₈` and `tailBound` evaluated there. -/
theorem tail_closes :
    piBelow 8 ^ 3 * (2 * ((tailStart : ℚ) + 1) ^ 2 + 17) * tailBound tailStart ^ 3 <
      17 * (tailStart : ℚ) ^ 3 := by
  rw [piBelow_eight]
  norm_num [tailBound, tailStart]

/-- `(2(t+1)² + 17)/t³` decreases: its value at `t ≥ s` is at most its value
at `s`, cleared of denominators. -/
theorem cube_ratio_anti {s t : ℚ} (hs : 0 < s) (hst : s ≤ t) :
    (2 * (t + 1) ^ 2 + 17) * s ^ 3 ≤ (2 * (s + 1) ^ 2 + 17) * t ^ 3 := by
  have ht : 0 < t := hs.trans_le hst
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  have k1 : t ^ 2 * s ^ 3 ≤ s ^ 2 * t ^ 3 := by
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg s)) hd]
  have k2 : t * s ^ 3 ≤ s * t ^ 3 := by
    nlinarith only [mul_nonneg (mul_nonneg ht.le hs.le) (mul_nonneg hd (by linarith : 0 ≤ t + s))]
  have k3 : s ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hs.le hst 3
  nlinarith only [k1, k2, k3]

/-- **The pieces of `S_p + 1/(p−1)` against `tailBound`**: with `t = ⌊√p⌋` and
`m = ⌊t/6⌋`, the bound `S ≤ (2m+4)/(p+1) + 1/(9(2m+1))` of the split sum gives
`t·(S + 1/(p−1)) ≤ tailBound t`. -/
theorem mul_le_tailBound {t m p S : ℚ} (ht : 3 ≤ t) (h6m1 : 6 * m ≤ t)
    (h6m2 : t ≤ 6 * m + 5) (htp : t * t ≤ p)
    (hS : S ≤ (2 * m + 4) / (p + 1) + 1 / (9 * (2 * m + 1))) :
    t * (S + 1 / (p - 1)) ≤ tailBound t := by
  have ht0 : 0 < t := by linarith
  have e1 : (2 * m + 4) / (p + 1) ≤ (t / 3 + 4) / (t ^ 2 + 1) := by
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    exact mul_le_mul (by linarith) (by nlinarith) (by positivity) (by linarith)
  have e2 : 1 / (9 * (2 * m + 1)) ≤ 1 / (3 * (t - 2)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have e3 : 1 / (p - 1) ≤ 1 / (t ^ 2 - 1) :=
    one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  have hsum : S + 1 / (p - 1) ≤
      (t / 3 + 4) / (t ^ 2 + 1) + 1 / (3 * (t - 2)) + 1 / (t ^ 2 - 1) := by
    linarith
  calc t * (S + 1 / (p - 1))
      ≤ t * ((t / 3 + 4) / (t ^ 2 + 1) + 1 / (3 * (t - 2)) + 1 / (t ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_left hsum ht0.le
    _ = tailBound t := by unfold tailBound; ring

/-- **The closing step of the tail.**  If `P ≤ c(2(t+1)² + 17)/17` and
`t·X ≤ tailBound tailStart` with `t ≥ tailStart`, then `P·X³ < 1`, given
`tail_closes` in the form `hclose`. -/
theorem mul_cube_lt_one {c P t X : ℚ} (hc : 0 ≤ c) (hX0 : 0 ≤ X) (ht : (tailStart : ℚ) ≤ t)
    (hP : P ≤ c * (2 * (t + 1) ^ 2 + 17) / 17) (htX : t * X ≤ tailBound tailStart)
    (hclose : c * (2 * ((tailStart : ℚ) + 1) ^ 2 + 17) * tailBound tailStart ^ 3 <
      17 * (tailStart : ℚ) ^ 3) :
    P * X ^ 3 < 1 := by
  have hS0 : (0 : ℚ) < tailStart := by exact_mod_cast (show 0 < tailStart by decide)
  have ht0 : 0 < t := hS0.trans_le ht
  set B := tailBound tailStart with hBdef
  have hB0 : 0 ≤ B := le_trans (mul_nonneg ht0.le hX0) htX
  set K := c * (2 * (t + 1) ^ 2 + 17) with hK
  have hK0 : 0 ≤ K := mul_nonneg hc (by positivity)
  have hXB : (t * X) ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ (mul_nonneg ht0.le hX0) htX 3
  -- `K·X³·t³ ≤ K·B³`
  have step2 : K * X ^ 3 * t ^ 3 ≤ K * B ^ 3 := by
    rw [mul_assoc, ← mul_pow, mul_comm X]
    exact mul_le_mul_of_nonneg_left hXB hK0
  -- `K·B³·s³ < 17·s³·t³`, `s = tailStart`
  have step3 : K * B ^ 3 * (tailStart : ℚ) ^ 3 < 17 * (tailStart : ℚ) ^ 3 * t ^ 3 := by
    have hcB : 0 ≤ c * B ^ 3 := mul_nonneg hc (pow_nonneg hB0 3)
    calc K * B ^ 3 * (tailStart : ℚ) ^ 3
        = c * B ^ 3 * ((2 * (t + 1) ^ 2 + 17) * (tailStart : ℚ) ^ 3) := by rw [hK]; ring
      _ ≤ c * B ^ 3 * ((2 * ((tailStart : ℚ) + 1) ^ 2 + 17) * t ^ 3) :=
          mul_le_mul_of_nonneg_left (cube_ratio_anti hS0 ht) hcB
      _ = (c * (2 * ((tailStart : ℚ) + 1) ^ 2 + 17) * B ^ 3) * t ^ 3 := by ring
      _ < (17 * (tailStart : ℚ) ^ 3) * t ^ 3 := mul_lt_mul_of_pos_right hclose (by positivity)
  -- so `K·X³ < 17`
  have hKX : K * X ^ 3 < 17 := by
    have h := lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right step2 (by positivity : (0 : ℚ) ≤ (tailStart : ℚ) ^ 3)) step3
    have e1 : K * X ^ 3 * t ^ 3 * (tailStart : ℚ) ^ 3 =
        (K * X ^ 3) * (t ^ 3 * (tailStart : ℚ) ^ 3) := by ring
    have e2 : 17 * (tailStart : ℚ) ^ 3 * t ^ 3 = 17 * (t ^ 3 * (tailStart : ℚ) ^ 3) := by ring
    rw [e1, e2] at h
    exact lt_of_mul_lt_mul_right h (by positivity)
  calc P * X ^ 3 ≤ K / 17 * X ^ 3 := mul_le_mul_of_nonneg_right hP (pow_nonneg hX0 3)
    _ = K * X ^ 3 / 17 := by ring
    _ < 1 := by rw [div_lt_one (by norm_num)]; exact hKX

/-- **The criterion at every prime `p ≥ tailStart²`.** -/
theorem step4Crit_of_ge {p : ℕ} (hp : p.Prime) (hge : tailStart ^ 2 ≤ p) : step4Crit p := by
  set t := Nat.sqrt p with ht
  have htS : tailStart ≤ t := by
    rw [ht, Nat.le_sqrt]
    simpa [sq] using hge
  have ht3 : 3 ≤ t := three_le_tailStart.trans htS
  have htp : t * t ≤ p := Nat.sqrt_le p
  have hpt : p < (t + 1) * (t + 1) := Nat.lt_succ_sqrt p
  -- the Mertens product, by the wheel
  set M := p / 6 + 1 with hMdef
  have hM1 : 1 ≤ M := by omega
  have hpM : p ≤ 6 * M + 2 := by omega
  have hc0 : 0 ≤ piBelow 8 ^ 3 := pow_nonneg (piBelow_nonneg 8) 3
  have hA3 : piBelow p ^ 3 ≤ piBelow 8 ^ 3 * (2 * (p : ℚ) + 17) / 17 := by
    have h1 : piBelow p ≤ mertensProd (6 * M + 2).primesBelow :=
      mertensProd_le_of_subset (fun _ hq ↦ Nat.prime_of_mem_primesBelow hq)
        (primesBelow_mono hpM)
    have h2 := mertensProd_wheel M hM1
    have h3 : (12 * (M : ℚ) + 5) ≤ 2 * (p : ℚ) + 17 := by
      have : 12 * M + 5 ≤ 2 * p + 17 := by omega
      exact_mod_cast this
    calc piBelow p ^ 3 ≤ mertensProd (6 * M + 2).primesBelow ^ 3 :=
          pow_le_pow_left₀ (piBelow_nonneg p) h1 3
      _ ≤ piBelow 8 ^ 3 * (12 * M + 5) / 17 := h2
      _ ≤ piBelow 8 ^ 3 * (2 * (p : ℚ) + 17) / 17 := by gcongr
  have htp' : (t : ℚ) * t ≤ p := by exact_mod_cast htp
  have hpt' : (p : ℚ) < (t + 1) * (t + 1) := by exact_mod_cast hpt
  have hP : piBelow p ^ 3 ≤ piBelow 8 ^ 3 * (2 * ((t : ℚ) + 1) ^ 2 + 17) / 17 := by
    refine hA3.trans ?_
    gcongr
    nlinarith only [hpt']
  -- the order-free sum, split at `6m + 5`
  set m := t / 6 with hmdef
  have h6m : 6 * m ≤ t := Nat.mul_div_le t 6
  have h6m' : t ≤ 6 * m + 5 := by omega
  have hS : sOrd p ≤ (2 * (m : ℚ) + 4) / ((p : ℚ) + 1) + 1 / (9 * (2 * (m : ℚ) + 1)) := by
    refine (sOrd_le_rangeBound_self hp).trans ?_
    rw [rangeBound_def, ← Finset.sum_filter_add_sum_filter_not _ (· < 6 * m + 5)]
    gcongr
    · -- few small primes, each at most `(p+1)⁻¹`
      calc ∑ q ∈ p.primesBelow.filter (· < 6 * m + 5),
              min (((q : ℚ) ^ 2)⁻¹) (((p : ℚ) + 1)⁻¹)
          ≤ ∑ q ∈ p.primesBelow.filter (· < 6 * m + 5), ((p : ℚ) + 1)⁻¹ :=
            Finset.sum_le_sum fun _ _ ↦ min_le_right _ _
        _ = (p.primesBelow.filter (· < 6 * m + 5)).card * ((p : ℚ) + 1)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * (m : ℚ) + 4) * ((p : ℚ) + 1)⁻¹ := by
            gcongr
            have hsub : p.primesBelow.filter (· < 6 * m + 5) ⊆
                (6 * (m + 1) + 2).primesBelow := by
              intro q hq
              obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
              exact Nat.mem_primesBelow.mpr ⟨by omega, (Nat.mem_primesBelow.mp hq1).2⟩
            have hc := (Finset.card_le_card hsub).trans (card_primesBelow_le (m + 1) (by omega))
            have : ((p.primesBelow.filter (· < 6 * m + 5)).card : ℚ) ≤ 2 * (m + 1) + 2 := by
              exact_mod_cast hc
            linarith
        _ = (2 * (m : ℚ) + 4) / ((p : ℚ) + 1) := by rw [div_eq_mul_inv]
    · -- the large primes, by the telescoping tail
      calc ∑ q ∈ p.primesBelow.filter (fun q ↦ ¬ q < 6 * m + 5),
              min (((q : ℚ) ^ 2)⁻¹) (((p : ℚ) + 1)⁻¹)
          ≤ ∑ q ∈ p.primesBelow.filter (fun q ↦ ¬ q < 6 * m + 5), ((q : ℚ) ^ 2)⁻¹ :=
            Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
        _ ≤ ∑ q ∈ (6 * (m + p) + 2).primesBelow.filter (6 * m + 5 ≤ ·), ((q : ℚ) ^ 2)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ by positivity
            intro q hq
            obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
            exact Finset.mem_filter.mpr ⟨primesBelow_mono (by omega) hq1, by omega⟩
        _ ≤ (1 / (2 * (m : ℚ) + 1) - 1 / (2 * ((m + p : ℕ) : ℚ) + 1)) / 9 := tail_sum_le m p
        _ ≤ (1 / (2 * (m : ℚ) + 1)) / 9 := by
            have : (0 : ℚ) ≤ 1 / (2 * ((m + p : ℕ) : ℚ) + 1) := by positivity
            exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
        _ = 1 / (9 * (2 * (m : ℚ) + 1)) := by rw [div_div, mul_comm]
  -- `t·(S_p + 1/(p−1)) ≤ tailBound t ≤ tailBound tailStart`
  have htS' : (tailStart : ℚ) ≤ t := by exact_mod_cast htS
  have htX : (t : ℚ) * (sOrd p + 1 / ((p : ℚ) - 1)) ≤ tailBound tailStart :=
    (mul_le_tailBound (by exact_mod_cast ht3) (by exact_mod_cast h6m)
      (by exact_mod_cast h6m') htp' hS).trans
      (tailBound_anti (by exact_mod_cast three_le_tailStart) htS')
  have hX0 : 0 ≤ sOrd p + 1 / ((p : ℚ) - 1) := by
    have := sOrd_nonneg p
    have : (0 : ℚ) < (p : ℚ) - 1 := by
      have : (3 : ℚ) ≤ t := by exact_mod_cast ht3
      nlinarith only [this, htp']
    positivity
  -- `(Π_p·X)³ < 1`
  have hcube : (piBelow p * (sOrd p + 1 / ((p : ℚ) - 1))) ^ 3 < 1 ^ 3 := by
    rw [mul_pow, one_pow]
    exact mul_cube_lt_one hc0 hX0 htS' hP htX tail_closes
  exact lt_of_pow_lt_pow_left₀ 3 zero_le_one hcube

/-! ### Every prime -/

/-- **The step-4 criterion holds at every prime `p ≥ 5` other than `7`.** -/
theorem step4Crit_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) :
    step4Crit p := by
  rcases le_or_gt p 31 with h | h
  · exact step4Crit_of_le_thirtyone hp h5 h h7
  rcases lt_or_ge p (tailStart ^ 2) with h' | h'
  · have h'' : p < 256 := by simpa [tailStart] using h'
    refine step4Crit_of_mid hp ?_ (by omega)
    rcases Nat.lt_or_ge p 37 with hlt | hge
    · interval_cases p <;> norm_num at hp
    · exact hge
  · exact step4Crit_of_ge hp h'

/-! ### Exactly `7` fails -/

/-- **The criterion fails at `7`**: `Π₇ = 15/4` and `S₇ = 1/8 + 1/729 + 1/15625`, so
`Π₇·(S₇ + 1/6) ≈ 1.099`.  The term `2^{-ord₇ 2} = 1/8` alone costs `15/32`. -/
theorem not_step4Crit_seven : ¬ step4Crit 7 := by
  rw [step4Crit, piBelow_seven, sOrd_seven]
  norm_num

/-- **`7` is the only exception**: at a prime `p ≥ 5` the criterion holds exactly
when `p ≠ 7`. -/
theorem step4Crit_iff_ne_seven {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    step4Crit p ↔ p ≠ 7 :=
  ⟨fun h h7 ↦ not_step4Crit_seven (h7 ▸ h), step4Crit_of_prime hp h5⟩

/-- A prime `p ≥ 5` at which the criterion fails is `7`. -/
theorem eq_seven_of_not_step4Crit {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hc : ¬ step4Crit p) : p = 7 :=
  not_not.mp (mt (step4Crit_iff_ne_seven hp h5).mpr hc)

end Step4Criterion

end Erdos274
