/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.Arithmetic.PrimeOrder
import Mathlib.Tactic.NormNum.Prime

/-!
# The step-4 criterion `Π_p·(S_p + 1/(p−1)) < 1` at every prime `p ≥ 5`, `p ≠ 7`

`Step4Closure.false_of_covering` refutes a covering at `p` once
`Π_p·(S_p + 1/(p−1)) < 1` (`step4Crit`).  This file proves it for **every**
prime `p ≥ 5` other than `7`, with no Mertens estimate.

* `p ≤ 31`: the order table of `PrimeOrder`.
* `37 ≤ p ≤ 251`: one exact certificate per range, with the order-free bound
  `S_p ≤ ∑_{q<p} min(q⁻², (p+1)⁻¹)` (`PrimeOrder.sOrd_le_rangeBound`), as in
  `CELargePrimes`.
* `p ≥ 256`: **the wheel-6 bounds**, proved by induction over blocks of six.
  Every prime `q ≥ 5` is `6m ± 1`, so
  - `Π_p³ ≤ 27(2p + 17)/5` (`mertensProd_wheel`), because the pair factor
    `f(m) = (6m−1)(6m+1)/((6m−2)·6m)` has `f(m)³ ≤ (12m+5)/(12m−7)`, which
    telescopes;
  - there are at most `2M + 2` primes below `6M + 2` (`card_primesBelow_le`);
  - `∑_{q ≥ 6m+5} q⁻² ≤ 1/(9(2m+1))` (`tail_sum_le`), because
    `(6M+5)⁻² + (6M+7)⁻² ≤ (1/(2M+1) − 1/(2M+3))/9`, which telescopes.

  Splitting `S_p` at `6m+5` with `m = ⌊√p⌋/6` gives `S_p + 1/(p−1) ≤ 1.05/√p`
  roughly, and then `(Π_p(S_p + 1/(p−1)))³ < 1`.

The range endpoints and the split point are proof data: they make the
certificates close, and no statement depends on them.
-/

namespace Erdos274

namespace Step4Criterion

open Finset PrimeOrder

set_option maxRecDepth 20000

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
        239, 241} := by decide

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

theorem not_prime_of_dvd {q d : ℕ} (hd : d.Prime) (h : d ∣ q) (hlt : d < q) : ¬ q.Prime :=
  fun hq ↦ by
    have := (Nat.prime_dvd_prime_iff_eq hd hq).mp h
    omega

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
  · exact absurd hqp (not_prime_of_dvd Nat.prime_two ⟨3 * M + 1, by ring⟩ (by omega))
  · exact absurd hqp (not_prime_of_dvd Nat.prime_three ⟨2 * M + 1, by ring⟩ (by omega))
  · exact absurd hqp (not_prime_of_dvd Nat.prime_two ⟨3 * M + 2, by ring⟩ (by omega))
  · simp
  · exact absurd hqp (not_prime_of_dvd Nat.prime_two ⟨3 * M + 3, by ring⟩ (by omega))
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

/-- The pair factor: `f(m)³ ≤ (12m+5)/(12m−7)`, cleared of denominators. -/
theorem pair_cube (m : ℚ) (hm : 1 ≤ m) :
    ((6 * m - 1) / (6 * m - 2) * ((6 * m + 1) / (6 * m))) ^ 3 * (12 * m - 7) ≤ 12 * m + 5 := by
  have h1 : 0 < 6 * m - 2 := by linarith
  have h2 : 0 < 6 * m := by linarith
  rw [div_mul_div_comm, div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have hu : 0 ≤ m - 1 := by linarith
  have key : (12 * m + 5) * ((6 * m - 2) * (6 * m)) ^ 3 -
      ((6 * m - 1) * (6 * m + 1)) ^ 3 * (12 * m - 7) =
      20633 + 90948 * (m - 1) + 149796 * (m - 1) ^ 2 + 109296 * (m - 1) ^ 3 +
        29808 * (m - 1) ^ 4 := by ring
  nlinarith [key, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4]

/-- **`Π³ ≤ 27(12M+5)/5` over the primes below `6M + 2`.** -/
theorem mertensProd_wheel (M : ℕ) (hM : 1 ≤ M) :
    mertensProd (6 * M + 2).primesBelow ^ 3 ≤ 27 * (12 * M + 5) / 5 := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [show (Nat.primesBelow (6 * 1 + 2) : Finset ℕ) = ({2, 3, 5, 7} : Finset ℕ) by decide]
    simp only [mertensProd]
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
    have hm : (1 : ℚ) ≤ (M : ℚ) + 1 := by linarith [(Nat.cast_nonneg M : (0 : ℚ) ≤ M)]
    have hpair := pair_cube ((M : ℚ) + 1) hm
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
      _ ≤ (27 * (12 * M + 5) / 5) * ((12 * ((M : ℚ) + 1) + 5) / (12 * ((M : ℚ) + 1) - 7)) :=
          mul_le_mul ih hf3 (by positivity) (by positivity)
      _ = 27 * (12 * ((M + 1 : ℕ) : ℚ) + 5) / 5 := by
          have : (12 : ℚ) * ((M : ℚ) + 1) - 7 = 12 * M + 5 := by ring
          rw [this]
          field_simp
          push_cast
          ring

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

/-! ### The tail `p ≥ 256` -/

/-- **The criterion at every prime `p ≥ 256`.** -/
theorem step4Crit_of_ge {p : ℕ} (hp : p.Prime) (h256 : 256 ≤ p) : step4Crit p := by
  set t := Nat.sqrt p with ht
  have ht16 : 16 ≤ t := by
    rw [ht, Nat.le_sqrt]
    omega
  have htp : t * t ≤ p := Nat.sqrt_le p
  have hpt : p < (t + 1) * (t + 1) := Nat.lt_succ_sqrt p
  -- the Mertens product, by the wheel
  set M := p / 6 + 1 with hMdef
  have hM1 : 1 ≤ M := by omega
  have hpM : p ≤ 6 * M + 2 := by omega
  have hA3 : piBelow p ^ 3 ≤ 27 * (2 * (p : ℚ) + 17) / 5 := by
    have h1 : piBelow p ≤ mertensProd (6 * M + 2).primesBelow :=
      mertensProd_le_of_subset (fun _ hq ↦ Nat.prime_of_mem_primesBelow hq)
        (primesBelow_mono hpM)
    have h2 := mertensProd_wheel M hM1
    have h3 : (12 * (M : ℚ) + 5) ≤ 2 * (p : ℚ) + 17 := by
      have : 12 * M + 5 ≤ 2 * p + 17 := by omega
      exact_mod_cast this
    calc piBelow p ^ 3 ≤ mertensProd (6 * M + 2).primesBelow ^ 3 :=
          pow_le_pow_left₀ (piBelow_nonneg p) h1 3
      _ ≤ 27 * (12 * M + 5) / 5 := h2
      _ ≤ 27 * (2 * (p : ℚ) + 17) / 5 := by gcongr
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
  -- `X = S_p + 1/(p−1) ≤ (21/20)/t`
  have ht' : (16 : ℚ) ≤ t := by exact_mod_cast ht16
  have htp' : (t : ℚ) * t ≤ p := by exact_mod_cast htp
  have hpt' : (p : ℚ) < (t + 1) * (t + 1) := by exact_mod_cast hpt
  have h6m1 : 6 * (m : ℚ) ≤ t := by exact_mod_cast h6m
  have h6m2 : (t : ℚ) ≤ 6 * m + 5 := by exact_mod_cast h6m'
  have ht0 : (0 : ℚ) < t := by linarith
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by nlinarith
  have hX : sOrd p + 1 / ((p : ℚ) - 1) ≤ (21 / 20) / t := by
    have e1 : (2 * (m : ℚ) + 4) / ((p : ℚ) + 1) ≤ (7 / 12) / t := by
      rw [div_le_div_iff₀ (by linarith) ht0]
      nlinarith
    have e2 : 1 / (9 * (2 * (m : ℚ) + 1)) ≤ (8 / 21) / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]
      nlinarith
    have e3 : 1 / ((p : ℚ) - 1) ≤ (16 / 255) / t := by
      rw [div_le_div_iff₀ hp1 ht0]
      nlinarith
    have e4 : (7 / 12 : ℚ) / t + (8 / 21) / t + (16 / 255) / t ≤ (21 / 20) / t := by
      rw [← add_div, ← add_div]
      gcongr
      norm_num
    linarith
  -- `(Π_p·X)³ < 1`
  have hX0 : 0 ≤ sOrd p + 1 / ((p : ℚ) - 1) := by
    have := sOrd_nonneg p
    positivity
  have hA0 := piBelow_nonneg p
  have hprod0 : 0 ≤ piBelow p * (sOrd p + 1 / ((p : ℚ) - 1)) := mul_nonneg hA0 hX0
  have hcube : (piBelow p * (sOrd p + 1 / ((p : ℚ) - 1))) ^ 3 < 1 ^ 3 := by
    rw [mul_pow, one_pow]
    have hX3 : (sOrd p + 1 / ((p : ℚ) - 1)) ^ 3 ≤ ((21 / 20) / t) ^ 3 :=
      pow_le_pow_left₀ hX0 hX 3
    calc piBelow p ^ 3 * (sOrd p + 1 / ((p : ℚ) - 1)) ^ 3
        ≤ (27 * (2 * (p : ℚ) + 17) / 5) * ((21 / 20) / t) ^ 3 :=
          mul_le_mul hA3 hX3 (by positivity) (by positivity)
      _ < 1 := by
          rw [div_pow, mul_div_assoc', div_lt_one (by positivity)]
          have hp2 : 2 * (p : ℚ) + 17 < 2 * ((t + 1) * (t + 1)) + 17 := by linarith
          nlinarith [mul_pos ht0 ht0]
  exact lt_of_pow_lt_pow_left₀ 3 zero_le_one hcube

/-! ### Every prime -/

/-- **The step-4 criterion holds at every prime `p ≥ 5` other than `7`.** -/
theorem step4Crit_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) :
    step4Crit p := by
  rcases le_or_gt p 31 with h | h
  · exact step4Crit_of_le_thirtyone hp h5 h h7
  rcases le_or_gt p 255 with h' | h'
  · refine step4Crit_of_mid hp ?_ h'
    rcases Nat.lt_or_ge p 37 with hlt | hge
    · interval_cases p <;> norm_num at hp
    · exact hge
  · exact step4Crit_of_ge hp h'

end Step4Criterion

end Erdos274
