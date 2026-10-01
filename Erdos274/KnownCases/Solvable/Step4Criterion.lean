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
* `37 ≤ p ≤ 251`: one exact certificate, with the order-free bound
  `S_p ≤ ∑_{q<p} min(q⁻³, (p+1)⁻¹)` (`PrimeOrder.sOrd_le_rangeBound3`), which
  uses `ord_p q ≥ 3` for `p ≥ 5` (`PrimeOrder.three_le_ordMod`).
* `p ≥ 256`: **the cube-root tail** (suggested by OpenAI GPT-5.6 Sol).  With
  `t³ ≤ p < (t+1)³`, `t ≥ 6`, split `S_p ≤ ∑_{q<p} min(q⁻³, (p+1)⁻¹)` at `t`:
  `S_p ≤ t/(p+1) + ∑_{n>t} n⁻³ ≤ 1/t² + 1/(2t²)` (`sum_Ico_inv_cube_le`, by
  telescoping), and `1/(p−1) ≤ 1/(5t²)`.  The product uses the wheel-6 bound
  `Π_p³ ≤ Π₈³(2p + 17)/17` (`mertensProd_wheel`): every prime `q ≥ 5` is
  `6m ± 1`, and the pair factor `f(m) = (6m−1)(6m+1)/((6m−2)·6m)` has
  `f(m)³ ≤ (12m+5)/(12m−7)`, which telescopes from `M = 1`.

**Where the numbers come from.**  In the tail, `Π₈ = piBelow 8` is a definition
evaluated, and `256` is where the range certificate stops; the closing
inequality has a factor-of-two margin.  Below `256` the work is finite and
cannot be made uniform: the criterion **fails** at `p = 7`, and at `p = 37` it
holds with a margin of about 1% (`DECISION_LOG` D94, D95), which no elementary
bound on `Π_p` reaches.  The order table and the range certificate are that
finite part.
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
  /- Prime endpoints and their certificates:
     5 → `piBelow_five`, `sOrd_five`; 11, 13, 17, 19, 23, 29, 31 →
     the correspondingly named `piBelow_*` and `sOrd_*` bounds below.
     Every other interval case is composite; 7 is excluded by `h7`. -/
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

/-! ### The middle range -/

/-- **One certificate for a range**: `Π_b·(rangeBound3 a b + 1/(a−1)) < 1`
gives the criterion at every prime in `[a, b]`, for `5 ≤ a`. -/
theorem step4Crit_of_range3 {a b p : ℕ} (hp : p.Prime) (ha : 5 ≤ a) (hap : a ≤ p) (hpb : p ≤ b)
    (h : piBelow b * (rangeBound3 a b + 1 / ((a : ℚ) - 1)) < 1) : step4Crit p := by
  refine step4Crit_of_bounds (by omega) (piBelow_mono hpb)
    (sOrd_le_rangeBound3 hp (ha.trans hap) hap hpb) (lt_of_le_of_lt ?_ h)
  have ha1 : (0 : ℚ) < (a : ℚ) - 1 := by
    have : (5 : ℚ) ≤ a := by exact_mod_cast ha
    linarith
  have hap' : (a : ℚ) - 1 ≤ (p : ℚ) - 1 := by
    have : (a : ℚ) ≤ p := by exact_mod_cast hap
    linarith
  have hinv : 1 / ((p : ℚ) - 1) ≤ 1 / ((a : ℚ) - 1) := one_div_le_one_div_of_le ha1 hap'
  have := rangeBound3_nonneg a b
  have := piBelow_nonneg b
  gcongr

private theorem primesBelow_251 :
    Nat.primesBelow 251 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
        73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
        157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233,
        239, 241} := by decide +kernel

/-- **The criterion at every prime `37 ≤ p ≤ 255`**: one certificate,
`Π₂₅₁·(rangeBound3 37 251 + 1/36) < 0.925`, using `ord_p q ≥ 3`; no prime lies
in `(251, 255]`. -/
theorem step4Crit_of_mid {p : ℕ} (hp : p.Prime) (h37 : 37 ≤ p) (h255 : p ≤ 255) :
    step4Crit p := by
  rcases le_or_gt p 251 with h | h
  · refine step4Crit_of_range3 hp (by norm_num) h37 h ?_
    simp only [piBelow_def, rangeBound3_def, primesBelow_251, mertensProd]
    norm_num [min_def]
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
    have hle := (Erdos274.mertensProd_le_of_subset_two_le htwo hsub).trans_eq hU
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

/-! ### The tail `p ≥ 256` -/

/-- `Π₈ = 35/8`, the definition evaluated. -/
theorem piBelow_eight : piBelow 8 = 35 / 8 := by
  rw [piBelow_def, show Nat.primesBelow 8 = ({2, 3, 5, 7} : Finset ℕ) by decide]
  simp only [mertensProd]
  norm_num

/-- Every `p` lies in a cube bracket `t³ ≤ p < (t+1)³`. -/
theorem exists_cube_bracket (p : ℕ) : ∃ t, t ^ 3 ≤ p ∧ p < (t + 1) ^ 3 := by
  have h : ∃ t, p < (t + 1) ^ 3 :=
    ⟨p, lt_of_lt_of_le (Nat.lt_succ_self p) (Nat.le_self_pow (by norm_num) _)⟩
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
  · rw [h0]
    simp
  · obtain ⟨s, hs⟩ : ∃ s, Nat.find h = s + 1 := ⟨Nat.find h - 1, by omega⟩
    have hmin := Nat.find_min h (show s < Nat.find h by omega)
    rw [hs]
    exact not_lt.mp hmin

/-- The telescoping step `(a+1)⁻³ ≤ 1/(2a²) − 1/(2(a+1)²)`. -/
theorem inv_cube_le_tele (a : ℚ) (ha : 1 ≤ a) :
    ((a + 1) ^ 3)⁻¹ ≤ 1 / (2 * a ^ 2) - 1 / (2 * (a + 1) ^ 2) := by
  have h0 : 0 < a := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity), inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg (a + 1)) (by linarith : (0 : ℚ) ≤ 6 * a + 2)]

/-- **`∑_{t < n ≤ t+K} n⁻³ ≤ 1/(2t²) − 1/(2(t+K)²)`**, by telescoping. -/
theorem sum_Ico_inv_cube_le (t : ℕ) (ht : 1 ≤ t) (K : ℕ) :
    ∑ n ∈ Finset.Ico (t + 1) (t + 1 + K), ((n : ℚ) ^ 3)⁻¹ ≤
      1 / (2 * (t : ℚ) ^ 2) - 1 / (2 * ((t + K : ℕ) : ℚ) ^ 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show t + 1 + (K + 1) = (t + 1 + K) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
    have h1 : (1 : ℚ) ≤ ((t + K : ℕ) : ℚ) := by
      have : 1 ≤ t + K := by omega
      exact_mod_cast this
    have h := inv_cube_le_tele ((t + K : ℕ) : ℚ) h1
    have e1 : ((t + 1 + K : ℕ) : ℚ) = ((t + K : ℕ) : ℚ) + 1 := by push_cast; ring
    have e2 : ((t + (K + 1) : ℕ) : ℚ) = ((t + K : ℕ) : ℚ) + 1 := by push_cast; ring
    rw [e1, e2]
    linarith

/-- **The criterion at every prime `p ≥ 256`.**  With `t³ ≤ p < (t+1)³`,
`t ≥ 6`: the primes `q ≤ t` give at most `t/(p+1) ≤ t⁻²` to `S_p`, the others
at most `∑_{n>t} n⁻³ ≤ 1/(2t²)`, and `1/(p−1) ≤ 1/(5t²)`; so
`S_p + 1/(p−1) ≤ 17/(10t²)`.  With `Π_p³ ≤ (35/8)³(2p+17)/17 ≤ (35/8)³·529p/4352`
and `(t+1)/t² ≤ 7/36`, the cube of the criterion is below `0.37`. -/
theorem step4Crit_of_ge {p : ℕ} (hp : p.Prime) (hge : 256 ≤ p) : step4Crit p := by
  obtain ⟨t, htp, hpt⟩ := exists_cube_bracket p
  have ht6 : 6 ≤ t := by
    by_contra h
    have h216 : (t + 1) ^ 3 ≤ 216 :=
      calc (t + 1) ^ 3 ≤ 6 ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 216 := by norm_num
    exact absurd (lt_of_lt_of_le hpt h216) (by omega)
  set T : ℚ := (t : ℚ) with hTdef
  have hT6 : (6 : ℚ) ≤ T := by rw [hTdef]; exact_mod_cast ht6
  have hT0 : 0 < T := by linarith
  have hT2 : 0 < T ^ 2 := pow_pos hT0 2
  have htp' : T ^ 3 ≤ (p : ℚ) := by rw [hTdef]; exact_mod_cast htp
  have hpt' : (p : ℚ) < (T + 1) ^ 3 := by rw [hTdef]; exact_mod_cast hpt
  -- the order-free sum, split at `t`
  have hS : sOrd p ≤ T / ((p : ℚ) + 1) + 1 / (2 * T ^ 2) := by
    refine (sOrd_le_rangeBound3 hp (by omega) le_rfl le_rfl).trans ?_
    rw [rangeBound3_def, ← Finset.sum_filter_add_sum_filter_not _ (· ≤ t)]
    gcongr
    · -- at most `t` small primes, each at most `(p+1)⁻¹`
      calc ∑ q ∈ p.primesBelow.filter (· ≤ t), min (((q : ℚ) ^ 3)⁻¹) (((p : ℚ) + 1)⁻¹)
          ≤ ∑ q ∈ p.primesBelow.filter (· ≤ t), ((p : ℚ) + 1)⁻¹ :=
            Finset.sum_le_sum fun _ _ ↦ min_le_right _ _
        _ = (p.primesBelow.filter (· ≤ t)).card * ((p : ℚ) + 1)⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ T * ((p : ℚ) + 1)⁻¹ := by
            gcongr
            have hsub : p.primesBelow.filter (· ≤ t) ⊆ Finset.Icc 1 t := by
              intro q hq
              obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
              have := (Nat.prime_of_mem_primesBelow hq1).one_lt
              exact Finset.mem_Icc.mpr ⟨by omega, hq2⟩
            have hc := (Finset.card_le_card hsub).trans_eq (Nat.card_Icc 1 t)
            have hc' : (p.primesBelow.filter (· ≤ t)).card ≤ t := by omega
            rw [hTdef]
            exact_mod_cast hc'
        _ = T / ((p : ℚ) + 1) := by rw [div_eq_mul_inv]
    · -- the large primes, by the telescoping tail
      calc ∑ q ∈ p.primesBelow.filter (fun q ↦ ¬ q ≤ t),
              min (((q : ℚ) ^ 3)⁻¹) (((p : ℚ) + 1)⁻¹)
          ≤ ∑ q ∈ p.primesBelow.filter (fun q ↦ ¬ q ≤ t), ((q : ℚ) ^ 3)⁻¹ :=
            Finset.sum_le_sum fun _ _ ↦ min_le_left _ _
        _ ≤ ∑ n ∈ Finset.Ico (t + 1) (t + 1 + p), ((n : ℚ) ^ 3)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ by positivity
            intro q hq
            obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
            have := Nat.lt_of_mem_primesBelow hq1
            exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        _ ≤ 1 / (2 * T ^ 2) - 1 / (2 * ((t + p : ℕ) : ℚ) ^ 2) :=
            sum_Ico_inv_cube_le t (by omega) p
        _ ≤ 1 / (2 * T ^ 2) := by
            have : (0 : ℚ) ≤ 1 / (2 * ((t + p : ℕ) : ℚ) ^ 2) := by positivity
            linarith
  -- `S_p + 1/(p−1) ≤ 17/(10t²)`
  set X := sOrd p + 1 / ((p : ℚ) - 1) with hXdef
  have hX : X ≤ 17 / (10 * T ^ 2) := by
    have h63 : 6 * T ^ 2 ≤ T ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hT6)]
    have e1 : T / ((p : ℚ) + 1) ≤ 1 / T ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hT2]
      have : T * T ^ 2 = T ^ 3 := by ring
      linarith
    have e2 : 1 / ((p : ℚ) - 1) ≤ 1 / (5 * T ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have e3 : 17 / (10 * T ^ 2) = 1 / T ^ 2 + 1 / (2 * T ^ 2) + 1 / (5 * T ^ 2) := by
      field_simp
      ring
    rw [e3]
    linarith
  have hX0 : 0 ≤ X := by
    have := sOrd_nonneg p
    have : (0 : ℚ) < (p : ℚ) - 1 := by
      have : (256 : ℚ) ≤ p := by exact_mod_cast hge
      linarith
    positivity
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
  have hP : piBelow p ^ 3 < (35 / 8) ^ 3 * (529 / 4352) * (T + 1) ^ 3 := by
    rw [piBelow_eight] at hA3
    have hp256 : (256 : ℚ) ≤ p := by exact_mod_cast hge
    calc piBelow p ^ 3 ≤ (35 / 8) ^ 3 * (2 * (p : ℚ) + 17) / 17 := hA3
      _ ≤ (35 / 8) ^ 3 * (529 / 4352) * p := by nlinarith
      _ < (35 / 8) ^ 3 * (529 / 4352) * (T + 1) ^ 3 :=
          mul_lt_mul_of_pos_left hpt' (by norm_num)
  -- `(Π_p·X)³ < 1`
  have hr : (T + 1) / T ^ 2 ≤ 7 / 36 := by
    rw [div_le_div_iff₀ hT2 (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hT6) (by linarith : (0 : ℚ) ≤ 7 * T + 6)]
  have heq : (T + 1) ^ 3 * (17 / (10 * T ^ 2)) ^ 3 = (17 / 10) ^ 3 * ((T + 1) / T ^ 2) ^ 3 := by
    field_simp
  have hcube : (piBelow p * X) ^ 3 < 1 := by
    rw [mul_pow]
    have hX3 : X ^ 3 ≤ (17 / (10 * T ^ 2)) ^ 3 := pow_le_pow_left₀ hX0 hX 3
    have hA0 : 0 ≤ piBelow p ^ 3 := pow_nonneg (piBelow_nonneg p) 3
    have hpos : 0 < (17 / (10 * T ^ 2)) ^ 3 := pow_pos (div_pos (by norm_num) (by positivity)) 3
    calc piBelow p ^ 3 * X ^ 3 ≤ piBelow p ^ 3 * (17 / (10 * T ^ 2)) ^ 3 :=
          mul_le_mul_of_nonneg_left hX3 hA0
      _ < (35 / 8) ^ 3 * (529 / 4352) * (T + 1) ^ 3 * (17 / (10 * T ^ 2)) ^ 3 :=
          mul_lt_mul_of_pos_right hP hpos
      _ = (35 / 8) ^ 3 * (529 / 4352) * ((17 / 10) ^ 3 * ((T + 1) / T ^ 2) ^ 3) := by
          rw [mul_assoc, heq]
      _ ≤ (35 / 8) ^ 3 * (529 / 4352) * ((17 / 10) ^ 3 * (7 / 36) ^ 3) := by
          have : 0 ≤ (T + 1) / T ^ 2 := by positivity
          gcongr
      _ < 1 := by norm_num
  exact lt_of_pow_lt_pow_left₀ 3 zero_le_one (by rwa [one_pow])

/-! ### Every prime -/

/-- **The step-4 criterion holds at every prime `p ≥ 5` other than `7`.** -/
theorem step4Crit_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h7 : p ≠ 7) :
    step4Crit p := by
  rcases le_or_gt p 31 with h | h
  · exact step4Crit_of_le_thirtyone hp h5 h h7
  rcases lt_or_ge p 256 with h' | h'
  · refine step4Crit_of_mid hp ?_ (by omega)
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
