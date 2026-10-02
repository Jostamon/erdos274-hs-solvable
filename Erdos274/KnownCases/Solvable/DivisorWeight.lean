/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.KnownCases.Solvable.ApexCharging
public import Erdos274.KnownCases.Solvable.GeometricShadow.UpSet
public import Mathlib.Data.Nat.Totient


/-!
# Lemma O in the untruncated weight

`DECISION_LOG` D98 §14.  `SevenClosure.closure_ineq` takes Lemma O in the
form `W(up H₀) ≤ Π·ν`, for the **untruncated** weight of `ExpWeight`.  The
group side produces it in the divisor form `μ(D(S)) ≤ |Ω|`
(`QuotientShadow.divisorMass_le_ncard_shadows`).  This file is the exact
dictionary between the two.

Fix primes `q : ι → ℕ`, injective, and the ratios `rᵢ = 1/qᵢ` (`ratio`).
A positive integer all of whose primes are among the `qᵢ` is `Smooth`; its
exponent vector is `vec q d`, with `vᵢ(d) = v_{qᵢ}(d)`.

* **The dictionary.**  `vec_mul`: `v(ab) = v(a) + v(b)`.  `vec_le_iff`:
  `v(a) ≤ v(b) ↔ a ∣ b`.  `w_vec`: `w(v(d)) = 1/d`.  `W_univ_ratio`:
  `W(ℕ^ι) = Π`, the Mertens product `∏ qᵢ/(qᵢ − 1)` (`PiN`).
* **Truncation is exact on up-sets.**  Fix `n`.  The map `z ↦ z ⊓ v(n)`
  has fibres `fib`, one over each divisor `e ∣ n` (`W_eq_sum_fib`).  The
  fibre over `v(e)` is a product set, and its mass is `Π·φ(n/e)/n`
  (`W_fib_vec`).  This is the untruncated reading of (5.2).
* **Lemma O** (`W_up_heads`).  For heads `H` dividing `n`,

      W(up v(H)) = Π · μ(D({n/h : h ∈ H})) / n,

  an identity.  With Lemma O's `μ(D(S)) ≤ N` it gives `W(up v(H)) ≤ Π·N/n`
  (`W_up_heads_le`), which is the shape `closure_ineq` consumes.

No constant enters: `Π` is `W_univ`, and `φ` comes from
`Nat.totient_eq_mul_prod_factors`.
-/

@[expose] public section

namespace Erdos274

namespace DivisorWeight

open Set ExpWeight ApexCharging GeometricShadow
open scoped ENNReal NNReal

variable {ι : Type*}

/-- The exponent vector `vᵢ(d) = v_{qᵢ}(d)`. -/
def vec (q : ι → ℕ) (d : ℕ) : ι → ℕ := fun i ↦ d.factorization (q i)

/-- The ratios `1/qᵢ`, as `ℝ≥0`. -/
noncomputable def ratioN (q : ι → ℕ) (i : ι) : ℝ≥0 := (q i : ℝ≥0)⁻¹

/-- The ratios `1/qᵢ`, as `ℝ≥0∞`. -/
noncomputable def ratio (q : ι → ℕ) (i : ι) : ℝ≥0∞ := ratioN q i

/-- `d` is `q`-smooth: nonzero, with every prime factor among the `qᵢ`. -/
def Smooth (q : ι → ℕ) (d : ℕ) : Prop := d ≠ 0 ∧ ∀ p ∈ d.primeFactors, ∃ i, q i = p

variable {q : ι → ℕ}

theorem Smooth.of_dvd {n d : ℕ} (hn : Smooth q n) (hd : d ∣ n) : Smooth q d :=
  ⟨ne_zero_of_dvd_ne_zero hn.1 hd, fun p hp ↦ hn.2 p (Nat.primeFactors_mono hd hn.1 hp)⟩

/-- Products of `q`-smooth positive integers remain `q`-smooth. -/
theorem Smooth.mul {a b : ℕ} (ha : Smooth q a) (hb : Smooth q b) : Smooth q (a * b) := by
  refine ⟨Nat.mul_ne_zero ha.1 hb.1, fun p hp ↦ ?_⟩
  rw [Nat.primeFactors_mul ha.1 hb.1, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact ha.2 p hp
  · exact hb.2 p hp

theorem vec_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : vec q (a * b) = vec q a + vec q b := by
  funext i
  simp [vec, Nat.factorization_mul ha hb]

theorem ratioN_lt_one (hq : ∀ i, (q i).Prime) (i : ι) : ratioN q i < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast (hq i).one_lt)

theorem ratio_ne_top (i : ι) : ratio q i ≠ ⊤ := ENNReal.coe_ne_top

theorem ratio_ne_zero (hq : ∀ i, (q i).Prime) (i : ι) : ratio q i ≠ 0 := by
  rw [ratio, ENNReal.coe_ne_zero, ratioN]
  exact inv_ne_zero (by exact_mod_cast (hq i).ne_zero)

theorem one_sub_ratio_inv (hq : ∀ i, (q i).Prime) (i : ι) :
    (1 - ratio q i)⁻¹ = (((1 - ratioN q i)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  have h1 : (1 : ℝ≥0) - ratioN q i ≠ 0 := (tsub_pos_of_lt (ratioN_lt_one hq i)).ne'
  rw [ratio, ← ENNReal.coe_one, ← ENNReal.coe_sub, ← ENNReal.coe_inv h1]

theorem coe_one_sub_ratioN (hq : ∀ i, (q i).Prime) (i : ι) :
    ((1 - ratioN q i : ℝ≥0) : ℝ) = 1 - (q i : ℝ)⁻¹ := by
  rw [NNReal.coe_sub (ratioN_lt_one hq i).le]
  simp [ratioN]

/-- **Divisibility is the order on exponent vectors.** -/
theorem vec_le_iff {a b : ℕ} (ha : Smooth q a) (hb : b ≠ 0) : vec q a ≤ vec q b ↔ a ∣ b := by
  rw [← Nat.factorization_le_iff_dvd ha.1 hb]
  constructor
  · intro h
    refine Finsupp.le_def.mpr fun p ↦ ?_
    by_cases hp : p ∈ a.primeFactors
    · obtain ⟨i, rfl⟩ := ha.2 p hp
      exact h i
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rw [hp]
      exact Nat.zero_le _
  · intro h i
    exact Finsupp.le_def.mp h (q i)

/-! ### The truncation fibres -/

/-- The fibre of the truncation `z ↦ z ⊓ v` over `b`. -/
def fib (v b : ι → ℕ) : Set (ι → ℕ) := {z | ∀ i, min (z i) (v i) = b i}

theorem fib_eq_shift {v b : ι → ℕ} (hb : b ≤ v) :
    fib v b = shift b (univ.pi fun i ↦ if b i < v i then {0} else univ) := by
  ext z
  simp only [fib, mem_shift, mem_univ_pi]
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · have : min (z i) (v i) = b i := h i
      change b i ≤ z i
      omega
    · have h1 : min (z i) (v i) = b i := h i
      have h2 : b i ≤ v i := hb i
      split_ifs with hi
      · simp only [Pi.sub_apply, mem_singleton_iff]
        omega
      · exact mem_univ _
  · rintro ⟨h1, h2⟩ i
    have h3 : b i ≤ z i := h1 i
    have h4 : b i ≤ v i := hb i
    have h5 := h2 i
    split_ifs at h5 with hi
    · simp only [Pi.sub_apply, mem_singleton_iff] at h5
      omega
    · omega

/-- The primes of `n/e` are the coordinates where `v(e) < v(n)`. -/
theorem primeFactors_div [Fintype ι] {n e : ℕ} (hn : Smooth q n) (he : e ∣ n) :
    (n / e).primeFactors = (Finset.univ.filter fun i ↦ vec q e i < vec q n i).image q := by
  ext p
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, Nat.factorization_div he,
    Finsupp.tsub_apply, Finset.mem_image]
  constructor
  · intro h
    have hp : p ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    obtain ⟨i, rfl⟩ := hn.2 p hp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [vec]; omega⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have := (Finset.mem_filter.mp hi).2
    simp only [vec] at this
    omega

variable [Fintype ι]

/-- The Mertens product `Π = ∏ (1 − 1/qᵢ)⁻¹`, as `ℝ≥0`. -/
noncomputable def PiN (q : ι → ℕ) : ℝ≥0 := ∏ i, (1 - ratioN q i)⁻¹

/-- The mass of a fibre: `w(b)·∏_{bᵢ = vᵢ} (1 − rᵢ)⁻¹`. -/
theorem W_fib {v b : ι → ℕ} (hb : b ≤ v) (r : ι → ℝ≥0∞) :
    W r (fib v b) = w r b * ∏ i, if b i < v i then 1 else (1 - r i)⁻¹ := by
  rw [fib_eq_shift hb, W_shift, W_pi]
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  split_ifs
  · have h0 : ∀ m ≠ 0, ({0} : Set ℕ).indicator (fun x ↦ r i ^ x) m = 0 :=
      fun m hm ↦ indicator_of_notMem (by simpa using hm) _
    rw [tsum_eq_single 0 h0]
    simp
  · simp [ENNReal.tsum_geometric]

section Primes

variable (hq : ∀ i, (q i).Prime)
include hq

/-- **`W(ℕ^ι) = Π`.** -/
theorem W_univ_ratio : W (ratio q) univ = (PiN q : ℝ≥0∞) := by
  rw [W_univ, PiN, ENNReal.ofNNReal_finsetProd]
  exact Finset.prod_congr rfl fun i _ ↦ one_sub_ratio_inv hq i

theorem factorization_prod_pow (a : ι → ℕ) :
    (∏ i, q i ^ a i).factorization = ∑ i, Finsupp.single (q i) (a i) := by
  rw [Nat.factorization_prod fun i _ ↦ pow_ne_zero _ (hq i).ne_zero]
  exact Finset.sum_congr rfl fun i _ ↦ (hq i).factorization_pow

theorem prod_pow_ne_zero (a : ι → ℕ) : ∏ i, q i ^ a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hq i).ne_zero

variable (hqi : Function.Injective q)
include hqi

theorem factorization_prod_pow_apply (a : ι → ℕ) (j : ι) :
    (∏ i, q i ^ a i).factorization (q j) = a j := by
  rw [factorization_prod_pow hq, Finsupp.finsetSum_apply,
    Finset.sum_eq_single j (fun i _ hij ↦ by simp [hqi.eq_iff, hij]) (by simp)]
  simp

/-- The exponent vector of `∏ qᵢ^{aᵢ}` is `a`. -/
theorem vec_prod_pow (a : ι → ℕ) : vec q (∏ i, q i ^ a i) = a :=
  funext (factorization_prod_pow_apply hq hqi a)

/-- A smooth number is the product of its prime powers. -/
theorem prod_pow_vec {d : ℕ} (hd : Smooth q d) : ∏ i, q i ^ vec q d i = d := by
  refine Nat.eq_of_factorization_eq (prod_pow_ne_zero hq _) hd.1 fun p ↦ ?_
  by_cases hp : ∃ i, q i = p
  · obtain ⟨j, rfl⟩ := hp
    rw [factorization_prod_pow_apply hq hqi]
    rfl
  · push Not at hp
    rw [factorization_prod_pow hq, Finsupp.finsetSum_apply,
      Finset.sum_eq_zero fun i _ ↦ by simp [hp i]]
    refine (Finsupp.notMem_support_iff.mp fun h ↦ ?_).symm
    rw [Nat.support_factorization] at h
    obtain ⟨i, hi⟩ := hd.2 p h
    exact hp i hi

omit [Fintype ι] in
theorem vec_injOn [Finite ι] {a b : ℕ} (ha : Smooth q a) (hb : Smooth q b)
    (h : vec q a = vec q b) : a = b := by
  have := Fintype.ofFinite ι
  rw [← prod_pow_vec hq hqi ha, ← prod_pow_vec hq hqi hb, h]

omit [Fintype ι] in
/-- The exponent vector of a prime power `qᵢ^k` is `k·δᵢ`. -/
theorem vec_pow [DecidableEq ι] (i : ι) (k : ℕ) : vec q (q i ^ k) = Pi.single i k := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [vec, (hq j).factorization_pow]
  · simp [vec, (hq i).factorization_pow, hqi.eq_iff, hji]

omit [Fintype ι] hqi in
theorem smooth_pow (i : ι) (k : ℕ) : Smooth q (q i ^ k) := by
  refine ⟨pow_ne_zero _ (hq i).ne_zero, fun p hp ↦ ⟨i, ?_⟩⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at hp
  · rw [Nat.primeFactors_pow _ hk.ne', (hq i).primeFactors, Finset.mem_singleton] at hp
    exact hp.symm

omit hq hqi in
/-- The weight in `ℝ≥0`: `w(b) = 1/∏ qᵢ^{bᵢ}`. -/
theorem w_ratio (b : ι → ℕ) :
    w (ratio q) b = ((((∏ i, q i ^ b i : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib, ENNReal.ofNNReal_finsetProd, w]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [ratio, ratioN, Nat.cast_pow, ← ENNReal.coe_pow, inv_pow]

/-- **`w(v(d)) = 1/d`.** -/
theorem w_vec {d : ℕ} (hd : Smooth q d) :
    w (ratio q) (vec q d) = ((((d : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [w_ratio, prod_pow_vec hq hqi hd]

theorem mem_fib_prod {n : ℕ} (hn : Smooth q n) (z : ι → ℕ) :
    (∏ i, q i ^ min (z i) (vec q n i)) ∈ n.divisors ∧
      z ∈ fib (vec q n) (vec q (∏ i, q i ^ min (z i) (vec q n i))) := by
  refine ⟨Nat.mem_divisors.mpr ⟨?_, hn.1⟩, ?_⟩
  · conv_rhs => rw [← prod_pow_vec hq hqi hn]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ ↦ pow_dvd_pow _ (min_le_right _ _)
  · intro i
    rw [vec_prod_pow hq hqi]

omit [Fintype ι] in
theorem eq_of_mem_fib [Finite ι] {n e e' : ℕ} (hn : Smooth q n) (he : e ∈ n.divisors)
    (he' : e' ∈ n.divisors) {z : ι → ℕ} (hz : z ∈ fib (vec q n) (vec q e))
    (hz' : z ∈ fib (vec q n) (vec q e')) : e = e' :=
  vec_injOn hq hqi (hn.of_dvd (Nat.dvd_of_mem_divisors he))
    (hn.of_dvd (Nat.dvd_of_mem_divisors he')) (funext fun i ↦ (hz i).symm.trans (hz' i))

/-- **The fibres partition `ℕ^ι`**, one for each divisor of `n`. -/
theorem W_eq_sum_fib {n : ℕ} (hn : Smooth q n) (r : ι → ℝ≥0∞) (S : Set (ι → ℕ)) :
    W r S = ∑ e ∈ n.divisors, W r (S ∩ fib (vec q n) (vec q e)) := by
  simp only [W]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine tsum_congr fun z ↦ ?_
  obtain ⟨he₀, hz⟩ := mem_fib_prod hq hqi hn z
  rw [Finset.sum_eq_single _ (fun e he hne ↦ indicator_of_notMem
    (fun h ↦ hne (eq_of_mem_fib hq hqi hn he he₀ h.2 hz)) _) (fun h ↦ absurd he₀ h)]
  by_cases hS : z ∈ S
  · rw [indicator_of_mem hS, indicator_of_mem (mem_inter hS hz)]
  · rw [indicator_of_notMem hS, indicator_of_notMem fun h ↦ hS h.1]

/-- **The mass of the fibre over `v(e)` is `Π·φ(n/e)/n`.** -/
theorem W_fib_vec {n e : ℕ} (hn : Smooth q n) (he : e ∣ n) :
    W (ratio q) (fib (vec q n) (vec q e)) =
      (((PiN q * (n / e).totient / n : ℝ≥0)) : ℝ≥0∞) := by
  have hle : vec q e ≤ vec q n := (vec_le_iff (hn.of_dvd he) hn.1).mpr he
  rw [W_fib hle, w_vec hq hqi (hn.of_dvd he)]
  have hite : ∀ i, (if vec q e i < vec q n i then 1 else (1 - ratio q i)⁻¹) =
      (((if vec q e i < vec q n i then 1 else (1 - ratioN q i)⁻¹ : ℝ≥0)) : ℝ≥0∞) := fun i ↦ by
    split_ifs
    · rfl
    · exact one_sub_ratio_inv hq i
  simp only [hite]
  rw [← ENNReal.ofNNReal_finsetProd, ← ENNReal.coe_mul, ENNReal.coe_inj, ← NNReal.coe_inj]
  -- the identity in `ℝ`
  set m := n / e with hm
  have he0 : e ≠ 0 := (hn.of_dvd he).1
  have hnem : n = e * m := (Nat.mul_div_cancel' he).symm
  have hm0 : m ≠ 0 := by rintro h; rw [h, mul_zero] at hnem; exact hn.1 hnem
  have hx : ∀ i, (1 : ℝ) - (q i : ℝ)⁻¹ ≠ 0 := fun i ↦ by
    have : (1 : ℝ) < q i := by exact_mod_cast (hq i).one_lt
    have : (q i : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  have hφ : (m.totient : ℝ) =
      m * ∏ i ∈ Finset.univ.filter fun i ↦ vec q e i < vec q n i, (1 - (q i : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ ↦ (x : ℝ)) (Nat.totient_eq_mul_prod_factors m)
    push_cast at h
    rw [h, primeFactors_div hn he, Finset.prod_image fun i _ j _ hij ↦ hqi hij]
  have hsplit : ∏ i, (if vec q e i < vec q n i then (1 : ℝ) else (1 - (q i : ℝ)⁻¹)⁻¹) =
      (∏ i, (1 - (q i : ℝ)⁻¹)⁻¹) *
        ∏ i ∈ Finset.univ.filter fun i ↦ vec q e i < vec q n i, (1 - (q i : ℝ)⁻¹) := by
    rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split_ifs
    · rw [inv_mul_cancel₀ (hx i)]
    · rw [mul_one]
  have hprod : ∀ i, (((if vec q e i < vec q n i then 1 else (1 - ratioN q i)⁻¹ : ℝ≥0)) : ℝ) =
      if vec q e i < vec q n i then (1 : ℝ) else (1 - (q i : ℝ)⁻¹)⁻¹ := fun i ↦ by
    split_ifs
    · rfl
    · rw [NNReal.coe_inv, coe_one_sub_ratioN hq]
  simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_prod, NNReal.coe_div, hprod,
    NNReal.coe_natCast, PiN, coe_one_sub_ratioN hq]
  rw [hsplit, hφ, hnem]
  push_cast
  have he0' : (e : ℝ) ≠ 0 := by exact_mod_cast he0
  have hm0' : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  field_simp

end Primes

/-! ### Lemma O -/

/-- The divisor-mass side of the identity: summing `φ(n/e)` over the divisors
`e ∣ n` above some head is `μ(D({n/h}))`. -/
theorem sum_totient_heads {n : ℕ} (hn : n ≠ 0) (H : Finset ℕ) (hH : ∀ h ∈ H, h ∣ n) :
    ∑ e ∈ n.divisors, (if ∃ h ∈ H, h ∣ e then (n / e).totient else 0) =
      divisorMass (H.image (n / ·)) := by
  classical
  have hS : ∀ s ∈ H.image (n / ·), s ∣ n := by
    intro s hs
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hs
    exact Nat.div_dvd_of_dvd (hH h hh)
  have h1 : ∑ e ∈ n.divisors, (if ∃ h ∈ H, h ∣ e then (n / e).totient else 0) =
      ∑ d ∈ n.divisors, (if ∃ h ∈ H, h ∣ n / d then d.totient else 0) := by
    rw [← Nat.sum_div_divisors n (fun d ↦ if ∃ h ∈ H, h ∣ n / d then d.totient else 0)]
    refine Finset.sum_congr rfl fun e he ↦ ?_
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hn]
  rw [h1, ← Finset.sum_filter, divisorMass, mass, ← upSet_eq_divisorClosure hn hS]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext d
  rw [Finset.mem_filter, mem_upSet_heads hn hH, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, h, hh, hhd⟩
    exact ⟨hd, h, hh, by rw [mul_comm]; exact (Nat.dvd_div_iff_mul_dvd hd).mp hhd⟩
  · rintro ⟨hd, h, hh, hhd⟩
    exact ⟨⟨hd, hn⟩, h, hh, (Nat.dvd_div_iff_mul_dvd hd).mpr (by rw [mul_comm]; exact hhd)⟩

/-- A point of a fibre dominates a head exactly when the fibre's label does. -/
theorem up_inter_fib {n e : ℕ} (hn : Smooth q n) (he : e ∣ n) (H : Finset ℕ)
    (hH : ∀ h ∈ H, h ∣ n) :
    up (H.image (vec q) : Set (ι → ℕ)) ∩ fib (vec q n) (vec q e) =
      if ∃ h ∈ H, h ∣ e then fib (vec q n) (vec q e) else ∅ := by
  classical
  have key : ∀ z ∈ fib (vec q n) (vec q e),
      z ∈ up (H.image (vec q) : Set (ι → ℕ)) ↔ ∃ h ∈ H, h ∣ e := by
    intro z hz
    simp only [up, SetLike.mem_coe, mem_upperClosure, Finset.coe_image, mem_image]
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, hle⟩
      refine ⟨h, hh, (vec_le_iff (hn.of_dvd (hH h hh)) (hn.of_dvd he).1).mp fun i ↦ ?_⟩
      have h1 : vec q h i ≤ z i := hle i
      have h2 : vec q h i ≤ vec q n i :=
        (vec_le_iff (hn.of_dvd (hH h hh)) hn.1).mpr (hH h hh) i
      have h3 : min (z i) (vec q n i) = vec q e i := hz i
      change vec q h i ≤ vec q e i
      omega
    · rintro ⟨h, hh, hhe⟩
      refine ⟨_, ⟨h, hh, rfl⟩, fun i ↦ ?_⟩
      have h1 : vec q h i ≤ vec q e i :=
        (vec_le_iff (hn.of_dvd (hH h hh)) (hn.of_dvd he).1).mpr hhe i
      have h3 : min (z i) (vec q n i) = vec q e i := hz i
      change vec q h i ≤ z i
      omega
  split_ifs with hP
  · exact inter_eq_right.mpr fun z hz ↦ (key z hz).mpr hP
  · exact eq_empty_of_forall_notMem fun z hz ↦ hP ((key z hz.2).mp hz.1)

section LemmaO

variable (hq : ∀ i, (q i).Prime) (hqi : Function.Injective q)
include hq hqi

/-- **Lemma O, untruncated.**  `W(up v(H)) = Π·μ(D({n/h}))/n`. -/
theorem W_up_heads {n : ℕ} (hn : Smooth q n) (H : Finset ℕ) (hH : ∀ h ∈ H, h ∣ n) :
    W (ratio q) (up (H.image (vec q) : Set (ι → ℕ))) =
      (PiN q : ℝ≥0∞) * (divisorMass (H.image (n / ·)) : ℝ≥0∞) / n := by
  classical
  rw [W_eq_sum_fib hq hqi hn, ← sum_totient_heads hn.1 H hH]
  have hterm : ∀ e ∈ n.divisors,
      W (ratio q) (up (H.image (vec q) : Set (ι → ℕ)) ∩ fib (vec q n) (vec q e)) =
        (PiN q : ℝ≥0∞) *
          (((if ∃ h ∈ H, h ∣ e then (n / e).totient else 0 : ℕ)) : ℝ≥0∞) / n := by
    intro e he
    have hed := Nat.dvd_of_mem_divisors he
    rw [up_inter_fib hn hed H hH]
    split_ifs
    · rw [W_fib_vec hq hqi hn hed, ENNReal.coe_div (by exact_mod_cast hn.1), ENNReal.coe_mul]
      simp
    · simp
  rw [Finset.sum_congr rfl hterm, Nat.cast_sum]
  simp only [ENNReal.div_eq_inv_mul, Finset.mul_sum]

/-- **Lemma O, untruncated, as an inequality**: a divisor-mass bound
`μ(D({n/h})) ≤ N` gives `W(up v(H)) ≤ Π·N/n`. -/
theorem W_up_heads_le {n N : ℕ} (hn : Smooth q n) (H : Finset ℕ) (hH : ∀ h ∈ H, h ∣ n)
    (hμ : divisorMass (H.image (n / ·)) ≤ N) :
    W (ratio q) (up (H.image (vec q) : Set (ι → ℕ))) ≤ (PiN q : ℝ≥0∞) * N / n := by
  rw [W_up_heads hq hqi hn H hH]
  gcongr

end LemmaO

end DivisorWeight

end Erdos274
