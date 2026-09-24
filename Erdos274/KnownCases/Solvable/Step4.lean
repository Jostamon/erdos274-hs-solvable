/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.SevenCB
import Erdos274.KnownCases.Solvable.Step4Structure
import Erdos274.KnownCases.Solvable.Step4Closure
import Erdos274.KnownCases.Solvable.Step4Criterion
import Erdos274.KnownCases.Solvable.Minimality
import Erdos274.ExactCovering.FiniteIndex

/-!
# Step 4, and the least counterexample

`DECISION_LOG` D98.  A least solvable counterexample to Herzog–Schönheim has
an exact covering with pairwise distinct indices, `k ≥ 2` parts, and HS for
every smaller solvable group.  `false_of_minimal` shows there is none.  Let
`p` be the largest prime of `|G|`.

* `p ≤ 3` (`false_of_small_primes`).  Indices of distinct parts are never
  coprime (`eq_of_coprime_index`), so either every index is even or every
  index is divisible by `3`.  No index is `2` (`index_ne_two`: the other parts
  would partition the index-2 subgroup, a smaller counterexample).  Then
  `∑ 1/dᵢ` falls short of `1` against `∏_{q ∣ |G|} q/(q−1) ≤ 3`.
* `p ≥ 5`.  `Step4Structure.exists_structure` gives `F = KQ ◁ G`.  Some part
  is non-universal, or the covering descends to `G/F`.
  - `p = 7`: `SevenCB.false_of_structure`.
  - `p ≠ 7`: `Step4Closure.false_of_covering`, with (CB) from
    `SevenCB.cb_loc` and the criterion from `Step4Criterion.step4Crit_of_prime`.

**Step 4 is the case `p² ∣ |G|`.  The argument never uses the exponent of
`p`**: the localisation `F = KQ`, (CB), the chambers and the closure hold for
`|Q| = p` too.  So this also closes step 3, and `herzog_schonheim_of_solvable`
is HS for every finite solvable group, by strong induction on `|G|`.
-/

namespace Erdos274

namespace Step4

open QuotientShadow SevenJoin ExpWeight ApexCharging DivisorWeight SevenClosure PrimeOrder
open scoped ENNReal NNReal Pointwise

universe u v

variable {G : Type u} [Group G] {κ : Type v} [Fintype κ]

/-! ### Coprime indices -/

/-- **Coprime indices meet** (M–S Lemma 2.2): two parts with coprime indices
are the same part. -/
theorem eq_of_coprime_index [Finite G] (C : Group.ExactCovering G κ) {i j : κ}
    (h : Nat.Coprime (C.parts i).index (C.parts j).index) : i = j := by
  by_contra hij
  have h' : Nat.Coprime ((C.parts i).relIndex ⊤) ((C.parts j).relIndex ⊤) := by
    rwa [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right]
  obtain ⟨a, ha, b, hb, hab⟩ := Chamber.exists_mul_of_coprime le_top le_top h'
    (Subgroup.mem_top ((C.reps i)⁻¹ * C.reps j))
  have hz : C.reps i * a = C.reps j * b⁻¹ := by
    calc C.reps i * a = C.reps i * ((C.reps i)⁻¹ * C.reps j) * b⁻¹ := by rw [hab]; group
      _ = C.reps j * b⁻¹ := by group
  have hzi : C.reps i * a ∈ C.reps i • (C.parts i : Set G) := by
    rw [mem_leftCoset_iff]
    simpa using ha
  have hzj : C.reps i * a ∈ C.reps j • (C.parts j : Set G) := by
    rw [hz, mem_leftCoset_iff]
    simpa using (C.parts j).inv_mem hb
  exact Set.disjoint_left.mp (C.disjoint (Set.mem_univ i) (Set.mem_univ j) hij) hzi hzj

/-! ### No index `2` -/

/-- **No part of index `2`** in a least counterexample (GS 2011 Lemma 2.3):
the other parts partition the index-2 subgroup, with half the indices. -/
theorem index_ne_two [Finite G] [Group.IsSolvable G] (C : Group.ExactCovering G κ)
    (hinj : Function.Injective fun i ↦ (C.parts i).index)
    (hmin : AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim.{u, v} (Nat.card G))
    (i : κ) : (C.parts i).index ≠ 2 := by
  classical
  intro h2
  set H := C.parts i with hH
  have hHtop : H ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at h2
    norm_num at h2
  obtain ⟨y, hy⟩ : ∃ y, y ∉ H := by
    by_contra hall
    push Not at hall
    exact hHtop (eq_top_iff.mpr fun y _ ↦ hall y)
  set x := C.reps i * y with hx
  -- the two cosets of `H`
  have hmem : ∀ g : G, g ∈ x • (H : Set G) ↔ g ∉ C.reps i • (H : Set G) := by
    intro g
    rw [mem_leftCoset_iff, mem_leftCoset_iff, SetLike.mem_coe, SetLike.mem_coe, hx,
      mul_inv_rev, mul_assoc, Subgroup.mul_mem_iff_of_index_two h2]
    simp [hy]
  -- the parts meeting `xH` lie inside it, and below `H`
  have hcell : ∀ j : C.FiberIndex H x, C.reps j.1 • (C.parts j.1 : Set G) ⊆ x • (H : Set G) := by
    intro j w hw
    rw [hmem]
    intro hwi
    obtain ⟨z, hzj, hzx⟩ := j.2
    have hji : j.1 ≠ i := by
      rintro hji
      rw [hji] at hzj
      exact (hmem z).mp hzx hzj
    exact Set.disjoint_left.mp (C.disjoint (Set.mem_univ j.1) (Set.mem_univ i) hji) hw hwi
  have hle : ∀ j : C.FiberIndex H x, C.parts j.1 ≤ H := by
    intro j h hh
    have h1 : C.reps j.1 ∈ x • (H : Set G) :=
      hcell j (by rw [mem_leftCoset_iff]; simp)
    have h2' : C.reps j.1 * h ∈ x • (H : Set G) :=
      hcell j (by rw [mem_leftCoset_iff]; simpa using hh)
    rw [mem_leftCoset_iff] at h1 h2'
    have := H.mul_mem (H.inv_mem h1) h2'
    simpa [mul_assoc] using this
  have hidx : ∀ j : C.FiberIndex H x,
      (C.parts j.1).index = H.index * ((C.fiberCover H x).parts j).index := by
    intro j
    change _ = H.index * ((C.parts j.1).subgroupOf H).index
    rw [mul_comm]
    exact (Subgroup.relIndex_mul_index (hle j)).symm
  have hnoti : ∀ j : C.FiberIndex H x, j.1 ≠ i := by
    intro j hji
    obtain ⟨z, hzj, hzx⟩ := j.2
    rw [hji] at hzj
    exact (hmem z).mp hzx hzj
  -- at least two parts meet `xH`
  have hcard : 1 < Fintype.card (C.FiberIndex H x) := by
    by_contra hle1
    have hpos : 0 < Fintype.card (C.FiberIndex H x) :=
      Fintype.card_pos_iff.mpr (C.fiberIndex_nonempty H x)
    have hc1 : Fintype.card (C.FiberIndex H x) = 1 := by omega
    obtain ⟨j₀, hj₀⟩ := Fintype.card_eq_one_iff.mp hc1
    have hs := fiberCover_sum_inv_index C H x
    rw [Fintype.sum_eq_single j₀ fun j hj ↦ absurd (hj₀ j) hj] at hs
    have h1 : ((C.fiberCover H x).parts j₀).index = 1 := by
      have : (((C.fiberPart (x := x) H j₀).index : ℕ) : ℚ) = 1 := inv_eq_one.mp hs
      exact_mod_cast this
    have hj : (C.parts j₀.1).index = (C.parts i).index := by
      rw [hidx j₀, h1, h2]
    exact hnoti j₀ (hinj hj)
  exact Group.ExactCovering.no_properCounterexampleSubpartition_of_solvable_minimality C hinj
    hmin ⟨H, C.FiberIndex H x, inferInstance, C.fiberCover H x,
      ⟨Subtype.val, Subtype.val_injective⟩, lt_top_iff_ne_top.mpr hHtop, hcard, hidx⟩

/-! ### `p ≤ 3` -/

/-- **No counterexample whose primes are at most `3`.** -/
theorem false_of_small_primes [Finite G] (C : Group.ExactCovering G κ)
    (hκ : 1 < Fintype.card κ) (hinj : Function.Injective fun i ↦ (C.parts i).index)
    (hno2 : ∀ i, (C.parts i).index ≠ 2) (h3 : ∀ q, q.Prime → q ∣ Nat.card G → q ≤ 3) :
    False := by
  classical
  set n := Nat.card G with hndef
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  set d : κ → ℕ := fun i ↦ (C.parts i).index with hd
  have hdn : ∀ i, d i ∣ n := fun i ↦ (C.parts i).index_dvd_card
  have hd1 : ∀ i, d i ≠ 1 := fun i h ↦
    C.part_ne_top_of_one_lt_card hκ i (Subgroup.index_eq_one.mp h)
  have hd0 : ∀ i, d i ≠ 0 := fun i ↦ (C.parts i).index_ne_zero_of_finite
  -- the prime factors of an index are `2` or `3`
  have hpf : ∀ i, ∀ r, r.Prime → r ∣ d i → r = 2 ∨ r = 3 := by
    intro i r hr hri
    have := h3 r hr ((hri.trans (hdn i)))
    interval_cases r <;> simp_all (config := { decide := true })
  -- every index is even, or every index is divisible by `3`
  have hcase : (∀ i, 2 ∣ d i) ∨ (∀ i, 3 ∣ d i) := by
    by_contra hno
    push Not at hno
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hno
    have hcop : Nat.Coprime (d i) (d j) := by
      refine Nat.coprime_of_dvd fun r hr hri hrj ↦ ?_
      rcases hpf j r hr hrj with rfl | rfl
      · exact hi hri
      · exact hj hrj
    have hij := eq_of_coprime_index C hcop
    subst hij
    rcases Nat.exists_prime_and_dvd (hd1 i) with ⟨r, hr, hri⟩
    rcases hpf i r hr hri with rfl | rfl
    · exact hi hri
    · exact hj hri
  -- the coordinates
  let ι := {x // x ∈ n.primeFactors}
  let q : ι → ℕ := Subtype.val
  have hq : ∀ i, (q i).Prime := fun i ↦ Nat.prime_of_mem_primeFactors i.2
  have hqi : Function.Injective q := Subtype.val_injective
  have hsm : Smooth q n := ⟨hn0, fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hsmd : ∀ i, Smooth q (d i) := fun i ↦ hsm.of_dvd (hdn i)
  have hinjv : Set.InjOn (fun i ↦ vec q (d i)) (Finset.univ : Finset κ) :=
    fun a _ b _ h ↦ hinj (vec_injOn hq hqi (hsmd a) (hsmd b) h)
  -- `∑ 1/dᵢ = 1` and `Π ≤ 3`
  have hsum : ∑ i, w (ratio q) (vec q (d i)) = 1 := by
    have hQ := exactCovering_sum_inv_index_of_finite C
    have hR : ∑ i, ((d i : ℝ≥0)⁻¹ : ℝ≥0) = 1 := by
      rw [← NNReal.coe_inj]
      have h := congrArg (Rat.cast : ℚ → ℝ) hQ
      push_cast at h ⊢
      exact h
    rw [Finset.sum_congr rfl fun i _ ↦ w_vec hq hqi (hsmd i), ← ENNReal.ofNNReal_finsetSum, hR]
    rfl
  have hPi : (PiN q : ℝ≥0∞) ≤ 3 := by
    have h := Step4Closure.prod_le_piBelow Nat.prime_three (Q := n.primeFactors) fun x hx ↦
      ⟨Nat.prime_of_mem_primeFactors hx,
        h3 x (Nat.prime_of_mem_primeFactors hx) (Nat.dvd_of_mem_primeFactors hx)⟩
    have hp3 : piBelow 3 = 2 := by
      rw [piBelow_def, show Nat.primesBelow 3 = {2} by decide]
      simp [mertensProd]
      norm_num
    rw [hp3] at h
    have hPiR : (PiN q : ℝ) ≤ 3 := by
      refine le_trans (le_of_eq ?_) (h.trans (by norm_num))
      rw [PiN, NNReal.coe_prod, ← Finset.prod_coe_sort n.primeFactors]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [NNReal.coe_inv, coe_one_sub_ratioN hq i]
    have : PiN q ≤ 3 := by exact_mod_cast hPiR
    exact_mod_cast this
  have hWu : W (ratio q) Set.univ = (PiN q : ℝ≥0∞) := W_univ_ratio hq
  -- an extra point of the target set, not an index
  -- a target set containing every index vector and one more point has weight above `1`
  have hkey : ∀ (S : Set (ι → ℕ)) (x : ι → ℕ), x ∈ S → (∀ i, x ≠ vec q (d i)) →
      (∀ i, vec q (d i) ∈ S) → 1 + w (ratio q) x ≤ W (ratio q) S := by
    intro S x hxS hx hS
    set T := (Finset.univ : Finset κ).image fun i ↦ vec q (d i) with hT
    have hxT : x ∉ T := by
      rw [hT, Finset.mem_image]
      rintro ⟨i, -, hi⟩
      exact hx i hi.symm
    have hsumT : ∑ z ∈ T, w (ratio q) z = 1 := by
      rw [hT, Finset.sum_image hinjv]
      exact hsum
    calc 1 + w (ratio q) x = W (ratio q) ((insert x T : Finset (ι → ℕ)) : Set (ι → ℕ)) := by
          rw [W_finset, Finset.sum_insert hxT, hsumT, add_comm]
      _ ≤ W (ratio q) S := by
          refine W_mono fun z hz ↦ ?_
          rw [Finset.coe_insert] at hz
          rcases hz with rfl | hz
          · exact hxS
          · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
            exact hS i
  -- the extra point `t·n`
  have hsmt : ∀ t, t ∣ n → Smooth q (t * n) := by
    intro t ht
    have ht0 : t ≠ 0 := fun h ↦ hn0 (Nat.eq_zero_of_zero_dvd (h ▸ ht))
    refine ⟨Nat.mul_ne_zero ht0 hn0, fun x hx ↦ ?_⟩
    rw [Nat.primeFactors_mul ht0 hn0, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact ⟨⟨x, Nat.primeFactors_mono ht hn0 hx⟩, rfl⟩
    · exact ⟨⟨x, hx⟩, rfl⟩
  have hnew : ∀ t, 1 < t → t ∣ n → ∀ i, vec q (t * n) ≠ vec q (d i) := by
    intro t ht htn i h
    have := vec_injOn hq hqi (hsmt t htn) (hsmd i) h
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (hdn i)
    rw [← this] at hle
    nlinarith [Nat.pos_of_ne_zero hn0]
  have hwpos : ∀ t, t ∣ n → w (ratio q) (vec q (t * n)) ≠ 0 := by
    intro t htn
    rw [w_vec hq hqi (hsmt t htn), ne_eq, ENNReal.coe_eq_zero, inv_eq_zero, Nat.cast_eq_zero]
    exact (hsmt t htn).1
  obtain ⟨i₀⟩ : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  rcases hcase with h2 | h3'
  · -- every index is even, and none is `2`
    have h2n : 2 ∣ n := (h2 i₀).trans (hdn i₀)
    have hs2 : Smooth q 2 := hsm.of_dvd h2n
    have hn1 : 1 < n := by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (hdn i₀)
      have := hd1 i₀
      have := hd0 i₀
      omega
    set S := shift (vec q 2) Set.univ \ {vec q 2} with hS
    have hin : ∀ z, vec q 2 ≤ z → z ≠ vec q 2 → z ∈ S := fun z hz hne ↦
      ⟨mem_shift.mpr ⟨hz, Set.mem_univ _⟩, hne⟩
    have hk := hkey S (vec q (2 * n))
      (hin _ ((vec_le_iff hs2 (hsmt 2 h2n).1).mpr (Dvd.intro n rfl))
        fun h ↦ by
          have := vec_injOn hq hqi (hsmt 2 h2n) hs2 h
          omega)
      (hnew 2 (by norm_num) h2n)
      fun i ↦ hin _ ((vec_le_iff hs2 (hd0 i)).mpr (h2 i))
        fun h ↦ hno2 i (vec_injOn hq hqi (hsmd i) hs2 h)
    have hsplit : W (ratio q) S + w (ratio q) (vec q 2) =
        W (ratio q) (shift (vec q 2) Set.univ) := by
      have hsub : {vec q 2} ⊆ shift (vec q 2) Set.univ := by
        rw [Set.singleton_subset_iff]
        exact mem_shift.mpr ⟨le_rfl, Set.mem_univ _⟩
      rw [← W_singleton, ← W_union_of_disjoint Set.disjoint_sdiff_left,
        Set.sdiff_union_of_subset hsub]
    rw [W_shift, hWu, w_vec hq hqi hs2] at hsplit
    have hbound : 1 + w (ratio q) (vec q (2 * n)) + ((((2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤
        1 + ((((2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      calc 1 + w (ratio q) (vec q (2 * n)) + ((((2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)
          ≤ W (ratio q) S + ((((2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by gcongr
        _ = ((((2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * (PiN q : ℝ≥0∞) := hsplit
        _ ≤ ((((2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * 3 := by gcongr
        _ = 1 + ((((2 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.coe_ofNat, ← ENNReal.coe_one, ← ENNReal.coe_mul, ← ENNReal.coe_add]
          congr 1
          rw [← NNReal.coe_inj]
          push_cast
          norm_num
    have hb := (ENNReal.add_le_add_iff_right ENNReal.coe_ne_top).mp hbound
    exact (ENNReal.lt_add_right ENNReal.one_ne_top (hwpos 2 h2n)).not_ge hb
  · -- every index is divisible by `3`
    have h3n : 3 ∣ n := (h3' i₀).trans (hdn i₀)
    have hs3 : Smooth q 3 := hsm.of_dvd h3n
    set S := shift (vec q 3) Set.univ with hS
    have hin : ∀ z, vec q 3 ≤ z → z ∈ S := fun z hz ↦ mem_shift.mpr ⟨hz, Set.mem_univ _⟩
    have hk := hkey S (vec q (3 * n))
      (hin _ ((vec_le_iff hs3 (hsmt 3 h3n).1).mpr (Dvd.intro n rfl)))
      (hnew 3 (by norm_num) h3n)
      fun i ↦ hin _ ((vec_le_iff hs3 (hd0 i)).mpr (h3' i))
    rw [hS, W_shift, hWu, w_vec hq hqi hs3] at hk
    have hb : 1 + w (ratio q) (vec q (3 * n)) ≤ 1 := by
      refine hk.trans ?_
      calc ((((3 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * (PiN q : ℝ≥0∞)
          ≤ ((((3 : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) * 3 := by gcongr
        _ = 1 := by
          rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_one]
          congr 1
          rw [← NNReal.coe_inj]
          push_cast
          norm_num
    exact (ENNReal.lt_add_right ENNReal.one_ne_top (hwpos 3 h3n)).not_ge hb

/-! ### The least counterexample -/

/-- **A least solvable counterexample does not exist.**  `G` is finite and
solvable, `C` an exact covering with at least two parts and pairwise distinct
indices, and every smaller finite solvable group satisfies HS. -/
theorem false_of_minimal [Finite G] [Group.IsSolvable G] (C : Group.ExactCovering G κ)
    (hκ : 1 < Fintype.card κ) (hinj : Function.Injective fun i ↦ (C.parts i).index)
    (hmin : AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim.{u, v} (Nat.card G)) :
    False := by
  classical
  have := Fintype.ofFinite G
  have hnt : Nontrivial G := exactCovering_nontrivial_of_one_lt_card C hκ
  set n := Nat.card G with hndef
  have hn1 : 1 < n := Finite.one_lt_card
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
  -- `p`, the largest prime of `|G|`
  set p := n.primeFactors.max' hne with hpdef
  have hpmem : p ∈ n.primeFactors := Finset.max'_mem _ _
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpG : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
  have hmax : ∀ q, q.Prime → q ∣ n → q ≤ p := fun q hq hqn ↦
    Finset.le_max' _ _ (Nat.mem_primeFactors.mpr ⟨hq, hqn, Nat.card_pos.ne'⟩)
  by_cases hp3 : p ≤ 3
  · exact false_of_small_primes C hκ hinj (index_ne_two C hinj hmin)
      fun q hq hqn ↦ (hmax q hq hqn).trans hp3
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, Q, hKn, hFn, hQ, hQne, hK, hKQ⟩ := Step4Structure.exists_structure (p := p) hpG
  set F := K ⊔ Q with hF
  have hdist : Set.InjOn (fun j ↦ (C.parts j).index) (nonUniv C F) := hinj.injOn
  -- some part is non-universal, or the covering descends to `G/F`
  have hneU : (nonUniv C F).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hall : ∀ j, F ≤ C.parts j := fun j ↦ by
      by_contra h
      have hj : j ∈ nonUniv C F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hempty] at hj
      exact Finset.notMem_empty _ hj
    have hker : ∀ i, (QuotientGroup.mk' F).ker ≤ C.parts i := fun i ↦ by
      rw [QuotientGroup.ker_mk']
      exact hall i
    set C' := C.map (QuotientGroup.mk' F) (QuotientGroup.mk'_surjective F) hker
    have hidx : ∀ i, (C'.parts i).index = (C.parts i).index := fun i ↦
      Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective F) (hker i)
    have hFbot : F ≠ ⊥ := fun h ↦ hQne (eq_bot_iff.mpr (h ▸ le_sup_right))
    have hcard : Nat.card (G ⧸ F) < Nat.card G := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup F
      have h2 : 1 < Nat.card F := by
        rw [Finite.one_lt_card_iff_nontrivial]
        exact (Subgroup.nontrivial_iff_ne_bot F).mpr hFbot
      have h3 : 0 < Nat.card (G ⧸ F) := Nat.card_pos
      rw [h1]
      nlinarith
    obtain ⟨a, b, hab, heq⟩ := hmin (G ⧸ F) hcard κ C' hκ
    exact hab (hinj (show (C.parts a).index = (C.parts b).index by
      rw [← hidx a, ← hidx b]; exact heq))
  have h5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by rintro h; rw [h] at hp; norm_num at hp
    omega
  by_cases hp7 : p = 7
  · have hmax7 : ∀ q, q.Prime → q ∣ Nat.card G → q ≤ 7 := hp7 ▸ hmax
    have hQ7 : IsPGroup 7 Q := hp7 ▸ hQ
    have hK7 : ¬ 7 ∣ Nat.card K := hp7 ▸ hK
    exact SevenCB.false_of_structure C F hF hQ7 hK7 hKQ hmax7 hdist hneU
  · refine Step4Closure.false_of_covering C F hpG hmax hdist hneU (fun j hj ↦ ?_)
      (Step4Criterion.step4Crit_of_prime hp h5 hp7)
    by_cases hpj : p ∣ loc C F j
    · exact Or.inl hpj
    right
    obtain ⟨q, hq, hqK, hdvd⟩ :=
      SevenCB.cb_loc C F hF hQ hK hKQ (Finset.mem_filter.mp hj).2 hpj
    have hqG : q ∣ n := hqK.trans (Subgroup.card_subgroup_dvd_card K)
    have hqp : q ≠ p := fun h ↦ hK (h ▸ hqK)
    exact ⟨q, hq, lt_of_le_of_ne (hmax q hq hqG) hqp, hdvd⟩

/-- **Herzog–Schönheim for finite solvable groups.**  In a partition of a
finite solvable group into at least two left cosets, two of the subgroups have
the same index. -/
theorem herzog_schonheim_of_solvable (G : Type u) [Group G] [Finite G]
    [Group.IsSolvable G] : GroupSatisfiesHerzogSchonheim.{u, v} G := by
  suffices h : ∀ N : ℕ, ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G = N → GroupSatisfiesHerzogSchonheim.{u, v} G from h _ G rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro G _ _ _ hG ι _ P hι
    by_contra hno
    push Not at hno
    have hinj : Function.Injective fun i ↦ (P.parts i).index := fun i j h ↦ by
      by_contra hij
      exact hno i j hij h
    have hmin : AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim.{u, v} (Nat.card G) :=
      fun Q _ _ _ hQ ↦ ih (Nat.card Q) (hG ▸ hQ) Q rfl
    exact false_of_minimal P hι hinj hmin

end Step4

end Erdos274
