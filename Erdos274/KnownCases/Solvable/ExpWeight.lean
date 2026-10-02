/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Group.Indicator


/-!
# The untruncated product-geometric weight on `ι → ℕ`

`DECISION_LOG` D98 §§13–14.  The `p = 7` closure of step 4 compares index
sums `∑ 1/d` with the reciprocal mass of translated up-sets.  It needs the
translation identity `W(S + e) = w(e)·W(S)` **with equality**: it subtracts
`W(U + 3e₂ + e₇)`, so the one-sided box bound of `BoxShift.sum_weight_shiftUp_le`
is not enough.  Equality holds without truncation, so this file works on all
of `ι → ℕ`, with values in `ℝ≥0∞`, where every sum exists.

For ratios `r : ι → ℝ≥0∞`,

    w(z) = ∏ᵢ rᵢ^{zᵢ},        W(S) = ∑_{z ∈ S} w(z).

With `rᵢ = 1/qᵢ`, `w(v(d)) = 1/d`, so `W` is the reciprocal mass of the
exact-covering language.

* `W_mono`, `W_union_add_inter`, `W_union_of_disjoint`, `W_singleton`,
  `W_finset`: `W` is a measure on the discrete space, in the form needed.
* `W_shift`: `W(S + e) = w(e)·W(S)`, exactly.
* `W_pi`: the mass of a product set is the product of the coordinate
  masses (`tsum_pi`).
* `W_univ`: `W(ℕ^ι) = ∏ᵢ (1 − rᵢ)⁻¹`, the Mertens product `Π` when
  `rᵢ = 1/qᵢ`.  This is where `Π` comes from; it is not an input.

This file imports only `Mathlib.*`.
-/

@[expose] public section

namespace Erdos274

namespace ExpWeight

open scoped ENNReal
open Set

variable {ι : Type*} [Fintype ι]

/-- The product-geometric weight `w(z) = ∏ᵢ rᵢ^{zᵢ}`. -/
noncomputable def w (r : ι → ℝ≥0∞) (z : ι → ℕ) : ℝ≥0∞ := ∏ i, r i ^ z i

/-- The untruncated mass `W(S) = ∑_{z ∈ S} w(z)`. -/
noncomputable def W (r : ι → ℝ≥0∞) (S : Set (ι → ℕ)) : ℝ≥0∞ :=
  ∑' z, S.indicator (w r) z

/-- The translate `S + e`. -/
def shift (e : ι → ℕ) (S : Set (ι → ℕ)) : Set (ι → ℕ) := (· + e) '' S

variable {r : ι → ℝ≥0∞}

theorem w_add (r : ι → ℝ≥0∞) (a b : ι → ℕ) : w r (a + b) = w r a * w r b := by
  simp only [w, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

omit [Fintype ι] in
theorem mem_shift {e : ι → ℕ} {S : Set (ι → ℕ)} {z : ι → ℕ} :
    z ∈ shift e S ↔ e ≤ z ∧ z - e ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun i ↦ Nat.le_add_left _ _, ?_⟩
    have : y + e - e = y := funext fun i ↦ Nat.add_sub_cancel (y i) (e i)
    rwa [this]
  · rintro ⟨hez, hz⟩
    exact ⟨z - e, hz, funext fun i ↦ Nat.sub_add_cancel (hez i)⟩

omit [Fintype ι] in
theorem add_mem_shift {e : ι → ℕ} {S : Set (ι → ℕ)} {y : ι → ℕ} (hy : y ∈ S) :
    y + e ∈ shift e S :=
  ⟨y, hy, rfl⟩

/-! ### `W` is a measure on the discrete space -/

theorem W_mono {S T : Set (ι → ℕ)} (h : S ⊆ T) : W r S ≤ W r T :=
  ENNReal.tsum_le_tsum fun z ↦ indicator_le_indicator_of_subset h (fun _ ↦ zero_le) z

/-- Inclusion–exclusion for two sets, in the additive form `ℝ≥0∞` wants. -/
theorem W_union_add_inter (S T : Set (ι → ℕ)) :
    W r (S ∪ T) + W r (S ∩ T) = W r S + W r T := by
  simp only [W, ← ENNReal.tsum_add]
  exact tsum_congr fun z ↦ indicator_union_add_inter_apply (w r) S T z

@[simp] theorem W_empty : W r ∅ = 0 := by simp [W]

theorem W_union_of_disjoint {S T : Set (ι → ℕ)} (h : Disjoint S T) :
    W r (S ∪ T) = W r S + W r T := by
  have := W_union_add_inter (r := r) S T
  rwa [h.inter_eq, W_empty, add_zero] at this

theorem W_union_le (S T : Set (ι → ℕ)) : W r (S ∪ T) ≤ W r S + W r T := by
  rw [← W_union_add_inter]
  exact le_self_add

theorem W_singleton (z : ι → ℕ) : W r {z} = w r z := by
  rw [W, tsum_eq_single z fun y hy ↦ indicator_of_notMem (by simpa using hy) _]
  exact indicator_of_mem rfl _

theorem W_finset (s : Finset (ι → ℕ)) : W r (s : Set (ι → ℕ)) = ∑ z ∈ s, w r z := by
  exact (sum_eq_tsum_indicator (w r) s).symm

/-! ### Translation is exact -/

/-- **`W(S + e) = w(e)·W(S)`.**  Translation by `e` is injective and multiplies
every weight by `w(e)`; there is no boundary to lose mass at. -/
theorem W_shift (e : ι → ℕ) (S : Set (ι → ℕ)) : W r (shift e S) = w r e * W r S := by
  have hinj : Function.Injective (· + e : (ι → ℕ) → ι → ℕ) := add_left_injective e
  have hsupp : Function.support ((shift e S).indicator (w r)) ⊆ range (· + e) :=
    (support_indicator_subset).trans (image_subset_range _ _)
  rw [W, ← hinj.tsum_eq hsupp, W, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y ↦ ?_
  by_cases hy : y ∈ S
  · rw [indicator_of_mem (add_mem_shift hy), indicator_of_mem hy, w_add, mul_comm]
  · rw [indicator_of_notMem, indicator_of_notMem hy, mul_zero]
    rintro ⟨y', hy', h⟩
    exact hy (hinj h ▸ hy')

/-- A single translate: `W(y + ℕⁿ) = w(y)·W(ℕⁿ)`, the mass of the principal
up-set of `y`. -/
theorem W_Ici (y : ι → ℕ) : W r (Ici y) = w r y * W r univ := by
  rw [← W_shift]
  congr 1
  ext z
  simp [mem_shift]

/-! ### Product sets, and the total mass -/

theorem tsum_pi_fin : ∀ (n : ℕ) (f : Fin n → ℕ → ℝ≥0∞),
    ∑' z : Fin n → ℕ, ∏ i, f i (z i) = ∏ i, ∑' m, f i m
  | 0, f => by
    rw [tsum_eq_single (Fin.elim0 : Fin 0 → ℕ) fun b hb ↦ (hb (Subsingleton.elim _ _)).elim]
    simp
  | n + 1, f => by
    rw [← (Fin.consEquiv fun _ ↦ ℕ).tsum_eq (fun z ↦ ∏ i, f i (z i)), ENNReal.tsum_prod']
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, tsum_pi_fin n (fun i ↦ f i.succ)]

/-- A sum of products over `ι → ℕ` is the product of the coordinate sums. -/
theorem tsum_pi (f : ι → ℕ → ℝ≥0∞) : ∑' z : ι → ℕ, ∏ i, f i (z i) = ∏ i, ∑' m, f i m := by
  let e := Fintype.equivFin ι
  rw [← (e.arrowCongr (Equiv.refl ℕ)).symm.tsum_eq]
  have h1 : ∀ y : Fin (Fintype.card ι) → ℕ,
      ∏ i, f i ((e.arrowCongr (Equiv.refl ℕ)).symm y i) = ∏ k, f (e.symm k) (y k) := fun y ↦
    Fintype.prod_equiv e _ _ fun i ↦ by simp [Equiv.arrowCongr]
  simp only [h1]
  rw [tsum_pi_fin]
  exact (Fintype.prod_equiv e _ _ fun i ↦ by simp).symm

/-- **The mass of a product set** is the product of the coordinate masses. -/
theorem W_pi (C : ι → Set ℕ) :
    W r (univ.pi C) = ∏ i, ∑' m, (C i).indicator (r i ^ ·) m := by
  rw [W, ← tsum_pi]
  refine tsum_congr fun z ↦ ?_
  by_cases hz : z ∈ univ.pi C
  · rw [indicator_of_mem hz, w]
    exact Finset.prod_congr rfl fun i _ ↦ (indicator_of_mem (hz i (mem_univ i)) _).symm
  · rw [indicator_of_notMem hz]
    obtain ⟨i, hi⟩ : ∃ i, z i ∉ C i := by simpa [Set.mem_univ_pi] using hz
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm

/-- **`W(ℕ^ι) = ∏ᵢ (1 − rᵢ)⁻¹`.**  With `rᵢ = 1/qᵢ` this is `∏ qᵢ/(qᵢ − 1)`. -/
theorem W_univ (r : ι → ℝ≥0∞) : W r univ = ∏ i, (1 - r i)⁻¹ := by
  rw [← Set.pi_univ, W_pi]
  simp [ENNReal.tsum_geometric]

/-! ### Generic weight bookkeeping -/

variable {ι κ : Type*} [Fintype ι] {r : ι → ℝ≥0∞}

theorem W_biUnion_le {α : Type*} (r : ι → ℝ≥0∞) (s : Finset α)
    (S : α → Set (ι → ℕ)) :
    W r (⋃ x ∈ s, S x) ≤ ∑ x ∈ s, W r (S x) := by
  simpa only [W, ← tsum_subtype] using ENNReal.tsum_biUnion_le (w r) s S

theorem sum_le_W_of_mapsTo (J : Finset κ) (g : κ → ι → ℕ)
    (hinj : Set.InjOn g J) {S : Set (ι → ℕ)} (hS : ∀ p ∈ J, g p ∈ S) :
    ∑ p ∈ J, w r (g p) ≤ W r S := by
  classical
  rw [← Finset.sum_image hinj, ← W_finset]
  refine W_mono fun z hz ↦ ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
  exact hS p hp

/-- The weights of distinct points in a finite family, together with one new
point, are bounded by the weight of any set containing them. -/
theorem sum_add_weight_le_W_of_injOn {κ : Type*}
    (J : Finset κ) (f : κ → ι → ℕ) (hinj : Set.InjOn f J)
    (x : ι → ℕ) (S : Set (ι → ℕ)) (hx : x ∈ S)
    (hxnot : ∀ j ∈ J, x ≠ f j) (hS : ∀ j ∈ J, f j ∈ S) :
    (∑ j ∈ J, w r (f j)) + w r x ≤ W r S := by
  classical
  let T := J.image f
  have hxT : x ∉ T := by
    intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    exact hxnot j hj heq.symm
  calc (∑ j ∈ J, w r (f j)) + w r x
      = W r ((insert x T : Finset (ι → ℕ)) : Set (ι → ℕ)) := by
          rw [W_finset, Finset.sum_insert hxT, Finset.sum_image hinj]
          simp [add_comm]
    _ ≤ W r S := W_mono fun z hz ↦ by
          rw [Finset.coe_insert] at hz
          rcases hz with rfl | hz
          · exact hx
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
            exact hS j hj

theorem W_image_add (s : Finset (ι → ℕ)) (e : ι → ℕ) :
    W r ((s.image (· + e) : Finset (ι → ℕ)) : Set (ι → ℕ)) =
      w r e * ∑ h ∈ s, w r h := by
  rw [W_finset, Finset.sum_image (fun x _ y _ hxy ↦ add_right_cancel hxy), Finset.mul_sum]
  exact Finset.sum_congr rfl fun h _ ↦ by rw [w_add, mul_comm]

theorem w_ne_top (hr : ∀ k, r k ≠ ⊤) (z : ι → ℕ) : w r z ≠ ⊤ :=
  ENNReal.prod_ne_top fun k _ ↦ ENNReal.pow_ne_top (hr k)

theorem w_ne_zero (hr0 : ∀ k, r k ≠ 0) (z : ι → ℕ) : w r z ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (hr0 k)

theorem one_le_W_univ : 1 ≤ W r univ := by
  have hzero : w r 0 = 1 := by simp [w]
  rw [← hzero, ← W_singleton]
  exact W_mono (subset_univ _)

end ExpWeight

/-! ### Compatibility wrappers for the original SevenClosure names -/

namespace SevenClosure

open Set ExpWeight
open scoped ENNReal

variable {ι κ : Type*} [Fintype ι] {r : ι → ℝ≥0∞}

theorem W_biUnion_le {α : Type*} (r : ι → ℝ≥0∞) (s : Finset α)
    (S : α → Set (ι → ℕ)) :
    W r (⋃ x ∈ s, S x) ≤ ∑ x ∈ s, W r (S x) := ExpWeight.W_biUnion_le r s S

theorem sum_le_W_of_mapsTo (J : Finset κ) (g : κ → ι → ℕ)
    (hinj : Set.InjOn g J) {S : Set (ι → ℕ)} (hS : ∀ p ∈ J, g p ∈ S) :
    ∑ p ∈ J, w r (g p) ≤ W r S := ExpWeight.sum_le_W_of_mapsTo J g hinj hS

theorem W_image_add (s : Finset (ι → ℕ)) (e : ι → ℕ) :
    W r ((s.image (· + e) : Finset (ι → ℕ)) : Set (ι → ℕ)) =
      w r e * ∑ h ∈ s, w r h := ExpWeight.W_image_add s e

theorem w_ne_top (hr : ∀ k, r k ≠ ⊤) (z : ι → ℕ) : w r z ≠ ⊤ := ExpWeight.w_ne_top hr z

theorem w_ne_zero (hr0 : ∀ k, r k ≠ 0) (z : ι → ℕ) : w r z ≠ 0 := ExpWeight.w_ne_zero hr0 z

theorem one_le_W_univ : 1 ≤ W r univ := ExpWeight.one_le_W_univ
end SevenClosure

end Erdos274
