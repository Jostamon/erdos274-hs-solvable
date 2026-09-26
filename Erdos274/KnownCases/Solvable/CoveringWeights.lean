/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.DivisorWeight
import Erdos274.KnownCases.Solvable.QuotientShadow.Basic
import Mathlib.Algebra.BigOperators.Field

/-! # Generic covering-weight bridge used by solvable closures -/

namespace Erdos274
namespace SevenJoin

open Set QuotientShadow ExpWeight ApexCharging DivisorWeight
open scoped ENNReal NNReal Pointwise

universe u v
/-! ### Heads, local indices and fibre counts -/

section Covering

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

/-- The local index `ℓⱼ = [F : Hⱼ ⊓ F]`. -/
noncomputable def loc (j : κ) : ℕ := (C.parts j).relIndex F

/-- The head `hⱼ = [G : F]/sⱼ`. -/
noncomputable def head (j : κ) : ℕ := F.index / sz C F j

omit [Fintype G] in
theorem card_inf_mul_loc (j : κ) :
    Nat.card (C.parts j ⊓ F : Subgroup G) * loc C F j = Nat.card F := by
  have h := Subgroup.relIndex_inf_mul_relIndex (⊥ : Subgroup G) (C.parts j) F
  rwa [bot_inf_eq, Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h

omit [Fintype G] in
theorem loc_dvd_card (j : κ) : loc C F j ∣ Nat.card G :=
  (Subgroup.relIndex_dvd_card _ _).trans (Subgroup.card_subgroup_dvd_card F)

omit [Fintype G] in
/-- A part is universal exactly when its local index is `1`. -/
theorem le_of_loc_eq_one {j : κ} (h : loc C F j = 1) : F ≤ C.parts j :=
  Subgroup.relIndex_eq_one.mp h

omit [Fintype G] in
/-- **The fibre count as an index sum**: `|Ω|/[G:F] ≤ ∑_{j∈T} 1/[G:Hⱼ]`. -/
theorem ncard_div_le [Finite G] (Ω : Set (G ⧸ F)) (T : Finset κ)
    (hΩ : Nat.card F * Ω.ncard ≤ ∑ j ∈ T, Nat.card (C.parts j)) :
    ((Ω.ncard : ℝ≥0) / F.index : ℝ≥0) ≤ ∑ j ∈ T, ((C.parts j).index : ℝ≥0)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  push_cast
  have hn0 : (0 : ℝ) < F.index := by
    exact_mod_cast Nat.pos_of_ne_zero F.index_ne_zero_of_finite
  have hG : (Nat.card F : ℝ) * F.index = Nat.card G := by
    exact_mod_cast Subgroup.card_mul_index F
  have hterm : ∀ j, ((C.parts j).index : ℝ)⁻¹ = Nat.card (C.parts j) / Nat.card G := fun j ↦ by
    have h : (Nat.card (C.parts j) : ℝ) * (C.parts j).index = Nat.card G := by
      exact_mod_cast (C.parts j).card_mul_index
    have hi : ((C.parts j).index : ℝ) ≠ 0 := by
      exact_mod_cast (C.parts j).index_ne_zero_of_finite
    have hc : (Nat.card (C.parts j) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := C.parts j)).ne'
    rw [← h]
    field_simp
  simp only [hterm, ← Finset.sum_div]
  have hΩ' : (Nat.card F : ℝ) * Ω.ncard ≤ ∑ j ∈ T, (Nat.card (C.parts j) : ℝ) := by
    exact_mod_cast hΩ
  have hG0 : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  rw [div_le_div_iff₀ hn0 hG0, ← hG]
  calc (Ω.ncard : ℝ) * (Nat.card F * F.index) = (Nat.card F * Ω.ncard) * F.index := by ring
    _ ≤ (∑ j ∈ T, (Nat.card (C.parts j) : ℝ)) * F.index := by gcongr

variable [F.Normal]

theorem head_mul_sz (j : κ) : head C F j * sz C F j = F.index :=
  Nat.div_mul_cancel (sz_dvd_index C F j)

theorem head_dvd_index (j : κ) : head C F j ∣ F.index :=
  Dvd.intro _ (head_mul_sz C F j)

theorem index_div_head (j : κ) : F.index / head C F j = sz C F j :=
  Nat.div_div_self (sz_dvd_index C F j) F.index_ne_zero_of_finite

/-- **`[G : Hⱼ] = hⱼ·ℓⱼ`**, the second isomorphism theorem in index form. -/
theorem index_eq_head_mul_loc (j : κ) : (C.parts j).index = head C F j * loc C F j := by
  have h1 := card_eq_mul_sz C F j
  have h2 := card_inf_mul_loc C F j
  have h3 := Subgroup.card_mul_index F
  have h4 := (C.parts j).card_mul_index
  have hs0 := sz_pos C F j
  have hI0 : 0 < Nat.card (C.parts j ⊓ F : Subgroup G) := Nat.card_pos
  obtain ⟨c, hc⟩ := sz_dvd_index C F j
  have hhead : head C F j = c := by rw [head, hc, Nat.mul_div_cancel_left _ hs0]
  rw [hhead]
  refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hI0 hs0) ?_
  calc Nat.card (C.parts j ⊓ F : Subgroup G) * sz C F j * (C.parts j).index
      = Nat.card (C.parts j) * (C.parts j).index := by rw [h1]
    _ = Nat.card F * F.index := by rw [h4, h3]
    _ = Nat.card (C.parts j ⊓ F : Subgroup G) * sz C F j * (c * loc C F j) := by
        rw [← h2, hc]; ring

end Covering

theorem coe_div_nat (N n : ℕ) (hn : n ≠ 0) :
    ((((N : ℝ≥0) / n : ℝ≥0)) : ℝ≥0∞) = (N : ℝ≥0∞) / n := by
  rw [ENNReal.coe_div (by exact_mod_cast hn)]
  simp

/-! ### Exponent data of a covering

The bridge from a covering to exponent vectors, shared by the general step-4
closure (`Step4Closure.false_of_covering`) and the `p = 7` closure below.
Fix primes `q : ι → ℕ` covering the prime divisors of `|G|`.  Per part `j`:
* `vec_head_add_vec_loc`: `v(dⱼ) = v(hⱼ) + v(ℓⱼ)`, from `dⱼ = hⱼℓⱼ`;
* `w_vec_head_add_vec_loc`: its weight is `1/dⱼ`;
* `injOn_vec_head_add_vec_loc`: distinct indices give distinct vectors;
* `W_up_heads_family_le`, `W_up_heads_nonUniv_le`: Lemma O on the heads,
  `W(up{v(hⱼ)}) ≤ Π·|⋃ shadows|/[G:F] ≤ Π·ν`. -/

section ExponentData

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G) [F.Normal]
  {ι : Type*} {q : ι → ℕ}

/-- **`v(dⱼ) = v(hⱼ) + v(ℓⱼ)`**: the index vector splits into head and local
parts. -/
theorem vec_head_add_vec_loc (hsm : Smooth q (Nat.card G)) (j : κ) :
    vec q (head C F j) + vec q (loc C F j) = vec q ((C.parts j).index) := by
  have hsmh : Smooth q (head C F j) :=
    (hsm.of_dvd F.index_dvd_card).of_dvd (head_dvd_index C F j)
  have hsml : Smooth q (loc C F j) := hsm.of_dvd (loc_dvd_card C F j)
  rw [index_eq_head_mul_loc C F j, vec_mul hsmh.1 hsml.1]

variable (hq : ∀ i, (q i).Prime) (hqi : Function.Injective q)
include hq hqi

/-- The weight of `v(hⱼ) + v(ℓⱼ)` is `1/[G : Hⱼ]`. -/
theorem w_vec_head_add_vec_loc [Fintype ι] (hsm : Smooth q (Nat.card G)) (j : κ) :
    w (ratio q) (vec q (head C F j) + vec q (loc C F j)) =
      ((((C.parts j).index : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [vec_head_add_vec_loc C F hsm j, w_vec hq hqi (hsm.of_dvd (C.parts j).index_dvd_card)]

/-- Parts with distinct indices have distinct vectors `v(hⱼ) + v(ℓⱼ)`. -/
theorem injOn_vec_head_add_vec_loc [Finite ι] (hsm : Smooth q (Nat.card G)) {J : Set κ}
    (hdist : Set.InjOn (fun j ↦ (C.parts j).index) J) :
    Set.InjOn (fun j ↦ vec q (head C F j) + vec q (loc C F j)) J := by
  intro a ha b hb h
  simp only [vec_head_add_vec_loc C F hsm] at h
  exact hdist ha hb (vec_injOn hq hqi (hsm.of_dvd (C.parts a).index_dvd_card)
    (hsm.of_dvd (C.parts b).index_dvd_card) h)

/-- **Lemma O on the heads of a family `T`**:
`W(up{v(hⱼ) : j ∈ T}) ≤ Π·|⋃_{j∈T} shadowⱼ|/[G:F]`. -/
theorem W_up_heads_family_le [Fintype ι] [Group.IsSolvable G] (hsm : Smooth q (Nat.card G))
    (T : Finset κ) :
    W (ratio q) (up (((T.image (head C F)).image (vec q) : Finset (ι → ℕ)) :
      Set (ι → ℕ))) ≤
        (PiN q : ℝ≥0∞) * (((((⋃ j ∈ T, shadow C F j).ncard : ℝ≥0) / F.index : ℝ≥0)) :
          ℝ≥0∞) := by
  classical
  have hH : ∀ h ∈ T.image (head C F), h ∣ F.index := by
    intro h hh
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hh
    exact head_dvd_index C F j
  have himg : (T.image (head C F)).image (F.index / ·) = T.image (sz C F) := by
    rw [Finset.image_image]
    exact Finset.image_congr fun j _ ↦ index_div_head C F j
  have hμ := divisorMass_le_ncard_shadows C F T
  rw [← himg] at hμ
  refine (W_up_heads_le hq hqi (hsm.of_dvd F.index_dvd_card) _ hH hμ).trans (le_of_eq ?_)
  rw [coe_div_nat _ _ F.index_ne_zero_of_finite, mul_div_assoc]

/-- **Lemma O over the non-universal parts**: `W(U) ≤ Π·ν`, where `U` is the
up-set of their heads and `ν = ∑ 1/[G : Hⱼ]` over them.  A part meeting a
non-universal shadow is non-universal, so the fibre count stays inside. -/
theorem W_up_heads_nonUniv_le [Fintype ι] [Group.IsSolvable G]
    (hsm : Smooth q (Nat.card G)) :
    W (ratio q) (up ((((nonUniv C F).image (head C F)).image (vec q) : Finset (ι → ℕ)) :
      Set (ι → ℕ))) ≤
        (PiN q : ℝ≥0∞) * ((∑ j ∈ nonUniv C F, ((C.parts j).index : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  classical
  refine (W_up_heads_family_le C F hq hqi hsm _).trans ?_
  gcongr
  refine ncard_div_le C F _ _ (card_mul_ncard_le_of_meet C F _ _ fun k δ hδ hδk ↦ ?_)
  obtain ⟨j, hj, hδj⟩ := Set.mem_iUnion₂.mp hδ
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, not_le_of_meet C F (Finset.mem_filter.mp hj).2 hδj hδk⟩

end ExponentData


end SevenJoin
end Erdos274
