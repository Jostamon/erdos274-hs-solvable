/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Order.BourbakiWitt

/-!
# Coset-counting lemmas in a finite group

Coset-counting lemmas used in the proof of the Herzog–Schönheim conjecture
for finite nilpotent groups (see `docs/erdos274/known-cases/BLUEPRINT.md`).

## Main results

* `Erdos274.card_inf_mul_card_map`: `|H ⊓ K| * |π_K(H)| = |H|` for the
  quotient map `π_K : G → G ⧸ K`, `K` normal.
* `Erdos274.smul_set_inter_smul_set_eq`: two intersecting cosets intersect in
  a coset of the intersection subgroup.
* `Erdos274.ncard_eq_sum_fiber_ncard`: counting a set fiberwise over `G ⧸ K`.
* `Erdos274.ncard_eq_card_mul_ncard_image`: a `P`-saturated set has
  `|P| · |image|` elements.
-/

namespace Erdos274

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- For subgroups `H, K` with `K` normal, `|H ⊓ K| * |π_K(H)| = |H|`,
where `π_K : G → G ⧸ K` is the quotient map. -/
theorem card_inf_mul_card_map (H K : Subgroup G) [K.Normal] :
    Nat.card (H ⊓ K : Subgroup G) * Nat.card (H.map (QuotientGroup.mk' K)) =
      Nat.card H := by
  set f := (QuotientGroup.mk' K).comp H.subtype with hf
  have hker : f.ker = (H ⊓ K).subgroupOf H := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      Subgroup.inf_subgroupOf_left K H]
    rfl
  have hrange : f.range = H.map (QuotientGroup.mk' K) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : Nat.card H =
      Nat.card (↥H ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange,
    hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    at h1
  rw [mul_comm]
  exact h1.symm

omit [Finite G] in
/-- A coset containing `y` equals the `y`-translate of the subgroup. -/
lemma smul_set_eq_of_mem {a y : G} {L : Subgroup G}
    (hy : y ∈ a • (L : Set G)) : a • (L : Set G) = y • (L : Set G) :=
  (leftCoset_eq_iff L).mpr ((mem_leftCoset_iff a).mp hy)

omit [Finite G] in
/-- Cosets absorb right multiplication by subgroup elements. -/
lemma mul_mem_smul_coset {g y h : G} {H : Subgroup G}
    (hy : y ∈ g • (H : Set G)) (hh : h ∈ H) : y * h ∈ g • (H : Set G) := by
  rw [mem_leftCoset_iff] at hy ⊢
  simpa [mul_assoc] using H.mul_mem hy hh

omit [Finite G] in
/-- Two intersecting cosets intersect in a coset of the intersection. -/
theorem smul_set_inter_smul_set_eq {H K : Subgroup G} {g k x : G}
    (hx : x ∈ g • (H : Set G) ∩ k • (K : Set G)) :
    g • (H : Set G) ∩ k • (K : Set G) = x • ((H ⊓ K : Subgroup G) : Set G) := by
  obtain ⟨hxH, hxK⟩ := hx
  rw [smul_set_eq_of_mem hxH, smul_set_eq_of_mem hxK, ← Set.smul_set_inter,
    ← Subgroup.coe_inf]

omit [Finite G] in
/-- A left coset has the cardinality of the subgroup. -/
lemma ncard_smul_coset (x : G) (H : Subgroup G) :
    (x • (H : Set G)).ncard = Nat.card H := by
  rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]

/-- Counting a set fiberwise over the quotient `G ⧸ K`. -/
lemma ncard_eq_sum_fiber_ncard (S : Set G) (K : Subgroup G) [Fintype (G ⧸ K)] :
    S.ncard = ∑ c : G ⧸ K, (S ∩ QuotientGroup.mk ⁻¹' {c}).ncard := by
  classical
  have : Fintype G := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise
      (f := fun x ↦ (QuotientGroup.mk x : G ⧸ K)) (t := Finset.univ)
      (fun x _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

section CosetHelpers

omit [Finite G] in
/-- If `L ⊓ P = ⊥`, the quotient map `G → G ⧸ P` embeds `L`. -/
lemma card_map_mk'_of_inf_eq_bot {L P : Subgroup G} [P.Normal] (h : L ⊓ P = ⊥) :
    Nat.card (L.map (QuotientGroup.mk' P)) = Nat.card L := by
  have h1 := card_inf_mul_card_map L P
  rw [h] at h1
  simpa using h1

omit [Finite G] in
/-- If `P ⊓ Q = ⊥`, the quotient map `G → G ⧸ P` is injective on any coset
of `Q`. -/
lemma injOn_mk_smul_coset_of_inf_eq_bot {P Q : Subgroup G} (hPQ : P ⊓ Q = ⊥)
    (z : G) :
    Set.InjOn (QuotientGroup.mk : G → G ⧸ P) (z • (Q : Set G)) := by
  rintro u hu v hv huv
  obtain ⟨qu, hqu, rfl⟩ := hu
  obtain ⟨qv, hqv, rfl⟩ := hv
  have h1 : (z * qu)⁻¹ * (z * qv) ∈ P := (QuotientGroup.eq).mp huv
  have h2 : (z * qu)⁻¹ * (z * qv) ∈ Q := by
    have : (z * qu)⁻¹ * (z * qv) = qu⁻¹ * qv := by group
    rw [this]
    exact Q.mul_mem (Q.inv_mem hqu) hqv
  have h3 : (z * qu)⁻¹ * (z * qv) = 1 := by
    have := hPQ ▸ Subgroup.mem_inf.mpr ⟨h1, h2⟩
    simpa using this
  have h4 : qu = qv := by
    have h5 : (z * qu)⁻¹ * (z * qv) = qu⁻¹ * qv := by group
    rw [h5] at h3
    exact inv_mul_eq_one.mp h3
  simp [h4]

omit [Finite G] in
/-- The fiber of the quotient map over `mk z` is the coset `z • Q`. -/
lemma preimage_mk_singleton_eq (Q : Subgroup G) (z : G) :
    (QuotientGroup.mk ⁻¹' {(z : G ⧸ Q)} : Set G) = z • (Q : Set G) := by
  change {x : G | (x : G ⧸ Q) = (z : G ⧸ Q)} = z • (Q : Set G)
  exact QuotientGroup.eq_class_eq_leftCoset Q z

section
variable {G' : Type*} [Group G']

omit [Finite G] in
/-- A monoid hom maps a coset onto a coset of the image subgroup. -/
lemma image_smul_coset (f : G →* G') (x : G) (L : Subgroup G) :
    f '' (x • (L : Set G)) = f x • ((L.map f : Subgroup G') : Set G') := by
  rw [Set.image_smul_distrib, Subgroup.coe_map]

end

omit [Finite G] in
/-- A `Finset.biUnion` over the subtype of a finset equals the plain
`biUnion`. -/
lemma biUnion_subtype_univ {κ : Type*} (J : Finset κ)
    (f : κ → Finset ℕ) [Fintype J] :
    (Finset.univ : Finset J).biUnion (fun j ↦ f j) = J.biUnion f := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Subtype.exists,
    exists_prop]

omit [Finite G] in
/-- The image in `G ⧸ K` of a coset of `L` has `|L.map (mk' K)|` elements. -/
lemma ncard_image_mk_smul_coset (K : Subgroup G) [K.Normal] (x : G)
    (L : Subgroup G) :
    ((QuotientGroup.mk '' (x • (L : Set G))) : Set (G ⧸ K)).ncard =
      Nat.card (L.map (QuotientGroup.mk' K)) := by
  rw [show (QuotientGroup.mk : G → G ⧸ K) = (QuotientGroup.mk' K : G →* G ⧸ K)
      from rfl,
    image_smul_coset (QuotientGroup.mk' K) x L, ncard_smul_coset]

/-- A set saturated for the quotient by `P` (closed under the `P`-fibers of
its elements) has cardinality `|P|` times the cardinality of its image. -/
lemma ncard_eq_card_mul_ncard_image {P : Subgroup G} {S : Set G}
    (hsat : ∀ x ∈ S, ∀ y : G,
      (QuotientGroup.mk y : G ⧸ P) = QuotientGroup.mk x → y ∈ S) :
    S.ncard = Nat.card P * (QuotientGroup.mk '' S : Set (G ⧸ P)).ncard := by
  classical
  have : Fintype (G ⧸ P) := Fintype.ofFinite _
  rw [ncard_eq_sum_fiber_ncard S P]
  have hterm : ∀ c : G ⧸ P, (S ∩ QuotientGroup.mk ⁻¹' {c}).ncard =
      if c ∈ QuotientGroup.mk '' S then Nat.card P else 0 := by
    intro c
    by_cases hc : c ∈ QuotientGroup.mk '' S
    · rw [ite_eq_left hc]
      obtain ⟨x, hxS, hxc⟩ := hc
      have hfib_sub : (QuotientGroup.mk ⁻¹' {c} : Set G) ⊆ S := by
        intro y hy
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
        exact hsat x hxS y (by rw [hy, ← hxc])
      rw [Set.inter_eq_self_of_subset_right hfib_sub]
      obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective c
      rw [← hz, preimage_mk_singleton_eq, ncard_smul_coset]
    · rw [ite_eq_right hc]
      have hempty : S ∩ QuotientGroup.mk ⁻¹' {c} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨hyS, hyc⟩
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hyc
        exact hc ⟨y, hyS, hyc⟩
      rw [hempty, Set.ncard_empty]
  rw [Finset.sum_congr rfl (fun c _ ↦ hterm c), Finset.sum_ite,
    Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
  congr 1
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext c
  simp

end CosetHelpers

end Erdos274
