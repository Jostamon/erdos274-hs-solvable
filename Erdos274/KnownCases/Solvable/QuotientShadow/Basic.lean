/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.ExactCovering.Pieces
import Erdos274.KnownCases.Solvable.OrbitUnionBound
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index

/-! # Basic quotient-shadow geometry and divisor mass -/

namespace Erdos274

open MulAction Finset
open scoped Pointwise

universe u v

namespace QuotientShadow

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]
open NormaliserSlice MassForm

section Shadow

variable [Fintype G] (C : Group.ExactCovering G ι) (F : Subgroup G)
/-- The shadow of part `j`: the left `F`-cosets its cell meets. -/
def shadow (j : ι) : Set (G ⧸ F) := {δ | (piece C F j δ).Nonempty}

/-- `sⱼ = [Hⱼ F : F]`: the number of `F`-cosets met by part `j`. -/
noncomputable def sz (j : ι) : ℕ := (shadow C F j).ncard

lemma card_eq_mul_sz (j : ι) :
    Nat.card (C.parts j) = Nat.card (C.parts j ⊓ F : Subgroup G) * sz C F j :=
  card_eq_mul_ncard_hits C F j

lemma sz_pos (j : ι) : 0 < sz C F j := by
  refine Nat.pos_of_ne_zero fun h ↦ ?_
  have := card_eq_mul_sz C F j
  rw [h, mul_zero] at this
  exact Nat.card_pos.ne' this

lemma mem_shadow_iff {j : ι} {δ : G ⧸ F} :
    δ ∈ shadow C F j ↔ ∃ h ∈ C.parts j, ((C.reps j * h : G) : G ⧸ F) = δ := by
  change (piece C F j δ).Nonempty ↔ _
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hc, hδ⟩ := (mem_piece C F).mp hx
    rw [mem_leftCoset_iff] at hc
    exact ⟨_, hc, by simpa using hδ⟩
  · rintro ⟨h, hh, hδ⟩
    refine ⟨C.reps j * h, (mem_piece C F).mpr ⟨?_, hδ⟩⟩
    rw [mem_leftCoset_iff]
    simpa using hh


end Shadow
end QuotientShadow

namespace SevenJoin

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
variable (C : Group.ExactCovering G κ) (F : Subgroup G)

/-- If every part meeting `Ω` belongs to `T`, its preimage is covered by the
cells of `T`. -/
theorem card_mul_ncard_le_of_meet (Ω : Set (G ⧸ F)) (T : Finset κ)
    (hT : ∀ j, ∀ δ ∈ Ω, δ ∈ QuotientShadow.shadow C F j → j ∈ T) :
    Nat.card F * Ω.ncard ≤ ∑ j ∈ T, Nat.card (C.parts j) := by
  classical
  rw [← QuotientShadow.card_ptsOf]
  have hsub : (QuotientGroup.mk ⁻¹' Ω : Set G) ⊆
      (QuotientShadow.ptsOf C T : Set G) := by
    intro z hz
    obtain ⟨k, hk⟩ := C.exists_mem z
    have hks : (z : G ⧸ F) ∈ QuotientShadow.shadow C F k := by
      rw [QuotientShadow.mem_shadow_iff]
      exact ⟨(C.reps k)⁻¹ * z, (mem_leftCoset_iff _).mp hk, by simp⟩
    rw [Finset.mem_coe]
    exact Finset.mem_biUnion.mpr ⟨k, hT k _ hz hks,
      (MassForm.mem_cell C).mpr hk⟩
  have h1 := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset] at h1
  have h2 := QuotientGroup.card_preimage_mk F Ω
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h2
  rw [← h2]
  exact h1

/-- Sharing an `F`-coset with a non-universal part forces non-universality. -/
theorem not_le_of_meet {j k : κ} (hj : ¬ F ≤ C.parts j) {δ : G ⧸ F}
    (hδj : δ ∈ QuotientShadow.shadow C F j)
    (hδk : δ ∈ QuotientShadow.shadow C F k) : ¬ F ≤ C.parts k := by
  intro hle
  obtain ⟨h, hh, hδ⟩ := (QuotientShadow.mem_shadow_iff C F).mp hδj
  obtain ⟨h', hh', hδ'⟩ := (QuotientShadow.mem_shadow_iff C F).mp hδk
  have hq : (C.reps k * h')⁻¹ * (C.reps j * h) ∈ F :=
    QuotientGroup.eq.mp (hδ'.trans hδ.symm)
  have hx : C.reps j * h ∈ C.reps k • (C.parts k : Set G) := by
    have := NormaliserSlice.mul_mem_cell C
      (show C.reps k * h' ∈ C.reps k • (C.parts k : Set G) from
        Set.smul_mem_smul_set hh') (hle hq)
    have e : C.reps k * h' * ((C.reps k * h')⁻¹ * (C.reps j * h)) =
        C.reps j * h := by group
    rwa [e] at this
  have hjc : C.reps j * h ∈ C.reps j • (C.parts j : Set G) :=
    Set.smul_mem_smul_set hh
  have hjk := NormaliserSlice.eq_of_mem_cell C hjc hx
  exact hj (by rw [hjk]; exact hle)

end SevenJoin

namespace QuotientShadow

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]

section Shadow

variable [Fintype G] (C : Group.ExactCovering G ι) (F : Subgroup G)

open Classical in
/-- The non-universal parts: `F ≰ Hⱼ`. -/
noncomputable def nonUniv : Finset ι := univ.filter fun j ↦ ¬ F ≤ C.parts j

/-- `F`-cosets met by non-universal parts contain only non-universal points. -/
lemma card_mul_ncard_le (W : Finset ι) (hW : ∀ j ∈ W, ¬ F ≤ C.parts j)
    (Ω : Set (G ⧸ F)) (hΩ : ∀ δ ∈ Ω, ∃ j ∈ W, δ ∈ shadow C F j) :
    Nat.card F * Ω.ncard ≤ ∑ j ∈ nonUniv C F, Nat.card (C.parts j) := by
  classical
  apply SevenJoin.card_mul_ncard_le_of_meet C F Ω (nonUniv C F)
  intro k δ hδ hδk
  obtain ⟨j, hjW, hδj⟩ := hΩ δ hδ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    SevenJoin.not_le_of_meet C F (hW j hjW) hδj hδk⟩

variable [F.Normal]

/-- The shadow of part `j` is an orbit of a subgroup of `G/F` (left regular
action): the orbit of `gⱼF` under `ḡⱼ H̄ⱼ ḡⱼ⁻¹`. -/
def shK (j : ι) : Subgroup (G ⧸ F) :=
  (C.parts j).map ((MulAut.conj ((C.reps j : G) : G ⧸ F)).toMonoidHom.comp
    (QuotientGroup.mk' F))

lemma orbit_shK (j : ι) :
    orbit (shK C F j) ((C.reps j : G) : G ⧸ F) = shadow C F j := by
  ext δ
  rw [MulAction.mem_orbit_iff, mem_shadow_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hk
    refine ⟨h, hh, ?_⟩
    rw [Subgroup.mk_smul, smul_eq_mul]
    simp [MulAut.conj_apply]
  · rintro ⟨h, hh, rfl⟩
    refine ⟨⟨_, (show _ ∈ shK C F j from Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)⟩, ?_⟩
    rw [Subgroup.mk_smul, smul_eq_mul]
    simp [MulAut.conj_apply]

lemma sz_dvd_index (j : ι) : sz C F j ∣ F.index := by
  rw [sz, ← orbit_shK, ← index_stabilizer]
  exact (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)

/-- Lemma O with `X = 1` on `G/F`, applied to shadows. -/
lemma divisorMass_le_ncard_shadows [Group.IsSolvable G] (W : Finset ι) :
    divisorMass (W.image (sz C F)) ≤ (⋃ j ∈ W, shadow C F j).ncard := by
  classical
  let κ := {j // j ∈ W}
  let K : κ → Subgroup (G ⧸ F) := fun i ↦ shK C F i.1
  let ω : κ → G ⧸ F := fun i ↦ ((C.reps i.1 : G) : G ⧸ F)
  have hO := mass_le_ncard_iUnion_orbit (H := (⊤ : Subgroup (G ⧸ F)))
    (Subgroup.PrimeNormalChain.of_isSolvable (G ⧸ F)) κ ω K (fun _ ↦ le_top)
    (fun i x _ ↦ by
      have hst : stabilizer (G ⧸ F) x = ⊥ := by
        ext k
        simp
      rw [top_inf_eq, hst, Subgroup.card_bot]
      exact Nat.coprime_one_right _)
  have hD : divisorClosure (W.image (sz C F)) ⊆
      univ.biUnion fun i : κ ↦ ((orbit (K i) (ω i)).ncard).divisors := by
    intro d hd
    obtain ⟨t, ht, hdt⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    refine Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
    change d ∈ ((orbit (shK C F j) ((C.reps j : G) : G ⧸ F)).ncard).divisors
    rw [orbit_shK]
    exact hdt
  have hU : (⋃ i, orbit (K i) (ω i)) ⊆ ⋃ j ∈ W, shadow C F j := by
    intro δ hδ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hδ
    change δ ∈ orbit (shK C F i.1) ((C.reps i.1 : G) : G ⧸ F) at hi
    rw [orbit_shK] at hi
    exact Set.mem_iUnion₂.mpr ⟨i.1, i.2, hi⟩
  exact (mass_mono hD).trans (hO.trans (Set.ncard_le_ncard hU))

end Shadow

end QuotientShadow

end Erdos274
