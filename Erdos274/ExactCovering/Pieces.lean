/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.ExactCovering.Cells
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Finite


/-! # Exact-covering cells restricted to quotient cosets -/

@[expose] public section

namespace Erdos274

open Finset
open scoped Pointwise

universe u v

namespace NormaliserSlice

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]

section Pieces

variable [Fintype G] (C : Group.ExactCovering G ι) (N : Subgroup G)

open Classical in
/-- The part `i` restricted to the left `N`-coset `δ`. -/
noncomputable def piece (i : ι) (δ : G ⧸ N) : Finset G :=
  univ.filter fun x ↦ x ∈ C.reps i • (C.parts i : Set G) ∧ (x : G ⧸ N) = δ

lemma mem_piece {i : ι} {δ : G ⧸ N} {x : G} :
    x ∈ piece C N i δ ↔ x ∈ C.reps i • (C.parts i : Set G) ∧ (x : G ⧸ N) = δ := by
  classical
  simp [piece]

/-- A point of a piece translates the piece onto `Hᵢ ⊓ N`. -/
lemma mem_piece_iff_of_mem {i : ι} {δ : G ⧸ N} {x₀ x : G}
    (h₀ : x₀ ∈ piece C N i δ) :
    x ∈ piece C N i δ ↔ x₀⁻¹ * x ∈ C.parts i ⊓ N := by
  rw [mem_piece] at h₀ ⊢
  obtain ⟨hc₀, hδ₀⟩ := h₀
  rw [mem_leftCoset_iff] at hc₀
  rw [mem_leftCoset_iff, Subgroup.mem_inf]
  constructor
  · rintro ⟨hc, hδ⟩
    refine ⟨?_, ?_⟩
    · have := (C.parts i).mul_mem ((C.parts i).inv_mem hc₀) hc
      simpa [mul_assoc] using this
    · exact QuotientGroup.eq.mp (hδ₀.trans hδ.symm)
  · rintro ⟨hH, hN⟩
    refine ⟨?_, ?_⟩
    · have := (C.parts i).mul_mem hc₀ hH
      simpa [mul_assoc] using this
    · rw [← hδ₀]
      exact (QuotientGroup.eq.mpr hN).symm

/-- A nonempty piece has exactly `|Hᵢ ⊓ N|` points. -/
lemma card_piece {i : ι} {δ : G ⧸ N} (hne : (piece C N i δ).Nonempty) :
    (piece C N i δ).card = Nat.card (C.parts i ⊓ N : Subgroup G) := by
  classical
  obtain ⟨x₀, h₀⟩ := hne
  have hset : piece C N i δ =
      (univ.filter fun y ↦ y ∈ C.parts i ⊓ N).image (x₀ * ·) := by
    ext x
    rw [mem_piece_iff_of_mem C N h₀, Finset.mem_image]
    constructor
    · intro hx
      exact ⟨x₀⁻¹ * x, by simpa using hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hset, Finset.card_image_of_injective _ (mul_right_injective x₀),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- A piece has `|Hᵢ ⊓ N|` points if nonempty and none otherwise. -/
lemma card_piece_eq_ite (i : ι) (δ : G ⧸ N) [Decidable (piece C N i δ).Nonempty] :
    (piece C N i δ).card =
      if (piece C N i δ).Nonempty then Nat.card (C.parts i ⊓ N : Subgroup G) else 0 := by
  split_ifs with h
  · exact card_piece C N h
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty]

/-- The pieces of a part, over all slices, have total size `|Hᵢ|`. -/
lemma sum_card_piece [Fintype (G ⧸ N)] (i : ι) :
    ∑ δ : G ⧸ N, (piece C N i δ).card = Nat.card (C.parts i) := by
  classical
  let cellF := MassForm.cell C i
  have hfib := Finset.card_eq_sum_card_fiberwise
    (s := cellF) (t := (univ : Finset (G ⧸ N))) (f := fun x : G ↦ (x : G ⧸ N))
    (fun _ _ ↦ Finset.mem_univ _)
  have hcell : cellF.card = Nat.card (C.parts i) := MassForm.card_cell C i
  rw [← hcell, hfib]
  refine Finset.sum_congr rfl fun δ _ ↦ ?_
  congr 1
  ext x
  simp [cellF, piece, MassForm.cell]

/-- `|Hᵢ| = |Hᵢ ⊓ N| · (number of slices met)`. -/
lemma card_eq_mul_ncard_hits (i : ι) :
    Nat.card (C.parts i) =
      Nat.card (C.parts i ⊓ N : Subgroup G) * {δ : G ⧸ N | (piece C N i δ).Nonempty}.ncard := by
  classical
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  rw [← sum_card_piece C N i]
  simp_rw [card_piece_eq_ite C N i]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext δ
  simp

/-- The number of slices met by a part is at most `[G : N]`. -/
lemma ncard_hits_le_index (i : ι) :
    {δ : G ⧸ N | (piece C N i δ).Nonempty}.ncard ≤ N.index := by
  have : Finite (G ⧸ N) := by infer_instance
  calc {δ : G ⧸ N | (piece C N i δ).Nonempty}.ncard ≤ (Set.univ : Set (G ⧸ N)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
    _ = N.index := by rw [Set.ncard_univ]; rfl

end Pieces

end NormaliserSlice

end Erdos274
