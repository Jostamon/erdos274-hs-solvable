/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Card


/-!
# Finite cells of an exact covering

This module collects small cell and point-union APIs.  Their historical
namespaces (`NormaliserSlice`, `MassForm`, and `QuotientShadow`) are retained
so downstream proofs keep their existing interfaces.
-/

@[expose] public section

namespace Erdos274

open Finset
open scoped Pointwise

universe u v

namespace NormaliserSlice

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]
variable (C : Group.ExactCovering G ι)

/-- Two cells sharing a point are the same cell. -/
lemma eq_of_mem_cell {i j : ι} {x : G} (hi : x ∈ C.reps i • (C.parts i : Set G))
    (hj : x ∈ C.reps j • (C.parts j : Set G)) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (C.disjoint (Set.mem_univ i) (Set.mem_univ j) hij) hi hj

/-- A cell is closed under right multiplication by its subgroup. -/
lemma mul_mem_cell {i : ι} {x h : G} (hx : x ∈ C.reps i • (C.parts i : Set G))
    (hh : h ∈ C.parts i) : x * h ∈ C.reps i • (C.parts i : Set G) := by
  rw [mem_leftCoset_iff] at hx ⊢
  simpa [mul_assoc] using (C.parts i).mul_mem hx hh

end NormaliserSlice

namespace MassForm

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]
variable [Fintype G] (C : Group.ExactCovering G ι)

open Classical in
/-- The cell `gᵢ Hᵢ` as a finset. -/
noncomputable def cell (i : ι) : Finset G :=
  univ.filter fun x ↦ x ∈ C.reps i • (C.parts i : Set G)

lemma mem_cell {i : ι} {x : G} : x ∈ cell C i ↔ x ∈ C.reps i • (C.parts i : Set G) := by
  classical
  simp [cell]

lemma card_cell (i : ι) : (cell C i).card = Nat.card (C.parts i) := by
  classical
  unfold cell
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  change Nat.card ↑(C.reps i • (C.parts i : Set G)) = _
  rw [Set.natCard_smul_set]
  rfl

end MassForm

namespace QuotientShadow

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]
variable [Fintype G] (C : Group.ExactCovering G ι)

open Classical in
/-- The points of the cells of the parts in `T`. -/
noncomputable def ptsOf (T : Finset ι) : Finset G := T.biUnion (MassForm.cell C)

lemma card_ptsOf (T : Finset ι) : (ptsOf C T).card = ∑ i ∈ T, Nat.card (C.parts i) := by
  classical
  unfold ptsOf
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ ↦ MassForm.card_cell C i
  intro i _ j _ hij
  change Disjoint (MassForm.cell C i) (MassForm.cell C j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  exact hij (NormaliserSlice.eq_of_mem_cell C
    ((MassForm.mem_cell C).mp hxi) ((MassForm.mem_cell C).mp hxj))

end QuotientShadow

end Erdos274
