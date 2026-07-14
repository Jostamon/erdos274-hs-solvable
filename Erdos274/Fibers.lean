/-
Copyright (c) 2026 Erdos 274 Agentic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdos 274 Agentic contributors
-/
import Erdos274.Placement.Saturation

universe u v
open scoped Cardinal Pointwise
namespace Erdos274

section ExactCovering

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]

namespace Group.ExactCovering

variable (P : Group.ExactCovering G ι)

/-- The cells meeting the left `N`-coset through `x`. -/
def FiberIndex (N : Subgroup G) (x : G) :=
  {i : ι //
    ((P.reps i • (P.parts i : Set G)) ∩ (x • (N : Set G))).Nonempty}

/-- A cell meets the `N`-fiber through `x` exactly when its image shadow contains the image of
`x`. Normality is used only to form the quotient group. -/
theorem fiber_nonempty_iff_mem_quotientShadow
    (N : Subgroup G) [N.Normal] (x : G) (i : ι) :
    ((P.reps i • (P.parts i : Set G)) ∩ (x • (N : Set G))).Nonempty ↔
      QuotientGroup.mk' N x ∈
        QuotientGroup.mk' N (P.reps i) •
          ((P.parts i).map (QuotientGroup.mk' N) : Set (G ⧸ N)) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  constructor
  · rintro ⟨y, hycell, hyfiber⟩
    have hqxy : q x = q y :=
      QuotientGroup.eq.mpr ((mem_leftCoset_iff x).mp hyfiber)
    rw [hqxy, mem_leftCoset_iff]
    apply Subgroup.mem_map.mpr
    refine ⟨(P.reps i)⁻¹ * y,
      (mem_leftCoset_iff (P.reps i)).mp hycell, ?_⟩
    simp [q]
  · intro hshadow
    rw [mem_leftCoset_iff] at hshadow
    obtain ⟨h, hh, hqh⟩ := Subgroup.mem_map.mp hshadow
    refine ⟨P.reps i * h, ?_, ?_⟩
    · rw [mem_leftCoset_iff]
      simpa using hh
    · rw [mem_leftCoset_iff]
      apply QuotientGroup.eq.mp
      change q x = q (P.reps i * h)
      rw [map_mul, hqh]
      exact (mul_inv_cancel_left (q (P.reps i)) (q x)).symm

/-- The indices whose cells have image shadows containing the selected quotient point. -/
def QuotientShadowIndex (N : Subgroup G) [N.Normal] (x : G) :=
  {i : ι //
    QuotientGroup.mk' N x ∈
      QuotientGroup.mk' N (P.reps i) •
        ((P.parts i).map (QuotientGroup.mk' N) : Set (G ⧸ N))}

noncomputable instance quotientShadowIndexFintype
    (N : Subgroup G) [N.Normal] (x : G) :
    Fintype (P.QuotientShadowIndex N x) := by
  letI : Finite (P.QuotientShadowIndex N x) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite (P.QuotientShadowIndex N x)

/-- The fiber-active indices and quotient-shadow-active indices are canonically equivalent. -/
def fiberIndexEquivQuotientShadowIndex
    (N : Subgroup G) [N.Normal] (x : G) :
    P.FiberIndex N x ≃ P.QuotientShadowIndex N x where
  toFun i := ⟨i.1,
    (P.fiber_nonempty_iff_mem_quotientShadow N x i.1).mp i.2⟩
  invFun i := ⟨i.1,
    (P.fiber_nonempty_iff_mem_quotientShadow N x i.1).mpr i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fiberIndex_nonempty (N : Subgroup G) (x : G) :
    Nonempty (P.FiberIndex N x) := by
  have hx : x ∈ ⋃ i, P.reps i • (P.parts i : Set G) := by
    rw [P.covers]
    exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  refine ⟨⟨i, ⟨x, hi, ?_⟩⟩⟩
  apply (mem_leftCoset_iff x).mpr
  simp

noncomputable instance fiberIndexFintype (N : Subgroup G) (x : G) :
    Fintype (P.FiberIndex N x) := by
  letI : Finite (P.FiberIndex N x) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite (P.FiberIndex N x)

/-- A chosen point where an active cell meets the selected subgroup coset. -/
noncomputable def fiberPoint (N : Subgroup G) (x : G) (i : P.FiberIndex N x) : G :=
  i.property.choose

theorem fiberPoint_mem_cell (N : Subgroup G) (x : G) (i : P.FiberIndex N x) :
    P.fiberPoint N x i ∈ P.reps i.1 • (P.parts i.1 : Set G) :=
  i.property.choose_spec.1

theorem fiberPoint_mem_fiber (N : Subgroup G) (x : G) (i : P.FiberIndex N x) :
    P.fiberPoint N x i ∈ x • (N : Set G) :=
  i.property.choose_spec.2

/-- The representative in `N` obtained after translating a chosen fiber intersection by `x⁻¹`. -/
noncomputable def fiberRep (N : Subgroup G) (x : G) (i : P.FiberIndex N x) : N :=
  ⟨x⁻¹ * P.fiberPoint N x i,
    (mem_leftCoset_iff x).mp (P.fiberPoint_mem_fiber N x i)⟩

/-- The subgroup `Hᵢ ∩ N`, represented as a subgroup of `N`. -/
def fiberPart (N : Subgroup G) (i : P.FiberIndex N x) : Subgroup N :=
  (P.parts i.1).comap N.subtype

theorem mem_fiberRep_smul_fiberPart_iff (N : Subgroup G) (x : G)
    (i : P.FiberIndex N x) (n : N) :
    n ∈ P.fiberRep N x i • (P.fiberPart N i : Set N) ↔
      x * (n : G) ∈ P.reps i.1 • (P.parts i.1 : Set G) := by
  rw [mem_leftCoset_iff, mem_leftCoset_iff]
  change ((P.fiberRep N x i)⁻¹ * n : N) ∈
      (P.parts i.1).comap N.subtype ↔
        (P.reps i.1)⁻¹ * (x * (n : G)) ∈ P.parts i.1
  change N.subtype ((P.fiberRep N x i)⁻¹ * n) ∈ P.parts i.1 ↔ _
  rw [map_mul, map_inv]
  change (x⁻¹ * P.fiberPoint N x i)⁻¹ * (n : G) ∈ P.parts i.1 ↔ _
  simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hw : (P.reps i.1)⁻¹ * P.fiberPoint N x i ∈ P.parts i.1 :=
    (mem_leftCoset_iff (P.reps i.1)).mp (P.fiberPoint_mem_cell N x i)
  constructor
  · intro hn
    simpa [mul_assoc] using (P.parts i.1).mul_mem hw hn
  · intro hn
    simpa [mul_assoc] using (P.parts i.1).mul_mem ((P.parts i.1).inv_mem hw) hn

/-- Intersecting an exact cover with a left coset of `N` gives an exact cover of `N`. -/
noncomputable def fiberCover (N : Subgroup G) (x : G) :
    Group.ExactCovering N (P.FiberIndex N x) where
  parts i := P.fiberPart N i
  reps i := P.fiberRep N x i
  disjoint := by
    intro i _ j _ hij
    change Disjoint
      (P.fiberRep N x i • (P.fiberPart N i : Set N))
      (P.fiberRep N x j • (P.fiberPart N j : Set N))
    rw [Set.disjoint_left]
    intro n hni hnj
    have hijval : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
    exact (Set.disjoint_left.mp
      (P.disjoint (Set.mem_univ i.1) (Set.mem_univ j.1) hijval))
        ((P.mem_fiberRep_smul_fiberPart_iff N x i n).mp hni)
        ((P.mem_fiberRep_smul_fiberPart_iff N x j n).mp hnj)
  covers := by
    apply Set.eq_univ_iff_forall.mpr
    intro n
    have hxn : x * (n : G) ∈ ⋃ i, P.reps i • (P.parts i : Set G) := by
      rw [P.covers]
      exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxn
    have hxfiber : x * (n : G) ∈ x • (N : Set G) := by
      rw [mem_leftCoset_iff]
      change x⁻¹ * (x * (n : G)) ∈ N
      simpa only [inv_mul_cancel_left] using n.property
    let k : P.FiberIndex N x := ⟨i, ⟨x * (n : G), hi, hxfiber⟩⟩
    apply Set.mem_iUnion.mpr
    exact ⟨k, (P.mem_fiberRep_smul_fiberPart_iff N x k n).mpr hi⟩

end Group.ExactCovering

end ExactCovering

end Erdos274
