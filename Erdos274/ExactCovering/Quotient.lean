/-
Copyright (c) 2026 Erdos 274 Agentic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdos 274 Agentic contributors
-/
import Erdos274.ExactCovering.FiniteIndex
/-!
# Quotients of exact coset coverings

This file develops the descent of an exact coset covering through group homomorphisms and,
in particular, through the quotient by its common normal core.

The key criterion identifies when the images of the selected left cosets remain pairwise
disjoint: the kernel of the homomorphism must lie in every participating subgroup. For a
surjective homomorphism satisfying this condition, the exact covering descends to the target
group.

Applying this construction to the common normal core gives a canonical finite quotient cover.
The quotient construction preserves the subgroup indices exactly.

## Main definitions

* `Group.ExactCovering.map`
* `Group.ExactCovering.finiteQuotientCover`

## Main results

* `Group.ExactCovering.preimage_map_leftCoset`
* `Group.ExactCovering.map_leftCosets_pairwiseDisjoint_iff_ker_le`
* `Group.ExactCovering.map_leftCosets_pairwiseDisjoint_iff_ker_le_commonCore`
* `Group.ExactCovering.quotient_mapped_leftCosets_pairwiseDisjoint_iff_part_le`
* `Group.ExactCovering.quotient_mapped_leftCosets_pairwiseDisjoint_iff_part_eq_commonCore`
* `Group.ExactCovering.finiteQuotientCover_part_index`
* `Group.ExactCovering.exists_equal_index_of_finiteQuotientCover`
-/
universe u v
open scoped Cardinal Pointwise
namespace Erdos274

section ExactCovering

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]

namespace Group.ExactCovering

variable (P : Group.ExactCovering G ι)


/--
The preimage of a mapped left coset is the original coset when the kernel is contained in the
subgroup.  This saturation identity is the key fact used to descend disjointness.
-/
theorem preimage_map_leftCoset {Q : Type*} [Group Q] (f : G →* Q)
    (H : Subgroup G) (hker : f.ker ≤ H) (g : G) :
    f ⁻¹' (f g • (H.map f : Set Q)) = g • (H : Set G) := by
  ext x
  change f x ∈ f g • (H.map f : Set Q) ↔ x ∈ g • (H : Set G)
  rw [mem_leftCoset_iff, mem_leftCoset_iff, ← map_inv, ← map_mul]
  change g⁻¹ * x ∈ (H.map f).comap f ↔ g⁻¹ * x ∈ H
  rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]

variable (P : Group.ExactCovering G ι)

/-- Mapped selected left cosets are pairwise disjoint exactly when the homomorphism kernel lies in
every participating subgroup. Surjectivity is needed for quotient coverage, but not for this
exactness criterion. -/
theorem map_leftCosets_pairwiseDisjoint_iff_ker_le
    {Q : Type*} [Group Q] (f : G →* Q) :
    (Set.univ : Set ι).PairwiseDisjoint (fun j ↦
      f (P.reps j) • ((P.parts j).map f : Set Q)) ↔
      ∀ j, f.ker ≤ P.parts j := by
  constructor
  · intro hpair j n hn
    let x := P.reps j * n
    have hfx : f x = f (P.reps j) := by
      simp [x, MonoidHom.mem_ker.mp hn]
    have hxjQ : f x ∈ f (P.reps j) • ((P.parts j).map f : Set Q) := by
      rw [hfx, mem_leftCoset_iff, inv_mul_cancel]
      exact Subgroup.mem_map.mpr ⟨1, (P.parts j).one_mem, by simp⟩
    have hxcover : x ∈ ⋃ k, P.reps k • (P.parts k : Set G) := by
      rw [P.covers]
      exact Set.mem_univ x
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxcover
    have hxkQ : f x ∈ f (P.reps k) • ((P.parts k).map f : Set Q) := by
      rw [mem_leftCoset_iff]
      apply Subgroup.mem_map.mpr
      refine ⟨(P.reps k)⁻¹ * x,
        (mem_leftCoset_iff (P.reps k)).mp hxk, ?_⟩
      simp
    have hkj : k = j := by
      by_contra hne
      exact (Set.disjoint_left.mp
        (hpair (Set.mem_univ k) (Set.mem_univ j) hne)) hxkQ hxjQ
    subst k
    simpa [x] using (mem_leftCoset_iff (P.reps j)).mp hxk
  · intro hker j _ k _ hjk
    change Disjoint
      (f (P.reps j) • ((P.parts j).map f : Set Q))
      (f (P.reps k) • ((P.parts k).map f : Set Q))
    rw [Set.disjoint_left]
    intro y hyj hyk
    rw [mem_leftCoset_iff] at hyj
    obtain ⟨h, hh, hfh⟩ := Subgroup.mem_map.mp hyj
    let x := P.reps j * h
    have hfx : f x = y := by
      simp [x, hfh]
    have hxj : x ∈ P.reps j • (P.parts j : Set G) := by
      rw [mem_leftCoset_iff]
      simpa [x] using hh
    have hxk : x ∈ P.reps k • (P.parts k : Set G) := by
      have hximage : f x ∈
          f (P.reps k) • ((P.parts k).map f : Set Q) := by
        simpa only [hfx] using hyk
      have hxpre : x ∈ f ⁻¹'
          (f (P.reps k) • ((P.parts k).map f : Set Q)) := hximage
      rwa [preimage_map_leftCoset f (P.parts k) (hker k) (P.reps k)] at hxpre
    exact (Set.disjoint_left.mp
      (P.disjoint (Set.mem_univ j) (Set.mem_univ k) hjk)) hxj hxk

/-- Since a homomorphism kernel is normal, the kernel-containment criterion is equivalently
containment in the cover's common normal core. -/
theorem map_leftCosets_pairwiseDisjoint_iff_ker_le_commonCore
    {Q : Type*} [Group Q] (f : G →* Q) :
    (Set.univ : Set ι).PairwiseDisjoint (fun j ↦
      f (P.reps j) • ((P.parts j).map f : Set Q)) ↔
      f.ker ≤ P.commonCore := by
  rw [P.map_leftCosets_pairwiseDisjoint_iff_ker_le]
  constructor
  · intro hparts
    apply Subgroup.normal_le_normalCore.mpr
    exact le_iInf hparts
  · intro hcore j
    exact hcore.trans (P.commonCore_le_part j)

/-- For a selected normal part, pairwise disjoint quotient images are equivalent to containment of
that part in every participating subgroup. -/
theorem quotient_mapped_leftCosets_pairwiseDisjoint_iff_part_le
    (i : ι) [(P.parts i).Normal] :
    (Set.univ : Set ι).PairwiseDisjoint (fun j ↦
      (QuotientGroup.mk' (P.parts i)) (P.reps j) •
        ((P.parts j).map (QuotientGroup.mk' (P.parts i)) :
          Set (G ⧸ P.parts i))) ↔
      ∀ j, P.parts i ≤ P.parts j := by
  simpa only [QuotientGroup.ker_mk'] using
    P.map_leftCosets_pairwiseDisjoint_iff_ker_le
      (QuotientGroup.mk' (P.parts i))

/-- Equivalently, exactness of the selected-part quotient shadow occurs precisely when the selected
normal part is the cover's common normal core. -/
theorem quotient_mapped_leftCosets_pairwiseDisjoint_iff_part_eq_commonCore
    (i : ι) [(P.parts i).Normal] :
    (Set.univ : Set ι).PairwiseDisjoint (fun j ↦
      (QuotientGroup.mk' (P.parts i)) (P.reps j) •
        ((P.parts j).map (QuotientGroup.mk' (P.parts i)) :
          Set (G ⧸ P.parts i))) ↔
      P.parts i = P.commonCore := by
  rw [P.quotient_mapped_leftCosets_pairwiseDisjoint_iff_part_le i]
  constructor
  · intro hle
    apply le_antisymm
    · apply Subgroup.normal_le_normalCore.mpr
      exact le_iInf hle
    · exact P.commonCore_le_part i
  · intro hi j
    rw [hi]
    exact P.commonCore_le_part j

/--
Push an exact covering through a surjective homomorphism whose kernel lies in every part.

Disjointness is proved by pulling a hypothetical common point back and using
`preimage_map_leftCoset`; it is not inferred from the generally false claim that images preserve
disjointness.
-/
def map {Q : Type*} [Group Q] (f : G →* Q) (hf : Function.Surjective f)
    (hker : ∀ i, f.ker ≤ P.parts i) : Group.ExactCovering Q ι where
  parts i := (P.parts i).map f
  reps i := f (P.reps i)
  nonempty _ := OneMemClass.coe_nonempty _
  disjoint := by
    intro i _ j _ hij
    change Disjoint
      (f (P.reps i) • ((P.parts i).map f : Set Q))
      (f (P.reps j) • ((P.parts j).map f : Set Q))
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨y, rfl⟩ := hf x
    have hyi : y ∈ P.reps i • (P.parts i : Set G) := by
      have : y ∈ f ⁻¹' (f (P.reps i) • ((P.parts i).map f : Set Q)) := hxi
      rwa [preimage_map_leftCoset f (P.parts i) (hker i) (P.reps i)] at this
    have hyj : y ∈ P.reps j • (P.parts j : Set G) := by
      have : y ∈ f ⁻¹' (f (P.reps j) • ((P.parts j).map f : Set Q)) := hxj
      rwa [preimage_map_leftCoset f (P.parts j) (hker j) (P.reps j)] at this
    exact (Set.disjoint_left.mp
      (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hyi hyj
  covers := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    obtain ⟨y, rfl⟩ := hf x
    have hy : y ∈ ⋃ i, P.reps i • (P.parts i : Set G) := by
      rw [P.covers]
      exact Set.mem_univ y
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have : y ∈ f ⁻¹' (f (P.reps i) • ((P.parts i).map f : Set Q)) := by
      rwa [preimage_map_leftCoset f (P.parts i) (hker i) (P.reps i)]
    exact this

/-- The exact covering descended to the finite quotient by the common normal core. -/
def finiteQuotientCover : Group.ExactCovering (G ⧸ P.commonCore) ι :=
  P.map (QuotientGroup.mk' P.commonCore)
    (QuotientGroup.mk'_surjective P.commonCore) fun i ↦ by
      simpa using P.commonCore_le_part i

/-- Descent to the common-core quotient preserves every subgroup index exactly. -/
theorem finiteQuotientCover_part_index (i : ι) :
    (P.finiteQuotientCover.parts i).index = (P.parts i).index := by
  apply Subgroup.index_map_eq
  · exact QuotientGroup.mk'_surjective P.commonCore
  · simpa using P.commonCore_le_part i

/-- If the canonical finite quotient cover has repeated indices, so does the original cover. -/
theorem exists_equal_index_of_finiteQuotientCover
    (h : ∃ i j, i ≠ j ∧ (P.finiteQuotientCover.parts i).index =
      (P.finiteQuotientCover.parts j).index) :
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  obtain ⟨i, j, hij, hind⟩ := h
  exact ⟨i, j, hij, by
    rwa [P.finiteQuotientCover_part_index i, P.finiteQuotientCover_part_index j] at hind⟩

end Group.ExactCovering

end ExactCovering

end Erdos274
