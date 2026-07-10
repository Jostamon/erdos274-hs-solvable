/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

-- Definitions adapted from `FormalConjectures/ErdosProblems/274.lean` in
-- google-deepmind/formal-conjectures (Apache 2.0).

/-!
# Exact coverings of a group by cosets

The basic definition underlying Erdős problem 274 (the Herzog–Schönheim
conjecture): a partition of a group into finitely many left cosets.  The
conjecture itself is stated in `Erdos274`, and its known special
cases are proved in the sibling modules.

## Main definitions

* `Erdos274.Group.ExactCovering`: a partition of `G` into left cosets.

## References

* [erdosproblems.com/274](https://www.erdosproblems.com/274)
* [Wikipedia](https://en.wikipedia.org/wiki/Herzog%E2%80%93Sch%C3%B6nheim_conjecture)
-/

open scoped Pointwise

namespace Erdos274

/-- An exact covering of a group `G` is a finite collection of subgroups
`H i` with representatives `g i` such that the cosets `g i • H i` are pairwise
disjoint and cover `G`. -/
structure Group.ExactCovering (G : Type*) [Group G] (ι : Type*) [Fintype ι] where
  /-- The subgroups whose cosets form the partition. -/
  parts : ι → Subgroup G
  /-- A representative for each coset. -/
  reps : ι → G
  disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun i ↦ reps i • (parts i : Set G)
  covers : ⋃ i, reps i • (parts i : Set G) = Set.univ

namespace Group.ExactCovering

variable {G ι : Type*} [Group G] [Fintype ι] (P : Group.ExactCovering G ι)

/-- Every element of `G` lies in one of the cosets of an exact covering. -/
lemma exists_mem (x : G) : ∃ i, x ∈ P.reps i • (P.parts i : Set G) := by
  simpa [← Set.mem_iUnion] using P.covers ▸ Set.mem_univ x

section Quotient

variable {G ι : Type*} [Group G] [Fintype ι] (P : Group.ExactCovering G ι)

omit [Fintype ι] in
/-- Cosets absorb right multiplication by subgroup elements. -/
private lemma mul_mem_smul_coset {g y h : G} {H : Subgroup G}
    (hy : y ∈ g • (H : Set G)) (hh : h ∈ H) : y * h ∈ g • (H : Set G) := by
  rw [mem_leftCoset_iff] at hy ⊢
  simpa [mul_assoc] using H.mul_mem hy hh

section
variable {G' : Type*} [Group G']

omit [Fintype ι] in
/-- A monoid hom maps a coset onto a coset of the image subgroup. -/
private lemma image_smul_coset (f : G →* G') (x : G) (L : Subgroup G) :
    f '' (x • (L : Set G)) = f x • ((L.map f : Subgroup G') : Set G') := by
  rw [Set.image_smul_distrib, Subgroup.coe_map]

end

/-- Descend an exact covering to a quotient by a normal subgroup contained in
every part. -/
def quotient (N : Subgroup G) [N.Normal] (hfull : ∀ j, N ≤ P.parts j) :
    Group.ExactCovering (G ⧸ N) ι where
  parts j := (P.parts j).map (QuotientGroup.mk' N)
  reps j := QuotientGroup.mk (P.reps j)
  disjoint := by
    have habs : ∀ (j : ι) (y x : G),
        y ∈ P.reps j • ((P.parts j : Subgroup G) : Set G) →
        (QuotientGroup.mk x : G ⧸ N) = QuotientGroup.mk y →
        x ∈ P.reps j • ((P.parts j : Subgroup G) : Set G) := by
      intro j y x hy hxy
      have h1 : y⁻¹ * x ∈ N := (QuotientGroup.eq).mp hxy.symm
      have := mul_mem_smul_coset hy (hfull j h1)
      simpa using this
    rintro i - j - hij
    refine Set.disjoint_left.mpr fun {c} hci hcj ↦ ?_
    have hci' : c ∈ (QuotientGroup.mk' N) '' (P.reps i •
        ((P.parts i : Subgroup G) : Set G)) := by
      rw [image_smul_coset]
      exact hci
    have hcj' : c ∈ (QuotientGroup.mk' N) '' (P.reps j •
        ((P.parts j : Subgroup G) : Set G)) := by
      rw [image_smul_coset]
      exact hcj
    obtain ⟨x, hx, hcx⟩ := hci'
    obtain ⟨y, hy, hcy⟩ := hcj'
    have hx' : x ∈ P.reps j • ((P.parts j : Subgroup G) : Set G) :=
      habs j y x hy (by rw [show (QuotientGroup.mk x : G ⧸ N) =
        (QuotientGroup.mk' N) x from rfl, hcx, ← hcy]; rfl)
    exact Set.disjoint_left.mp
      (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hij) hx hx'
  covers := by
    rw [Set.eq_univ_iff_forall]
    intro c
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hx : x ∈ ⋃ j, P.reps j • ((P.parts j : Subgroup G) : Set G) :=
      P.covers ▸ Set.mem_univ x
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    show QuotientGroup.mk x ∈ (QuotientGroup.mk (P.reps j) : G ⧸ N) •
      (((P.parts j).map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) :
        Set (G ⧸ N))
    rw [show (QuotientGroup.mk (P.reps j) : G ⧸ N) =
        (QuotientGroup.mk' N) (P.reps j) from rfl, ← image_smul_coset]
    exact ⟨x, hj, rfl⟩

end Quotient

end Group.ExactCovering

end Erdos274
