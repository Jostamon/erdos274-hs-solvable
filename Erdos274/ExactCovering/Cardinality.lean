/-
Copyright (c) 2026 Erdos 274 Agentic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdos 274 Agentic contributors
-/
module

public import Erdos274.ExactCovering.Quotient

/-!
# Cardinality properties of exact coset coverings

This file relates the different cardinality notions used for subgroup parts of an exact coset
covering and studies their behaviour under passage to the common-core quotient.

It relates genuine cardinality `Cardinal.mk`, finite cardinality `Nat.card`, and
extended-natural cardinality `ENat.card` (Mathlib's `Nat.cast_card`,
`ENat.card_eq_coe_natCard`, `ENat.one_lt_card_iff_nontrivial`). It proves a cardinal factorization
formula for subgroups containing the kernel of a homomorphism and applies it to the canonical
common-core quotient cover.

The file also separates the finite and infinite ambient-group cases. In an infinite group,
every finite-index subgroup has the same genuine cardinality as the ambient group, so repeated
part cardinality is automatic for every nontrivial finite exact covering.

## Main results

* `natCard_eq_iff_cardinalMk_eq`
* `cardinalMk_eq_map_mul_kernel`
* `cardinalMk_eq_of_map_cardinalMk_eq`
* `finiteQuotientCover_part_cardinalMk`
* `finiteQuotientCover_cardinalMk_eq_imp`
* `exactCovering_nontrivial_of_one_lt_card`
* `cardinalMk_subgroup_eq_of_finiteIndex`
* `exactCovering_exists_equal_cardinalMk_of_infinite`
-/

@[expose] public section
universe u v
open scoped BigOperators Cardinal Pointwise
namespace Erdos274

section CardinalSemantics

variable {α β : Type u}

/-- For finite types, equality of natural cardinals and equality of true cardinals agree. -/
theorem natCard_eq_iff_cardinalMk_eq [Finite α] [Finite β] :
    Nat.card α = Nat.card β ↔ #α = #β := by
  rw [← Nat.cast_card, ← Nat.cast_card, Nat.cast_inj]

/-- For finite types, equality of extended-natural cardinals and natural cardinals agree. -/
theorem enatCard_eq_iff_natCard_eq [Finite α] [Finite β] :
    ENat.card α = ENat.card β ↔ Nat.card α = Nat.card β := by
  rw [ENat.card_eq_coe_natCard, ENat.card_eq_coe_natCard, ENat.natCast_inj]

end CardinalSemantics

section QuotientCardinality

variable {G Q : Type u} [Group G] [Group Q]

/--
For a homomorphism whose kernel lies in `H`, the true cardinal of `H` is the cardinal of its image
times the cardinal of the kernel.  No finiteness or cardinal cancellation is used here.
-/
theorem cardinalMk_eq_map_mul_kernel (f : G →* Q) (H : Subgroup G)
    (hker : f.ker ≤ H) :
    #H = #(H.map f) * #f.ker := by
  let φ : H →* H.map f := f.subgroupMap H
  calc
    #H = #((H ⧸ φ.ker) × φ.ker) :=
      Subgroup.groupEquivQuotientProdSubgroup.cardinal_eq
    _ = #(H ⧸ φ.ker) * #φ.ker := by simp
    _ = #(H.map f) * #φ.ker := by
      rw [(QuotientGroup.quotientKerEquivOfSurjective φ
        (f.subgroupMap_surjective H)).cardinal_eq]
    _ = #(H.map f) * #(f.ker.subgroupOf H) := by
      rw [Subgroup.ker_subgroupMap]
    _ = #(H.map f) * #f.ker := by
      rw [(Subgroup.subgroupOfEquivOfLe hker).cardinal_eq]

/-- Equality of mapped subgroup cardinals always lifts when both subgroups contain the kernel. -/
theorem cardinalMk_eq_of_map_cardinalMk_eq (f : G →* Q) (H K : Subgroup G)
    (hH : f.ker ≤ H) (hK : f.ker ≤ K)
    (hmap : #(H.map f) = #(K.map f)) : #H = #K := by
  calc
    #H = #(H.map f) * #f.ker := cardinalMk_eq_map_mul_kernel f H hH
    _ = #(K.map f) * #f.ker := congrArg (fun c ↦ c * #f.ker) hmap
    _ = #K := (cardinalMk_eq_map_mul_kernel f K hK).symm

variable {ι : Type v} [Fintype ι]

/-- Exact cardinal formula for every part after descent to the common-core quotient. -/
theorem finiteQuotientCover_part_cardinalMk
    (P : Group.ExactCovering G ι) (i : ι) :
    #(P.parts i) = #(P.finiteQuotientCover.parts i) * #P.commonCore := by
  change #(P.parts i) =
    #((P.parts i).map (QuotientGroup.mk' P.commonCore)) * #P.commonCore
  simpa only [QuotientGroup.ker_mk'] using
    cardinalMk_eq_map_mul_kernel (QuotientGroup.mk' P.commonCore) (P.parts i)
      (by simpa using P.commonCore_le_part i)

/-- Repeated quotient-part cardinality implies repeated original-part cardinality in all groups. -/
theorem finiteQuotientCover_cardinalMk_eq_imp
    (P : Group.ExactCovering G ι) (i j : ι)
    (h : #(P.finiteQuotientCover.parts i) = #(P.finiteQuotientCover.parts j)) :
    #(P.parts i) = #(P.parts j) := by
  calc
    #(P.parts i) = #(P.finiteQuotientCover.parts i) * #P.commonCore :=
      finiteQuotientCover_part_cardinalMk P i
    _ = #(P.finiteQuotientCover.parts j) * #P.commonCore :=
      congrArg (fun c ↦ c * #P.commonCore) h
    _ = #(P.parts j) := (finiteQuotientCover_part_cardinalMk P j).symm

end QuotientCardinality

section CoverNontrivial

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]

/-- More than one nonempty, pairwise-disjoint cell forces the ambient group to be nontrivial. -/
theorem exactCovering_nontrivial_of_one_lt_card
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) : Nontrivial G := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  let : Subsingleton G := hsub
  let : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hι
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  obtain ⟨x, hxi⟩ := P.coset_nonempty i
  obtain ⟨y, hyj⟩ := P.coset_nonempty j
  have hxj : x ∈ P.reps j • (P.parts j : Set G) := by
    simpa only [Subsingleton.elim x y] using hyj
  exact (Set.disjoint_left.mp
    (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hxi hxj

end CoverNontrivial

section InfiniteGroups

variable {G : Type u} [Group G]

/-- A finite-index subgroup of an infinite group has the same true cardinality as the group. -/
theorem cardinalMk_subgroup_eq_of_finiteIndex [Infinite G] (H : Subgroup G)
    (hH : H.FiniteIndex) : #H = #G := by
  let : H.FiniteIndex := hH
  have hH_not_finite : ¬Finite H := by
    intro hfinite
    let : Finite H := hfinite
    have : Finite G :=
      (H.finite_iff_finite_and_finiteIndex).mpr ⟨inferInstance, inferInstance⟩
    exact not_finite_iff_infinite.mpr (inferInstance : Infinite G) inferInstance
  let : Infinite H := not_finite_iff_infinite.mp hH_not_finite
  let : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have hquot_le : #(G ⧸ H) ≤ #H :=
    (Cardinal.lt_aleph0_of_finite (G ⧸ H)).le.trans (Cardinal.aleph0_le_mk H)
  have hmul : #(G ⧸ H) * #H = #H :=
    Cardinal.mul_eq_right (Cardinal.aleph0_le_mk H) hquot_le
      (Cardinal.mk_ne_zero (G ⧸ H))
  calc
    #H = #(G ⧸ H) * #H := hmul.symm
    _ = #((G ⧸ H) × H) := by simp
    _ = #G := Subgroup.groupEquivQuotientProdSubgroup.cardinal_eq.symm

variable {ι : Type v} [Fintype ι]

/-- The desired repeated-cardinality conclusion is automatic for infinite ambient groups. -/
theorem exactCovering_exists_equal_cardinalMk_of_infinite [Infinite G]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) := by
  let : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hι
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  exact ⟨i, j, hij,
    (cardinalMk_subgroup_eq_of_finiteIndex (P.parts i) (P.part_finiteIndex i)).trans
      (cardinalMk_subgroup_eq_of_finiteIndex (P.parts j) (P.part_finiteIndex j)).symm⟩

end InfiniteGroups


end Erdos274
