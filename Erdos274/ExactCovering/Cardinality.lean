/-
Copyright (c) 2026 Erdos 274 Agentic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdos 274 Agentic contributors
-/
import Erdos274.ExactCovering.Quotient

universe u v
open scoped BigOperators Cardinal Pointwise
namespace Erdos274

section CardinalSemantics

variable {α β : Type u}

/-- `#α` is genuine cardinality: equality means the types are equivalent. -/
theorem cardinalMk_eq_iff_equiv : #α = #β ↔ Nonempty (α ≃ β) :=
  Cardinal.eq

/-- On finite types, `Cardinal.mk` is the natural cardinal embedded in `Cardinal`. -/
theorem cardinalMk_eq_natCard_of_finite [Finite α] :
    #α = (Nat.card α : Cardinal) :=
  Nat.cast_card.symm

/-- On infinite types, `Nat.card` has its documented junk value `0`. -/
theorem natCard_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 :=
  Nat.card_eq_zero_of_infinite

/-- On infinite types, `ENat.card` records infinity as `⊤`. -/
theorem enatCard_eq_top_of_infinite [Infinite α] : ENat.card α = ⊤ :=
  ENat.card_eq_top_of_infinite

/-- On finite types, `ENat.card` is the natural cardinal embedded in `ENat`. -/
theorem enatCard_eq_natCard_of_finite [Finite α] : ENat.card α = Nat.card α :=
  ENat.card_eq_coe_natCard α

/-- The ambient hypothesis `1 < ENat.card α` says exactly that `α` is nontrivial. -/
theorem one_lt_enatCard_iff_nontrivial : 1 < ENat.card α ↔ Nontrivial α :=
  ENat.one_lt_card_iff_nontrivial α

/-- An infinite type has cardinal at least `ℵ₀`; unlike `Nat.card`, `#` does not collapse it. -/
theorem infinite_iff_aleph0_le_cardinalMk : Infinite α ↔ ℵ₀ ≤ #α :=
  Cardinal.infinite_iff

/-- For finite types, equality of natural cardinals and equality of true cardinals agree. -/
theorem natCard_eq_iff_cardinalMk_eq [Finite α] [Finite β] :
    Nat.card α = Nat.card β ↔ #α = #β := by
  constructor
  · intro h
    calc
      #α = (Nat.card α : Cardinal) := Nat.cast_card.symm
      _ = (Nat.card β : Cardinal) := congrArg (fun n : ℕ ↦ (n : Cardinal)) h
      _ = #β := Nat.cast_card
  · intro h
    simpa only [Nat.card] using congrArg Cardinal.toNat h

/-- For finite types, equality of extended-natural cardinals and natural cardinals agree. -/
theorem enatCard_eq_iff_natCard_eq [Finite α] [Finite β] :
    ENat.card α = ENat.card β ↔ Nat.card α = Nat.card β := by
  rw [ENat.card_eq_coe_natCard, ENat.card_eq_coe_natCard, ENat.coe_inj]

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
  letI : Subsingleton G := hsub
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hι
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
  letI : H.FiniteIndex := hH
  have hH_not_finite : ¬Finite H := by
    intro hfinite
    letI : Finite H := hfinite
    haveI : Finite G :=
      (H.finite_iff_finite_and_finiteIndex).mpr ⟨inferInstance, inferInstance⟩
    exact not_finite_iff_infinite.mpr (inferInstance : Infinite G) inferInstance
  letI : Infinite H := not_finite_iff_infinite.mp hH_not_finite
  letI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
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
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hι
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  exact ⟨i, j, hij,
    (cardinalMk_subgroup_eq_of_finiteIndex (P.parts i) (P.part_finiteIndex i)).trans
      (cardinalMk_subgroup_eq_of_finiteIndex (P.parts j) (P.part_finiteIndex j)).symm⟩

end InfiniteGroups


end Erdos274
