/-
Copyright (c) 2026 Erdos 274 Agentic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdos 274 Agentic contributors
-/
import Erdos274.ExactCovering.Cardinality
import Erdos274.ExactCovering.Fibers
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum

universe u v
open scoped BigOperators Cardinal Pointwise
namespace Erdos274

section FiniteGroups

variable {G : Type u} [Group G] [Finite G] {ι : Type v} [Fintype ι]

/-- In a finite group, equality of subgroup orders is equivalent to equality of indices. -/
theorem subgroup_natCard_eq_iff_index_eq (H K : Subgroup G) :
    Nat.card H = Nat.card K ↔ H.index = K.index := by
  constructor
  · intro hcard
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H))
    calc
      Nat.card H * H.index = Nat.card G := H.card_mul_index
      _ = Nat.card K * K.index := K.card_mul_index.symm
      _ = Nat.card H * K.index := by rw [hcard]
  · intro hindex
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero H.index_ne_zero_of_finite)
    calc
      H.index * Nat.card H = Nat.card G := H.index_mul_card
      _ = K.index * Nat.card K := K.index_mul_card.symm
      _ = H.index * Nat.card K := by rw [hindex]

/--
In a finite group, equality of genuine subgroup cardinals is equivalent to equality of indices.
-/
theorem subgroup_cardinalMk_eq_iff_index_eq (H K : Subgroup G) :
    #H = #K ↔ H.index = K.index :=
  (natCard_eq_iff_cardinalMk_eq (α := H) (β := K)).symm.trans
    (subgroup_natCard_eq_iff_index_eq H K)

theorem subgroup_enatCard_eq_iff_index_eq (H K : Subgroup G) :
    ENat.card H = ENat.card K ↔ H.index = K.index :=
  (enatCard_eq_iff_natCard_eq (α := H) (β := K)).trans
    (subgroup_natCard_eq_iff_index_eq H K)

variable {ι : Type v} [Fintype ι]


/-- In a finite exact cover, the subgroup orders add up to the order of the ambient group. -/
theorem exactCovering_sum_natCard_parts (P : Group.ExactCovering G ι) :
    ∑ i, Nat.card (P.parts i) = Nat.card G := by
  classical
  have hpairwise : Pairwise (fun i j ↦
      Disjoint (P.reps i • (P.parts i : Set G))
        (P.reps j • (P.parts j : Set G))) :=
    fun i j hij ↦ P.disjoint (Set.mem_univ i) (Set.mem_univ j) hij
  have hcount := Set.ncard_iUnion_of_finite
    (fun _ ↦ Set.finite_univ.subset (Set.subset_univ _)) hpairwise
  rw [P.covers, Set.ncard_univ, finsum_eq_sum_of_fintype] at hcount
  simpa only [← Nat.card_coe_set_eq, Set.natCard_smul_set, SetLike.coe_sort_coe]
    using hcount.symm


/-- In a finite exact cover, the reciprocals of the subgroup indices sum to one. -/
theorem exactCovering_sum_inv_index_of_finite (P : Group.ExactCovering G ι) :
    ∑ i, ((P.parts i).index : ℚ)⁻¹ = 1 := by
  classical
  have hG0 : (Nat.card G : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hsumQ :
      ∑ i, (Nat.card (P.parts i) : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast exactCovering_sum_natCard_parts P
  calc
    ∑ i, ((P.parts i).index : ℚ)⁻¹ =
        ∑ i, (Nat.card (P.parts i) : ℚ) / (Nat.card G : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [inv_eq_one_div]
      apply (div_eq_div_iff
        (Nat.cast_ne_zero.mpr (P.parts i).index_ne_zero_of_finite) hG0).2
      norm_num
      exact_mod_cast (P.parts i).card_mul_index.symm
    _ = (∑ i, (Nat.card (P.parts i) : ℚ)) / (Nat.card G : ℚ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := by rw [hsumQ, div_self hG0]


/-- In the finite case, common-core quotienting preserves equality of part cardinals both ways. -/
theorem finiteQuotientCover_cardinalMk_eq_iff
    (P : Group.ExactCovering G ι) (i j : ι) :
    #(P.finiteQuotientCover.parts i) = #(P.finiteQuotientCover.parts j) ↔
      #(P.parts i) = #(P.parts j) := by
  rw [subgroup_cardinalMk_eq_iff_index_eq,
    P.finiteQuotientCover_part_index i, P.finiteQuotientCover_part_index j,
    subgroup_cardinalMk_eq_iff_index_eq]


end FiniteGroups

/-- Every exact finite coset cover has reciprocal index sum one, even in an infinite group. -/
theorem exactCovering_sum_inv_index {G : Type u} [Group G]
    {i : Type v} [Fintype i] (P : Group.ExactCovering G i) :
    ∑ j, ((P.parts j).index : ℚ)⁻¹ = 1 := by
  letI : Finite (G ⧸ P.commonCore) := P.finite_commonCore_quotient
  simpa only [P.finiteQuotientCover_part_index] using
    exactCovering_sum_inv_index_of_finite P.finiteQuotientCover

/-- The subgroup-intersection indices in every subgroup-coset fiber have reciprocal sum one. -/
theorem fiberCover_sum_inv_index {G : Type u} [Group G]
    {ι : Type v} [Fintype ι] (P : Group.ExactCovering G ι)
    (N : Subgroup G) (x : G) :
    ∑ i : P.FiberIndex N x, ((P.fiberPart (x := x) N i).index : ℚ)⁻¹ = 1 :=
  exactCovering_sum_inv_index (P.fiberCover N x)

namespace Group.ExactCovering

variable {G : Type u} [Group G] {ι : Type v} [Fintype ι]

/-- An exact covering parametrizes the group by the sigma type of its subgroup parts. -/
noncomputable def cellEquiv (P : Group.ExactCovering G ι) : (Σ i, P.parts i) ≃ G :=
  Equiv.ofBijective
    (fun x ↦ P.reps x.1 * (x.2 : G))
    (by
      constructor
      · rintro ⟨i, h⟩ ⟨j, k⟩ heq
        change P.reps i * (h : G) = P.reps j * (k : G) at heq
        have hhi : P.reps i * (h : G) ∈ P.reps i • (P.parts i : Set G) := by
          rw [mem_leftCoset_iff]
          change (P.reps i)⁻¹ * (P.reps i * (h : G)) ∈ P.parts i
          simpa only [inv_mul_cancel_left] using h.property
        have hkj : P.reps j * (k : G) ∈ P.reps j • (P.parts j : Set G) := by
          rw [mem_leftCoset_iff]
          change (P.reps j)⁻¹ * (P.reps j * (k : G)) ∈ P.parts j
          simpa only [inv_mul_cancel_left] using k.property
        have hij : i = j := by
          by_contra hij
          exact (Set.disjoint_left.mp
            (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hij))
              hhi (by rw [heq]; exact hkj)
        subst j
        have hk : h = k := by
          apply Subtype.ext
          exact mul_left_cancel heq
        subst k
        rfl
      · intro g
        have hg : g ∈ ⋃ i, P.reps i • (P.parts i : Set G) := by
          rw [P.covers]
          exact Set.mem_univ g
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
        let h : P.parts i :=
          ⟨(P.reps i)⁻¹ * g, (mem_leftCoset_iff (P.reps i)).mp hi⟩
        refine ⟨⟨i, h⟩, ?_⟩
        simp [h])

@[simp]
theorem cellEquiv_apply (P : Group.ExactCovering G ι) (i : ι) (h : P.parts i) :
    P.cellEquiv ⟨i, h⟩ = P.reps i * (h : G) :=
  rfl

end Group.ExactCovering

end Erdos274
