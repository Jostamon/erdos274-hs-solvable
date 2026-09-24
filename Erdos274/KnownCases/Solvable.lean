/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.Research.SolvableHS.Step4
import Erdos274.Reduction.Statements

/-!
# The Herzog–Schönheim conjecture for solvable groups

The solvable case of Erdős problem 274, for **every** solvable group, finite
or infinite.  It is stated in the exact shape of the formal-conjectures file
`FormalConjectures/ErdosProblems/274.lean` (google-deepmind/formal-conjectures):
the same `Erdos274.Group.ExactCovering` (field for field, see
`Erdos274.Defs`), the same hypotheses and the same conclusions,
with only `[Group.IsSolvable G]` added.

## From arbitrary groups to finite ones

Herzog–Schönheim is a conjecture about arbitrary groups.  It reduces to finite
groups (`herzogSchonheim_iff_finite` in `Reduction.Statements`):

* every part of a finite exact coset covering has finite index
  (`Group.ExactCovering.part_finiteIndex`, from B. H. Neumann's lemma as
  `Subgroup.leftCoset_cover_filter_FiniteIndex` in Mathlib);
* so the normal core `N` of the intersection of the parts has finite index, is
  contained in every part, and the covering descends to the finite group `G/N`
  with the same indices (`Group.ExactCovering.finiteQuotientCover`).

A quotient of a solvable group is solvable, so the finite theorem
`Step4.herzog_schonheim_of_solvable` (`DECISION_LOG` D100) applies to `G/N`
whether or not `G` is finite.

## Main results

* `Erdos274.herzog_schonheim.variants.solvable`: upstream `herzog_schonheim`
  (index form) with `[Group.IsSolvable G]` added.
* `Erdos274.erdos_274.variants.solvable`: the cardinality form, for every
  solvable group.
* `Erdos274.erdos_274.variants.solvable_fintype`: the cardinality form in the
  shape of upstream `erdos_274.variants.abelian`, with `CommGroup` replaced by
  a solvable `Group`.
-/

open scoped Pointwise Cardinal

namespace Erdos274

universe u v

set_option linter.unusedVariables false in
/-- **The Herzog–Schönheim conjecture for solvable groups**, index form:
upstream `herzog_schonheim` with `[Group.IsSolvable G]` added.  `G` may be
infinite.  `hG` is kept, unused, to match upstream. -/
@[nolint unusedArguments]
theorem herzog_schonheim.variants.solvable {G : Type*} [Group G]
    [Group.IsSolvable G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (hι : 1 < Fintype.card ι) (P : Group.ExactCovering G ι) :
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  have : Finite (G ⧸ P.commonCore) := P.finite_commonCore_quotient
  exact P.exists_equal_index_of_finiteQuotientCover
    (Step4.herzog_schonheim_of_solvable (G ⧸ P.commonCore) ι P.finiteQuotientCover hι)

set_option linter.unusedVariables false in
/-- **The Herzog–Schönheim conjecture for solvable groups**, cardinality form
(the right-hand side of upstream `erdos_274`, for solvable `G`).  `G` may be
infinite.  `hG` is kept, unused, to match upstream. -/
@[nolint unusedArguments]
theorem erdos_274.variants.solvable {G : Type*} [Group G]
    [Group.IsSolvable G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) := by
  have : Finite (G ⧸ P.commonCore) := P.finite_commonCore_quotient
  obtain ⟨i, j, hij, h⟩ :=
    Step4.herzog_schonheim_of_solvable (G ⧸ P.commonCore) ι P.finiteQuotientCover hι
  exact ⟨i, j, hij, finiteQuotientCover_cardinalMk_eq_imp P i j
    ((subgroup_cardinalMk_eq_iff_index_eq _ _).mpr h)⟩

/-- The cardinality form in the shape of upstream `erdos_274.variants.abelian`,
with `[CommGroup G]` replaced by `[Group G] [Group.IsSolvable G]`. -/
theorem erdos_274.variants.solvable_fintype {G : Type*} [Fintype G] [Group G]
    [Group.IsSolvable G] (hG : 1 < Fintype.card G) {ι : Type*} [Fintype ι]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) :=
  erdos_274.variants.solvable
    ((ENat.one_lt_card_iff_nontrivial G).mpr (Fintype.one_lt_card_iff_nontrivial.mp hG)) P hι

/-! ### Compile-time guards against the upstream statements -/

/-- Upstream `herzog_schonheim` is the proposition `HerzogSchonheim` of
`Reduction.Statements` (binders reordered), which is equivalent to its
restriction to finite groups (`herzogSchonheim_iff_finite`). -/
theorem herzogSchonheim_iff_upstream :
    HerzogSchonheim.{u, v} ↔
      ∀ {G : Type u} [Group G], 1 < ENat.card G →
        ∀ {ι : Type v} [Fintype ι], 1 < Fintype.card ι →
          ∀ (P : Group.ExactCovering G ι),
            ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index :=
  ⟨fun h _ _ hG _ _ hι P ↦ h _ hG _ P hι, fun h _ _ hG _ _ P hι ↦ h hG hι P⟩

-- Upstream `herzog_schonheim`, with `[Group.IsSolvable G]` added.
example :
    ∀ {G : Type*} [Group G] [Group.IsSolvable G],
      1 < ENat.card G →
      ∀ {ι : Type*} [Fintype ι],
        1 < Fintype.card ι →
        (P : Group.ExactCovering G ι) →
        ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index :=
  @herzog_schonheim.variants.solvable

-- Upstream `erdos_274.variants.abelian`, with `CommGroup` replaced by a solvable `Group`.
example :
    ∀ {G : Type*} [Fintype G] [Group G] [Group.IsSolvable G],
      1 < Fintype.card G →
      ∀ {ι : Type*} [Fintype ι] (P : Group.ExactCovering G ι),
        1 < Fintype.card ι →
        ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) :=
  @erdos_274.variants.solvable_fintype

-- The upstream structure, field for field.
example {G : Type*} [Group G] {ι : Type*} [Fintype ι] (parts : ι → Subgroup G) (reps : ι → G)
    (nonempty : ∀ i, (parts i : Set G).Nonempty)
    (disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun (i : ι) ↦ reps i • (parts i : Set G))
    (covers : ⋃ i, reps i • (parts i : Set G) = Set.univ) : Group.ExactCovering G ι :=
  { parts, reps, nonempty, disjoint, covers }

end Erdos274
