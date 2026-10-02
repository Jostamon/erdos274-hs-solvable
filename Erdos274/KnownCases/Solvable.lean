/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.KnownCases.Solvable.Step4
public import Erdos274.ExactCovering.Cardinality
public import Erdos274.ExactCovering.Quotient


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
groups (`herzogSchonheim_iff_finite` in `Reduction.Statements`; this file uses
the two ingredients directly, not that equivalence):

* every part of a finite exact coset covering has finite index
  (`Group.ExactCovering.part_finiteIndex`, from B. H. Neumann's lemma as
  `Subgroup.leftCoset_cover_filter_FiniteIndex` in Mathlib);
* so the normal core `N` of the intersection of the parts has finite index, is
  contained in every part, and the covering descends to the finite group `G/N`
  with the same indices (`Group.ExactCovering.finiteQuotientCover`).

A quotient of a solvable group is solvable, so the finite theorem
`Step4.herzog_schonheim_of_solvable` (`DECISION_LOG` D100) applies to `G/N`
whether or not `G` is finite. Its proof is assembled from focused exact-cover,
finite-group, arithmetic, and solvable-closure modules. The final import path
uses the extracted cell, piece, quotient-shadow, and covering-weight
foundations. It omits the earlier `NormaliserSlice`, `MassForm`, and full
`QuotientShadow` implementations, which remain available to library and
archive modules.

The signature checks against the upstream statements, and
`herzogSchonheim_iff_upstream`, are in `Reduction.Upstream`, so that the
reduction library is not a dependency of this theorem.

## Main results

* `Erdos274.herzog_schonheim.variants.solvable`: upstream `herzog_schonheim`
  (index form) with `[Group.IsSolvable G]` added.
* `Erdos274.erdos_274.variants.solvable`: the cardinality form, for every
  solvable group.
* `Erdos274.erdos_274.variants.solvable_fintype`: the cardinality form in the
  shape of upstream `erdos_274.variants.abelian`, with `CommGroup` replaced by
  a solvable `Group`.
-/

@[expose] public section

open scoped Pointwise Cardinal

namespace Erdos274

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

/-- **The Herzog–Schönheim conjecture for solvable groups**, cardinality form
(the right-hand side of upstream `erdos_274`, for solvable `G`).  `G` may be
infinite.  `hG` is kept, unused, to match upstream. -/
theorem erdos_274.variants.solvable {G : Type*} [Group G]
    [Group.IsSolvable G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) := by
  obtain ⟨i, j, hij, h⟩ := herzog_schonheim.variants.solvable hG hι P
  exact ⟨i, j, hij, exactCovering_cardinalMk_eq_of_index_eq P i j h⟩

/-- The cardinality form in the shape of upstream `erdos_274.variants.abelian`,
with `[CommGroup G]` replaced by `[Group G] [Group.IsSolvable G]`. -/
theorem erdos_274.variants.solvable_fintype {G : Type*} [Fintype G] [Group G]
    [Group.IsSolvable G] (hG : 1 < Fintype.card G) {ι : Type*} [Fintype ι]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) :=
  erdos_274.variants.solvable
    ((ENat.one_lt_card_iff_nontrivial G).mpr (Fintype.one_lt_card_iff_nontrivial.mp hG)) P hι

end Erdos274
