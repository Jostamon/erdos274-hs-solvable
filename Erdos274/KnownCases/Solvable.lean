/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.Research.SolvableHS.Step4

/-!
# The Herzog–Schönheim conjecture for finite solvable groups

The solvable case of Erdős problem 274, stated in the exact shape of the
formal-conjectures file `FormalConjectures/ErdosProblems/274.lean`
(google-deepmind/formal-conjectures): the same `Erdos274.Group.ExactCovering`
(field for field, see `Erdos274.Defs`), the same hypotheses, and
the same conclusions, with `[Finite G] [Group.IsSolvable G]` added.

## Main results

* `Erdos274.herzog_schonheim.variants.solvable`: upstream `herzog_schonheim`
  (index form) for finite solvable `G`.
* `Erdos274.erdos_274.variants.solvable`: the cardinality form, shaped like
  upstream `erdos_274.variants.abelian`.

Both rest on `Step4.herzog_schonheim_of_solvable` (`DECISION_LOG` D100).
-/

open scoped Pointwise Cardinal

namespace Erdos274

set_option linter.unusedVariables false in
/-- **The Herzog–Schönheim conjecture for finite solvable groups**, index form:
upstream `herzog_schonheim` with `[Finite G] [Group.IsSolvable G]` added.
`hG` is kept, unused, to match upstream. -/
@[nolint unusedArguments]
theorem herzog_schonheim.variants.solvable {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (hι : 1 < Fintype.card ι) (P : Group.ExactCovering G ι) :
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index :=
  Step4.herzog_schonheim_of_solvable G ι P hι

set_option linter.unusedVariables false in
/-- **The Herzog–Schönheim conjecture for finite solvable groups**, cardinality
form: upstream `erdos_274.variants.abelian` with `CommGroup` replaced by a
solvable `Group`.  `hG` is kept, unused, to match upstream. -/
@[nolint unusedArguments]
theorem erdos_274.variants.solvable {G : Type*} [Fintype G] [Group G]
    [Group.IsSolvable G] (hG : 1 < Fintype.card G) {ι : Type*} [Fintype ι]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) := by
  obtain ⟨i, j, hij, h⟩ := Step4.herzog_schonheim_of_solvable G ι P hι
  refine ⟨i, j, hij, ?_⟩
  have hcard : Nat.card (P.parts i) = Nat.card (P.parts j) :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
      (H := P.parts i))) (by rw [Subgroup.card_mul_index, h, Subgroup.card_mul_index])
  rw [← Nat.cast_card, ← Nat.cast_card, hcard]

/-! ### Compile-time guards against the upstream statements -/

-- Upstream `herzog_schonheim`, with `[Finite G] [Group.IsSolvable G]` added.
example :
    ∀ {G : Type*} [Group G] [Finite G] [Group.IsSolvable G],
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
  @erdos_274.variants.solvable

-- The upstream structure, field for field.
example {G : Type*} [Group G] {ι : Type*} [Fintype ι] (parts : ι → Subgroup G) (reps : ι → G)
    (nonempty : ∀ i, (parts i : Set G).Nonempty)
    (disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun (i : ι) ↦ reps i • (parts i : Set G))
    (covers : ⋃ i, reps i • (parts i : Set G) = Set.univ) : Group.ExactCovering G ι :=
  { parts, reps, nonempty, disjoint, covers }

end Erdos274
