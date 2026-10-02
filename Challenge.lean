module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite


/-!
# The Herzog–Schönheim conjecture for solvable groups

An *exact covering* of a group `G` is a partition of `G` into finitely many left
cosets `g_i H_i` of subgroups `H_i`.  The **Herzog–Schönheim conjecture** asserts that
if there are at least two cosets, then two of the subgroups `H_i`, `H_j` (`i ≠ j`)
have the same index.  The conjecture is open for arbitrary groups; the statements
below assert it for **every solvable group**, finite or infinite.  Erdős problem 274
asks the weaker, cardinality form (two of the subgroups have the same cardinality),
which follows from the index form.

The structure `Erdos274.Group.ExactCovering` below is, field for field, the one in
`FormalConjectures/ErdosProblems/274.lean` of google-deepmind/formal-conjectures
(<https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/274.lean>),
and the hypotheses and conclusions are those of the upstream `herzog_schonheim` (index form)
and of the conclusion of `erdos_274` and `erdos_274.variants.abelian` (cardinality form; upstream
`erdos_274` is phrased as an `answer(sorry) ↔ ∃ …` existence statement, its negation is our
conclusion), with `[Group.IsSolvable G]` added.  Under the hypotheses, `G` is
any solvable group, `ι` any finite index type with at least two elements, and the
hypothesis `1 < ENat.card G` is kept (unused) only to match upstream.

## Compared declarations

* `Erdos274.Palomar.herzog_schonheim_solvable`: two of the parts have equal
  `Subgroup.index`.
* `Erdos274.Palomar.erdos_274_solvable`: two of the parts have equal cardinality
  (`Cardinal.mk`), for every solvable `G`.

The first is the Herzog–Schönheim conjecture (index form) and the second is Erdős problem 274 (cardinality form), each restricted to solvable groups.  Literature status, including what was already known (finite nilpotent, pyramidal, simple and symmetric groups) and the withdrawn 2019 claim for solvable groups, is in `README.md`.

There are no extra assumptions, no `sorry` outside this Challenge, and no custom
definitions other than `ExactCovering`.
-/

@[expose] public section

open scoped Pointwise Cardinal

namespace Erdos274

/-- An exact covering of a group `G` is a finite collection of subgroups `{H_1, ..., H_k}` and
representative `{g_1, ..., g_k}` such that the cosets `g_iH_i` are pairwise disjoint and their
union covers `G`. -/
structure Group.ExactCovering (G : Type*) [Group G] (ι : Type*) [Fintype ι] where
  /-- The subgroups whose cosets form the partition. -/
  parts : ι → Subgroup G
  /-- A representative for each coset. -/
  reps : ι → G
  /-- Each part is nonempty (automatic for a subgroup; present upstream). -/
  nonempty (i : ι) : (parts i : Set G).Nonempty
  disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun i ↦ reps i • (parts i : Set G)
  covers : ⋃ i, reps i • (parts i : Set G) = Set.univ

namespace Palomar

/-- **Herzog–Schönheim for solvable groups**, index form: in an exact covering of a solvable
group `G` by at least two cosets, two distinct parts have the same index. -/
theorem herzog_schonheim_solvable {G : Type*} [Group G]
    [Group.IsSolvable G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (hι : 1 < Fintype.card ι) (P : Group.ExactCovering G ι) :
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  sorry

/-- **Herzog–Schönheim for solvable groups**, cardinality form (the form asked in Erdős problem 274): in an exact
covering of a solvable group `G` by at least two cosets, two distinct parts have the same
cardinality. -/
theorem erdos_274_solvable {G : Type*} [Group G]
    [Group.IsSolvable G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) := by
  sorry


end Palomar

end Erdos274
