/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic


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

@[expose] public section

open scoped Pointwise

namespace Erdos274

/-- An exact covering of a group `G` is a finite collection of subgroups `{H_1, ..., H_k}` and
representative `{g_1, ..., g_k}` such that the cosets `g_iH_i` are pairwise disjoint and their
union covers `G`.

Field for field (names, types and order) this is the upstream
`Erdos274.Group.ExactCovering` of formal-conjectures, so every statement about it here is a
statement about the upstream structure.  The `nonempty` field is automatic for subgroups
(`OneMemClass.coe_nonempty`) and is kept only for that match. -/
structure Group.ExactCovering (G : Type*) [Group G] (ι : Type*) [Fintype ι] where
  /-- The subgroups whose cosets form the partition. -/
  parts : ι → Subgroup G
  /-- A representative for each coset. -/
  reps : ι → G
  /-- Each part is nonempty (automatic for a subgroup; present upstream). -/
  nonempty (i : ι) : (parts i : Set G).Nonempty
  disjoint : (Set.univ (α := ι)).PairwiseDisjoint fun i ↦ reps i • (parts i : Set G)
  covers : ⋃ i, reps i • (parts i : Set G) = Set.univ

namespace Group.ExactCovering

variable {G ι : Type*} [Group G] [Fintype ι] (P : Group.ExactCovering G ι)

/-- Every element of `G` lies in one of the cosets of an exact covering. -/
lemma exists_mem (x : G) : ∃ i, x ∈ P.reps i • (P.parts i : Set G) := by
  simpa [← Set.mem_iUnion] using P.covers ▸ Set.mem_univ x

end Group.ExactCovering

end Erdos274
