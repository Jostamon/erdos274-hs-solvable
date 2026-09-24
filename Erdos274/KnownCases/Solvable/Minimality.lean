/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon, OpenAI
-/
import Erdos274.Spectrum.Basic
import Mathlib.GroupTheory.Solvable

/-!
# Solvable HS: least-order endpoint and proper-coset subpartitions

The important observation formalized here is that, in a least-order solvable
counterexample, it is enough to find a proper subgroup which inherits an exact
cover with pairwise distinct relative indices.  This is the endpoint that a
global affine compression theorem should produce.

No research axiom occurs in this file.
-/

namespace Erdos274

universe u v

/-- Every smaller finite *solvable* group satisfies HS.  This is the correct
minimality predicate for a proof restricted to solvable groups; it is weaker
than `AllFiniteGroupsBelowSatisfyHerzogSchonheim`. -/
def AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim
    (n : ℕ) : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q] [Group.IsSolvable Q],
    Nat.card Q < n → GroupSatisfiesHerzogSchonheim.{u, v} Q

/-- A formal endpoint for a successful global compression.

`Q` is an exact covering of a proper subgroup `K`; `e` records the original
source labels; and `index_factor` is the tower formula saying that the original
index equals the common ambient factor `[G:K]` times the relative index in
`K`.  Therefore distinct original indices imply distinct relative indices. -/
def Group.ExactCovering.HasProperCounterexampleSubpartition
    {G : Type u} [Group G] {ι : Type v} [Fintype ι]
    (P : Group.ExactCovering G ι) : Prop :=
  ∃ (K : Subgroup G) (κ : Type v) (_ : Fintype κ)
      (Q : Group.ExactCovering K κ) (e : κ ↪ ι),
    K < ⊤ ∧
    1 < Fintype.card κ ∧
    ∀ j : κ,
      (P.parts (e j)).index = K.index * (Q.parts j).index

namespace Group.ExactCovering

variable {G : Type u} [Group G] [Finite G]
variable {ι : Type v} [Fintype ι]

variable [Group.IsSolvable G]

/-- A least-order solvable distinct-index counterexample cannot contain the
formal proper-subpartition endpoint above. -/
theorem no_properCounterexampleSubpartition_of_solvable_minimality
    (P : Group.ExactCovering G ι)
    (hinjective : Function.Injective fun i ↦ (P.parts i).index)
    (hminimal :
      AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim.{u, v} (Nat.card G)) :
    ¬ P.HasProperCounterexampleSubpartition := by
  intro hsub
  rcases hsub with ⟨K, κ, instκ, Q, e, hK, hκ, hfactor⟩
  let : Fintype κ := instκ
  have hKcard : Nat.card K < Nat.card G :=
    (Subgroup.card_lt_of_lt hK).trans_eq Subgroup.card_top
  have hHS : GroupSatisfiesHerzogSchonheim.{u, v} K :=
    hminimal K hKcard
  obtain ⟨a, b, hab, hlocal⟩ := hHS κ Q hκ
  have hglobal :
      (P.parts (e a)).index = (P.parts (e b)).index := by
    rw [hfactor a, hfactor b, hlocal]
  have heq : e a = e b := hinjective hglobal
  exact hab (e.injective heq)

end Group.ExactCovering
end Erdos274
