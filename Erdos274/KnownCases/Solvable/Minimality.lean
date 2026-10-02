/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon, OpenAI
-/
module

public import Erdos274.Statements
public import Erdos274.ExactCovering.Quotient
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Algebra.Group.Subgroup.Finite


/-!
# Solvable HS: least-order endpoint and proper-coset subpartitions

The important observation formalized here is that, in a least-order solvable
counterexample, it is enough to find a proper subgroup which inherits an exact
cover with pairwise distinct relative indices.  The proof restricts the
covering to a complementary coset and applies the proper-subpartition theorem
to its active parts.

No research axiom occurs in this file.
-/

@[expose] public section

namespace Erdos274

universe u v

/-- Every smaller finite *solvable* group satisfies HS.  This is the correct
minimality predicate for a proof restricted to solvable groups; it is weaker
than `AllFiniteGroupsBelowSatisfyHerzogSchonheim`. -/
def AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim
    (n : ℕ) : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q] [Group.IsSolvable Q],
    Nat.card Q < n → GroupSatisfiesHerzogSchonheim.{u, v} Q

/-- Minimality rules out a nontrivial normal subgroup contained in every part:
the covering would descend to a smaller solvable quotient with the same
indices. -/
theorem false_of_nontrivial_normal_subgroup_in_all_parts
    {G : Type u} [Group G] [Finite G] [Group.IsSolvable G] {ι : Type v} [Fintype ι]
    (C : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι)
    (hinj : Function.Injective fun i ↦ (C.parts i).index)
    (hmin : AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim.{u, v} (Nat.card G))
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) (hfull : ∀ i, N ≤ C.parts i) :
  False := by
  classical
  have hNcard : 1 < Nat.card N := by
    rw [Finite.one_lt_card_iff_nontrivial]
    exact (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hqcard : Nat.card (G ⧸ N) < Nat.card G := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hqpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    rw [hcard]
    calc Nat.card (G ⧸ N) = Nat.card (G ⧸ N) * 1 := (Nat.mul_one _).symm
      _ < Nat.card (G ⧸ N) * Nat.card N :=
        Nat.mul_lt_mul_of_pos_left hNcard hqpos
  let C' := C.quotient N hfull
  obtain ⟨i, j, hij, hidx⟩ := hmin (G ⧸ N) hqcard ι C' hι
  exact hij (hinj (by
    have hi := C.quotient_part_index N hfull i
    have hj := C.quotient_part_index N hfull j
    simpa only [C'] using hi.symm.trans (hidx.trans hj)))

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
