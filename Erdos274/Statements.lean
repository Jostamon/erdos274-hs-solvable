/-
Copyright (c) 2026 Erdos 274 Agentic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Erdos274.Defs
import Mathlib.GroupTheory.Index

/-! # Herzog--Schönheim statements shared by proof modules -/

universe u v
namespace Erdos274

/-- A group satisfies the index form of Herzog--Schönheim for index types in `Type v`. -/
def GroupSatisfiesHerzogSchonheim (G : Type u) [Group G] : Prop :=
  ∀ (ι : Type v) [Fintype ι], ∀ (P : Group.ExactCovering G ι),
    1 < Fintype.card ι →
      ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index

/-- Every finite group of cardinality below `n` satisfies Herzog--Schönheim. -/
def AllFiniteGroupsBelowSatisfyHerzogSchonheim (n : ℕ) : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q],
    Nat.card Q < n → GroupSatisfiesHerzogSchonheim.{u, v} Q

end Erdos274
