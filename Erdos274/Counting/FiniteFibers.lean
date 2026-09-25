/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

/-! # Counting finite sets by fibres of a map -/

namespace Erdos274

open scoped BigOperators

/-- Count a finite set by its fibres under a labelling map. -/
lemma ncard_eq_sum_set_fibers {α β : Type*} [Finite α] [Fintype β]
    (S : Set α) (f : α → β) :
    S.ncard = ∑ b : β, (S ∩ {a | f a = b}).ncard := by
  classical
  have : Fintype α := Fintype.ofFinite α
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext a
  simp

end Erdos274
