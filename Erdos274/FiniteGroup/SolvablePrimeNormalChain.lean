/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.FiniteGroup.MaximalNormal
public import Erdos274.FiniteGroup.PrimeNormalChain
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Cyclic


/-! # Prime-normal chains in finite solvable groups -/

@[expose] public section

namespace Subgroup

universe u

/-- Auxiliary induction form with cardinality fuel. -/
private theorem primeNormalChain_top_of_isSolvable_aux :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G = n → Subgroup.PrimeNormalChain (⊤ : Subgroup G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ hn
    rcases subsingleton_or_nontrivial G with hs | hs
    · have htop : (⊤ : Subgroup G) = ⊥ := by
        ext x
        simp [Subsingleton.elim x 1]
      exact htop ▸ Subgroup.PrimeNormalChain.bot
    · obtain ⟨L, hLnormal, hLne, hLmax⟩ := Erdos274.exists_maximal_normal G
      have := hLnormal
      have hsimple : IsSimpleGroup (G ⧸ L) :=
        Erdos274.isSimpleGroup_quotient_of_maximal_normal hLne hLmax
      -- The simple quotient of a solvable group is commutative, hence of
      -- prime order.
      have hcomm : ∀ a b : G ⧸ L, a * b = b * a :=
        IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
      let : CommGroup (G ⧸ L) :=
        { (inferInstance : Group (G ⧸ L)) with mul_comm := hcomm }
      have hprime : L.index.Prime := by
        rw [Subgroup.index_eq_card]
        exact IsSimpleGroup.prime_card
      -- Recurse into `L`.
      have hLlt : Nat.card L < n := by
        exact ((Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hLne)).trans_eq
          Subgroup.card_top).trans_eq hn
      have tail : Subgroup.PrimeNormalChain L :=
        (ih (Nat.card L) hLlt L rfl).map_subtype L
      exact Subgroup.PrimeNormalChain.step le_top (hLnormal.subgroupOf ⊤)
        (by rwa [Subgroup.relIndex_top_right]) tail

/-- **A finite solvable group has a prime-normal chain**: a composition
series from `⊥` to `⊤` whose successive quotients have prime order. -/
theorem PrimeNormalChain.of_isSolvable (G : Type u) [Group G] [Finite G]
    [Group.IsSolvable G] : Subgroup.PrimeNormalChain (⊤ : Subgroup G) :=
  primeNormalChain_top_of_isSolvable_aux (Nat.card G) G rfl

end Subgroup
