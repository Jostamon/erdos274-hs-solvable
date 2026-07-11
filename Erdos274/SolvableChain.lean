/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.SubnormalUnionBound
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Finite solvable groups carry a prime-normal chain

A finite solvable group has a composition series whose quotients have
prime order (`Subgroup.PrimeNormalChain.of_isSolvable`).  Consequently the
totient union bound holds for a nonempty finite family of left cosets of
**arbitrary** subgroups of a finite solvable group
(`Erdos274.sum_totient_le_ncard_iUnion_of_isSolvable`) — this is the
"case 2" branch of Sun's Theorem 3.1 (Sun 2004, J. Algebra 273)
specialized to solvable groups, and it discharges "Gap B" of the
solvable Herzog–Schönheim pathway: only the `p ∤ [G:H]` supply ("Gap A",
see `docs/erdos274/SUN_BLUEPRINT.md`) remains open for solvable groups.
-/

namespace Subgroup

universe u

/-- Auxiliary induction form with cardinality fuel. -/
private theorem primeNormalChain_top_of_isSolvable_aux :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] [IsSolvable G],
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
      haveI := hLnormal
      haveI hsimple : IsSimpleGroup (G ⧸ L) :=
        Erdos274.isSimpleGroup_quotient_of_maximal_normal hLne hLmax
      -- The simple quotient of a solvable group is commutative, hence of
      -- prime order.
      have hcomm : ∀ a b : G ⧸ L, a * b = b * a :=
        IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
      letI : CommGroup (G ⧸ L) :=
        { (inferInstance : Group (G ⧸ L)) with mul_comm := hcomm }
      have hprime : L.index.Prime := by
        rw [Subgroup.index_eq_card]
        exact IsSimpleGroup.prime_card
      -- Recurse into `L`.
      have hLlt : Nat.card L < n := by
        have hmul : Nat.card L * L.index = Nat.card G := L.card_mul_index
        have h2 := hprime.two_le
        have h0 : 0 < Nat.card L := Nat.card_pos
        calc Nat.card L < Nat.card L * 2 := by omega
          _ ≤ Nat.card L * L.index := Nat.mul_le_mul_left _ h2
          _ = Nat.card G := hmul
          _ = n := hn
      have tail : Subgroup.PrimeNormalChain L :=
        (ih (Nat.card L) hLlt L rfl).map_subtype L
      exact Subgroup.PrimeNormalChain.step le_top (hLnormal.subgroupOf ⊤)
        (by rwa [Subgroup.relIndex_top_right]) tail

/-- **A finite solvable group has a prime-normal chain**: a composition
series from `⊥` to `⊤` whose successive quotients have prime order. -/
theorem PrimeNormalChain.of_isSolvable (G : Type u) [Group G] [Finite G]
    [IsSolvable G] : Subgroup.PrimeNormalChain (⊤ : Subgroup G) :=
  primeNormalChain_top_of_isSolvable_aux (Nat.card G) G rfl

end Subgroup

namespace Erdos274

open Finset
open scoped Pointwise

universe u v

/-- **The totient union bound in finite solvable groups** (Sun 2004,
Theorem 3.1, composition-series case): for a nonempty finite family of
left cosets `gⱼKⱼ` of **arbitrary** subgroups of a finite solvable group,
`∑ φ(d) ≤ |⋃ gⱼKⱼ|`, the sum over all divisors of all the `|Kⱼ|`. -/
theorem sum_totient_le_ncard_iUnion_of_isSolvable {G : Type u} [Group G]
    [Finite G] [IsSolvable G] {κ : Type v} [Fintype κ] [Nonempty κ]
    (g : κ → G) (K : κ → Subgroup G) :
    ∑ d ∈ univ.biUnion (fun j ↦ (Nat.card (K j)).divisors), d.totient ≤
      (⋃ j, g j • ((K j : Subgroup G) : Set G)).ncard :=
  sum_totient_le_ncard_iUnion_of_primeNormalChain
    (Subgroup.PrimeNormalChain.of_isSolvable G) g K

end Erdos274
