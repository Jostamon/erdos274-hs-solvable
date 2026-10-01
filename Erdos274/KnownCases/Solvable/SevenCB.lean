/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.ExactEight

/-!
# (CB) for the parts of a covering, and the `p = 7` closure

`DECISION_LOG` D98 §§6, 14; `solvable-herzog-schonheim-review.md` §1.  The
step-4 setting has `F ◁ G` with no nontrivial `p′`-quotient
(`CyclotomicBlock.IsPResidual`), e.g. `F = O^{p′}(G)`
(`Step4Structure.exists_structure`).  This is a hypothesis here: it describes
the setting and makes no new claim.

* `cb_loc`: **(CB) for a part.**  A non-universal part with `p ∤ ℓⱼ` has
  `q^{ord_p q} ∣ ℓⱼ` for some prime `q ≠ p` dividing `|G|`.  This is
  `CyclotomicBlock.cyclotomic_block_index`, applied inside `F` to
  `Hⱼ ⊓ F`, whose index in `F` is `ℓⱼ`.
* `false_of_structure`: `Chamber.false_of_covering_chamber` with (CB) and
  the exact-8 chamber (`ExactEight.exact_eight`) discharged.  At `p = 7` the
  primes `q` are `2`, `3` and `5`, because `q ∣ |G|`, `q ≤ 7` and `q ≠ 7`.
  No group-theoretic input is left as a hypothesis.
-/

namespace Erdos274

namespace SevenCB

open QuotientShadow SevenJoin Chamber CyclotomicBlock ExactEight

universe u v

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

omit [Fintype G] in
/-- **(CB) for the parts of a covering.** -/
theorem cb_loc [Finite G] [Group.IsSolvable G] {p : ℕ} [Fact p.Prime]
    (hres : IsPResidual p F) {j : κ} (hj : ¬ F ≤ C.parts j) (hpj : ¬ p ∣ loc C F j) :
    ∃ q, q.Prime ∧ q ≠ p ∧ q ∣ Nat.card G ∧ q ^ orderOf (q : ZMod p) ∣ loc C F j := by
  have hY : (C.parts j).subgroupOf F ≠ ⊤ := fun h ↦ hj (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨q, hq, hqp, hqF, hdvd⟩ := cyclotomic_block_index hres hY hpj
  exact ⟨q, hq, hqp, hqF.trans (Subgroup.card_subgroup_dvd_card F), hdvd⟩

omit [Fintype G] in
/-- **The `p = 7` residual of step 4 does not exist**, given the step-4
structure.

The hypotheses are the setting only: the primes of `|G|` are at most `7`;
`F ◁ G` has no nontrivial `7′`-quotient; the non-universal parts have distinct
indices, and there is at least one. -/
theorem false_of_structure [Finite G] [Group.IsSolvable G] [F.Normal]
    (hres : IsPResidual 7 F) (hG : ∀ p, p.Prime → p ∣ Nat.card G → p ≤ 7)
    (hdist : Set.InjOn (fun j ↦ (C.parts j).index) (nonUniv C F))
    (hne : (nonUniv C F).Nonempty) : False := by
  classical
  have := Fintype.ofFinite G
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine false_of_covering_chamber C F hG hdist hne (fun j hj ↦ ?_)
    fun j k hj δ hδj hδk _ ↦ exact_eight C F hres hj hδj hδk
  by_cases h7 : 7 ∣ loc C F j
  · exact Or.inl h7
  obtain ⟨q, hq, hq7, hqG, hdvd⟩ := cb_loc C F hres (Finset.mem_filter.mp hj).2 h7
  have hle := hG q hq hqG
  interval_cases q
  · exact absurd hq (by norm_num)
  · exact absurd hq (by norm_num)
  · exact Or.inr (Or.inl hdvd)
  · exact Or.inr (Or.inr (Or.inl hdvd))
  · exact absurd hq (by norm_num)
  · exact Or.inr (Or.inr (Or.inr hdvd))
  · exact absurd hq (by norm_num)
  · exact absurd rfl hq7

end SevenCB

end Erdos274
