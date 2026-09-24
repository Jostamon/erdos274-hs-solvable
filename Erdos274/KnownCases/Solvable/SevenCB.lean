/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.ExactEight

/-!
# (CB) for the parts of a covering, and the `p = 7` closure from `F = KQ`

`DECISION_LOG` D98 §§6, 14.  The step-4 setting has `F = F_* = KQ`, where
* `K ◁ G` is a `p′`-group;
* `Q` is a `p`-group;
* `[K,Q] = K`.

These are hypotheses here: they describe the setting and make no new claim.

* `cb_loc`: **(CB) for a part.**  A non-universal part with `p ∤ ℓⱼ` has
  `q^{ord_p q} ∣ ℓⱼ` for some prime `q ∣ |K|`.  This is
  `CyclotomicBlock.cyclotomic_block_index`, applied inside `F` to
  `Hⱼ ⊓ F`, whose index in `F` is `ℓⱼ`.
* `false_of_structure`: `Chamber.false_of_covering_chamber` with (CB) and
  the exact-8 chamber (`ExactEight.exact_eight`) discharged.  At `p = 7` the
  primes `q ∣ |K|` are `2`, `3` and `5`, because `q ∣ |G|`, `q ≤ 7` and
  `7 ∤ |K|`.  No group-theoretic input is left as a hypothesis.
-/

namespace Erdos274

namespace SevenCB

open QuotientShadow SevenJoin Chamber CyclotomicBlock ExactEight

universe u v

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

omit [Fintype G] in
/-- **(CB) for the parts of a covering.** -/
theorem cb_loc [Finite G] [Group.IsSolvable G] {p : ℕ} [Fact p.Prime] {K Q : Subgroup G} [K.Normal]
    (hF : F = K ⊔ Q) (hQ : IsPGroup p Q) (hK : ¬ p ∣ Nat.card K) (hKQ : ⁅K, Q⁆ = K)
    {j : κ} (hj : ¬ F ≤ C.parts j) (hpj : ¬ p ∣ loc C F j) :
    ∃ q, q.Prime ∧ q ∣ Nat.card K ∧ q ^ orderOf (q : ZMod p) ∣ loc C F j := by
  have hKF : K ≤ F := hF ▸ le_sup_left
  have hQ' : IsPGroup p (Q.subgroupOf F) := hQ.comap_of_injective F.subtype F.subtype_injective
  have hK' : ¬ p ∣ Nat.card (K.subgroupOf F) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKF).toEquiv]
  obtain ⟨hKQ', hsup⟩ := subgroupOf_structure F hF hKQ
  have hY : (C.parts j).subgroupOf F ≠ ⊤ := fun h ↦ hj (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨q, hq, hqK, hdvd⟩ := cyclotomic_block_index hQ' hK' hKQ' hsup hY hpj
  refine ⟨q, hq, ?_, hdvd⟩
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKF).toEquiv] at hqK

omit [Fintype G] in
/-- **The `p = 7` residual of step 4 does not exist**, given the step-4
structure `F = KQ`.

The hypotheses are the setting only: the primes of `|G|` are at most `7`;
`F = K ⊔ Q`, with `K ◁ G` a `7′`-group, `Q` a `7`-group, and `[K,Q] = K`; the
non-universal parts have distinct indices, and there is at least one. -/
theorem false_of_structure [Finite G] [Group.IsSolvable G] [F.Normal] {K Q : Subgroup G}
    [K.Normal]
    (hF : F = K ⊔ Q) (hQ : IsPGroup 7 Q) (hK : ¬ 7 ∣ Nat.card K) (hKQ : ⁅K, Q⁆ = K)
    (hG : ∀ p, p.Prime → p ∣ Nat.card G → p ≤ 7)
    (hdist : Set.InjOn (fun j ↦ (C.parts j).index) (nonUniv C F))
    (hne : (nonUniv C F).Nonempty) : False := by
  classical
  have := Fintype.ofFinite G
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine false_of_covering_chamber C F hG hdist hne (fun j hj ↦ ?_)
    fun j k hj δ hδj hδk _ ↦ exact_eight C F hF hQ hKQ hj hδj hδk
  by_cases h7 : 7 ∣ loc C F j
  · exact Or.inl h7
  obtain ⟨q, hq, hqK, hdvd⟩ := cb_loc C F hF hQ hK hKQ (Finset.mem_filter.mp hj).2 h7
  have hqG : q ∣ Nat.card G := hqK.trans (Subgroup.card_subgroup_dvd_card K)
  have hq7 : q ≠ 7 := fun h ↦ hK (h ▸ hqK)
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
