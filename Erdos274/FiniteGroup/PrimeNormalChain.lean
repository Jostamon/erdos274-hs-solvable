/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Mathlib.GroupTheory.IndexNormal


/-! Prime-index normal chains of subgroups. -/

@[expose] public section

namespace Subgroup

universe u v

/-- A chain from `H` to `⊥` whose successive inclusions are normal and have
prime relative index. Normality is deliberately relative to the preceding
subgroup, not to the original ambient group. -/
inductive PrimeNormalChain {G : Type u} [Group G] : Subgroup G → Prop
  | bot : PrimeNormalChain ⊥
  | step {H K : Subgroup G} (hKH : K ≤ H)
      (hnormal : (K.subgroupOf H).Normal) (hprime : (K.relIndex H).Prime)
      (tail : PrimeNormalChain K) : PrimeNormalChain H

namespace PrimeNormalChain

/-- Transport a prime-normal chain through an injective homomorphism. -/
theorem map {G : Type u} {G' : Type v} [Group G] [Group G']
    {H : Subgroup G} (c : PrimeNormalChain H) (f : G →* G')
    (hf : Function.Injective f) : PrimeNormalChain (H.map f) := by
  induction c with
  | bot => simpa using (PrimeNormalChain.bot : PrimeNormalChain (⊥ : Subgroup G'))
  | @step H K hKH hn hp tail ih =>
      refine PrimeNormalChain.step (map_mono hKH) ?_ ?_ ih
      · constructor
        intro x hx y
        obtain ⟨x0, hxK, hx⟩ := hx
        obtain ⟨y0, hyH, hy⟩ := y.property
        change (y : G') * (x : G') * (y : G')⁻¹ ∈ Subgroup.map f K
        refine ⟨y0 * x0 * y0⁻¹,
          hn.conj_mem ⟨x0, hKH hxK⟩ hxK ⟨y0, hyH⟩, ?_⟩
        rw [map_mul, map_mul, map_inv, hx, hy]
        rfl
      · simpa [Subgroup.relIndex_map_map_of_injective K H hf] using hp

/-- Regard a chain in the abstract group `H` as a chain ending at the
ambient subgroup `H`. -/
theorem map_subtype {G : Type u} [Group G] (H : Subgroup G)
    (c : PrimeNormalChain (⊤ : Subgroup H)) : PrimeNormalChain H := by
  have he : Subgroup.map H.subtype ⊤ = H := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  rw [← he]
  exact c.map H.subtype H.subtype_injective

/-- Restrict a chain ending at the subgroup `H` to a chain filling the whole
group `H`. -/
theorem comap_subtype {G : Type u} [Group G] {H : Subgroup G}
    (c : PrimeNormalChain H) : PrimeNormalChain (⊤ : Subgroup H) := by
  induction c with
  | bot =>
      have hbot : (⊤ : Subgroup (⊥ : Subgroup G)) = ⊥ := by
        ext x
        obtain ⟨x, hx⟩ := x
        simp [Subgroup.mem_bot, Subtype.ext_iff, Subgroup.mem_bot.mp hx]
      rw [hbot]
      exact PrimeNormalChain.bot
  | @step H K hKH hnormal hprime tail ih =>
      have hmap := ih.map (Subgroup.inclusion hKH)
        (Subgroup.inclusion_injective hKH)
      have htop : (⊤ : Subgroup K).map (Subgroup.inclusion hKH) =
          K.subgroupOf H := by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨(x : G), hx⟩, Subgroup.mem_top _, rfl⟩
      rw [htop] at hmap
      refine PrimeNormalChain.step le_top ?_ ?_ hmap
      · exact hnormal.comap (⊤ : Subgroup H).subtype
      · rw [Subgroup.relIndex_top_right]
        exact hprime

/-- A chain ending at a nontrivial subgroup starts with a step. -/
theorem exists_step_of_ne_bot {G : Type u} [Group G] {H : Subgroup G}
    (c : PrimeNormalChain H) (h : H ≠ ⊥) :
    ∃ K, K ≤ H ∧ (K.subgroupOf H).Normal ∧ (K.relIndex H).Prime ∧
      PrimeNormalChain K := by
  cases c with
  | bot => exact absurd rfl h
  | step hKH hnormal hprime tail => exact ⟨_, hKH, hnormal, hprime, tail⟩

end PrimeNormalChain

/-- A subgroup whose copy inside `⊤` is normal is normal. -/
lemma normal_of_normal_subgroupOf_top {G : Type u} [Group G] {L : Subgroup G}
    (h : (L.subgroupOf ⊤).Normal) : L.Normal := by
  constructor
  intro x hx y
  have := h.conj_mem ⟨x, Subgroup.mem_top x⟩
    (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨y, Subgroup.mem_top y⟩
  simpa [Subgroup.mem_subgroupOf] using this

end Subgroup
