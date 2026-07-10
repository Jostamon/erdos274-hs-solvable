/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Mathlib.GroupTheory.IndexNormal

/-! Prime-index normal chains of subgroups. -/

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

end PrimeNormalChain
end Subgroup
