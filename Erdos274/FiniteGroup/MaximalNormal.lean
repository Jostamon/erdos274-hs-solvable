/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Data.Fintype.Powerset

/-!
# Maximal normal subgroups of finite groups

A nontrivial finite group has a maximal proper normal subgroup, and the
quotient by one is simple.  General group theory, used by the subnormal union
bound (`KnownCases.Subnormal.UnionBound`) and by the construction of a
prime-normal chain in a solvable group (`FiniteGroup.SolvablePrimeNormalChain`).
-/

namespace Erdos274

universe u

/-- A nontrivial finite group has a maximal proper normal subgroup. -/
lemma exists_maximal_normal (G : Type u) [Group G] [Finite G] [Nontrivial G] :
    ∃ L : Subgroup G, L.Normal ∧ L ≠ ⊤ ∧
      ∀ N : Subgroup G, N.Normal → N ≠ ⊤ → L ≤ N → N = L := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G ↦ (H : Set G)) SetLike.coe_injective
  set S : Set (Subgroup G) := {N | N.Normal ∧ N ≠ ⊤} with hS_def
  have hfin : S.Finite := Set.toFinite S
  have hne : S.Nonempty := ⟨⊥, Subgroup.normal_bot, bot_ne_top⟩
  obtain ⟨L, hLmem, hLmax⟩ := hfin.exists_maximal hne
  exact ⟨L, hLmem.1, hLmem.2,
    fun N hN hNtop hLN ↦ le_antisymm (hLmax ⟨hN, hNtop⟩ hLN) hLN⟩

/-- The quotient by a maximal proper normal subgroup is simple. -/
lemma isSimpleGroup_quotient_of_maximal_normal {G : Type u} [Group G]
    {L : Subgroup G} [L.Normal] (hne : L ≠ ⊤)
    (hmax : ∀ N : Subgroup G, N.Normal → N ≠ ⊤ → L ≤ N → N = L) :
    IsSimpleGroup (G ⧸ L) := by
  have hnontriv : Nontrivial (G ⧸ L) := by
    obtain ⟨x, hx⟩ : ∃ x, x ∉ L := by
      by_contra h
      push Not at h
      exact hne (Subgroup.eq_top_iff' L |>.mpr h)
    exact ⟨QuotientGroup.mk x, 1, by
      simpa [QuotientGroup.eq_one_iff] using hx⟩
  refine ⟨fun N hN ↦ ?_⟩
  set M : Subgroup G := N.comap (QuotientGroup.mk' L) with hM_def
  have hMnormal : M.Normal := hN.comap (QuotientGroup.mk' L)
  have hLM : L ≤ M := by
    intro x hx
    simp only [hM_def, Subgroup.mem_comap]
    have h1 : QuotientGroup.mk' L x = 1 := by
      simpa [QuotientGroup.eq_one_iff] using hx
    rw [h1]
    exact N.one_mem
  have hmap : M.map (QuotientGroup.mk' L) = N :=
    Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective L) N
  by_cases hMtop : M = ⊤
  · right
    rw [← hmap, hMtop]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective L)
  · left
    have hML : M = L := hmax M hMnormal hMtop hLM
    rw [← hmap, hML, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

end Erdos274
