/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.Order.Preorder.Finite

/-! # Elementary-abelian minimal normal subgroups

General finite group theory:

* `exists_minimal_normal_ne_bot`: a nontrivial finite group has a minimal
  nontrivial normal subgroup;
* `commutator_self_eq_bot_of_minimal_normal`: in a solvable group it is
  commutative;
* `minimal_normal_is_elementary_abelian`: in a finite solvable group it is an
  elementary abelian `p`-group;
* `exists_prime_of_minimal_normal_section`: the same for a **section** `V/N`
  between normal subgroups `N < V` with nothing normal strictly between,
  stated in `G` (`vᵖ ∈ N`, and `V` commutes modulo `N`).
-/

open scoped IsMulCommutative

namespace Erdos274

/-- Every nontrivial finite group has a **minimal nontrivial normal subgroup**: a normal
subgroup `M ≠ ⊥` such that every nontrivial normal subgroup contained in `M` equals `M`. -/
theorem exists_minimal_normal_ne_bot (L : Type*) [Group L] [Finite L] [Nontrivial L] :
    ∃ M : Subgroup L, M.Normal ∧ M ≠ ⊥ ∧
      ∀ N : Subgroup L, N.Normal → N ≠ ⊥ → N ≤ M → N = M := by
  have : Finite (Subgroup L) :=
    Finite.of_injective (fun H : Subgroup L => (H : Set L)) SetLike.coe_injective
  have htop : (⊤ : Subgroup L).Normal ∧ (⊤ : Subgroup L) ≠ ⊥ := by
    refine ⟨inferInstance, fun h => ?_⟩
    obtain ⟨g, hg⟩ := exists_ne (1 : L)
    exact hg (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top g))
  obtain ⟨M, -, hM⟩ := Finite.exists_le_minimal
    (p := fun N : Subgroup L => N.Normal ∧ N ≠ ⊥) (a := (⊤ : Subgroup L)) htop
  exact ⟨M, hM.1.1, hM.1.2, fun N hN hNne hNle => hM.eq_of_le ⟨hN, hNne⟩ hNle⟩

/-- A minimal nontrivial normal subgroup `M` of a solvable group is **commutative**: the
commutator subgroup `⁅M, M⁆` is normal in the ambient group and, by solvability, strictly
below `M`, so minimality forces `⁅M, M⁆ = ⊥`. -/
theorem commutator_self_eq_bot_of_minimal_normal {L : Type*} [Group L] [Group.IsSolvable L]
    {M : Subgroup L} (hMn : M.Normal) (hMne : M ≠ ⊥)
    (hmin : ∀ N : Subgroup L, N.Normal → N ≠ ⊥ → N ≤ M → N = M) :
    ⁅M, M⁆ = ⊥ := by
  by_contra hC
  have := hMn
  exact (Group.IsSolvable.commutator_lt_of_ne_bot hMne).ne
    (hmin ⁅M, M⁆ inferInstance hC (Subgroup.commutator_le_self M))

/-- A minimal nontrivial normal subgroup of a finite solvable group is an
elementary abelian `p`-group: it is commutative, has prime exponent, and has
prime-power cardinality with positive exponent. -/
theorem minimal_normal_is_elementary_abelian
    {G : Type*} [Group G] [Group.IsSolvable G]
    {M : Subgroup G} [Finite M] (hMn : M.Normal) (hMne : M ≠ ⊥)
    (hmin : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ≤ M → N = M) :
    ∃ p a : ℕ, p.Prime ∧ 0 < a ∧ Nat.card M = p ^ a ∧
      IsMulCommutative M ∧ ∀ x : M, x ^ p = 1 := by
  have hMM : ⁅M, M⁆ = ⊥ :=
    commutator_self_eq_bot_of_minimal_normal hMn hMne hmin
  have hcomm : IsMulCommutative M :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMM)
  let : IsMulCommutative M := hcomm
  have hMcard_ne_one : Nat.card M ≠ 1 :=
    (M.one_lt_card_iff_ne_bot.mpr hMne).ne'
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hMcard_ne_one
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have hxne : x ≠ 1 := by
    intro hx
    exact hp.ne_one (hxorder.symm.trans (orderOf_eq_one_iff.mpr hx))
  let K : Subgroup M := (powMonoidHom p).ker
  have hxK : x ∈ K := by
    change x ^ p = 1
    rw [← hxorder]
    exact pow_orderOf_eq_one x
  have hKchar : K.Characteristic := by
    apply Subgroup.characteristic_iff_comap_le.mpr
    intro e y hy
    change (e y) ^ p = 1 at hy
    change y ^ p = 1
    apply e.injective
    simpa only [map_pow, map_one] using hy
  let : K.Characteristic := hKchar
  let N : Subgroup G := K.map M.subtype
  have hNnormal : N.Normal := by
    dsimp only [N]
    let : M.Normal := hMn
    infer_instance
  have hNne : N ≠ ⊥ := by
    intro hNbot
    have hxN : (x : G) ∈ N := ⟨x, hxK, rfl⟩
    have hxone : (x : G) = 1 := Subgroup.mem_bot.mp (hNbot ▸ hxN)
    exact hxne (Subtype.ext hxone)
  have hNle : N ≤ M := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hNM : N = M := hmin N hNnormal hNne hNle
  have hexponent : ∀ y : M, y ^ p = 1 := by
    intro y
    have hyN : (y : G) ∈ N := by
      rw [hNM]
      exact y.2
    obtain ⟨z, hzK, hzy⟩ := hyN
    have hzy' : z = y := Subtype.ext hzy
    subst z
    exact hzK
  have hMp : IsPGroup p M := fun y ↦ ⟨1, by simpa using hexponent y⟩
  obtain ⟨a, hcard⟩ := IsPGroup.iff_card.mp hMp
  have ha : 0 < a := by
    by_contra ha
    have : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    exact hMcard_ne_one (by simpa using hcard)
  exact ⟨p, a, hp, ha, hcard, hcomm, hexponent⟩

/-- **A minimal normal section is elementary abelian.**  Let `N < V` be normal
subgroups of a finite solvable group with no normal subgroup strictly between
them.  Then `V/N` is minimal normal in `G/N`, so for some prime `q` every
`v ∈ V` has `v^q ∈ N`, and `V` commutes modulo `N`. -/
theorem exists_prime_of_minimal_normal_section {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable G] {N V : Subgroup G} [N.Normal] (hVn : V.Normal) (hNV : N < V)
    (hmin : ∀ V' : Subgroup G, V'.Normal → N < V' → V' ≤ V → V' = V) :
    ∃ q, q.Prime ∧ (∀ v ∈ V, v ^ q ∈ N) ∧
      ∀ v ∈ V, ∀ w ∈ V, (v : G ⧸ N) * w = w * v := by
  -- `V/N` is minimal normal in `G/N`
  set A₀ := V.map (QuotientGroup.mk' N) with hA₀
  have hA₀n : A₀.Normal := Subgroup.Normal.map hVn _ (QuotientGroup.mk'_surjective N)
  have hA₀ne : A₀ ≠ ⊥ := by
    rw [hA₀, Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact fun h ↦ hNV.not_ge h
  have hA₀min : ∀ N' : Subgroup (G ⧸ N), N'.Normal → N' ≠ ⊥ → N' ≤ A₀ → N' = A₀ := by
    intro N' hN'n hN'ne hN'le
    set V' := N'.comap (QuotientGroup.mk' N) with hV'
    have hV'n : V'.Normal := Subgroup.Normal.comap hN'n _
    have hNV' : N ≤ V' := by
      intro n hn
      rw [hV', Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
      exact N'.one_mem
    have hV'V : V' ≤ V := by
      calc V' ≤ A₀.comap (QuotientGroup.mk' N) := Subgroup.comap_mono hN'le
        _ = V ⊔ N := by rw [hA₀, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
        _ = V := sup_eq_left.mpr hNV.le
    have hNV'ne : N ≠ V' := by
      intro h
      apply hN'ne
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) N',
        ← hV', ← h, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hVV' : V' = V := hmin V' hV'n (lt_of_le_of_ne hNV' hNV'ne) hV'V
    rw [hA₀, ← hVV', hV',
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]
  obtain ⟨q, a, hq, -, -, hcomm, hexp⟩ := minimal_normal_is_elementary_abelian hA₀n hA₀ne hA₀min
  have hmkV : ∀ v ∈ V, ((v : G ⧸ N)) ∈ A₀ := fun v hv ↦ Subgroup.mem_map_of_mem _ hv
  refine ⟨q, hq, fun v hv ↦ ?_, fun v hv w hw ↦ ?_⟩
  · have h := congrArg Subtype.val (hexp ⟨_, hmkV v hv⟩)
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    rw [← QuotientGroup.mk_pow] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  · exact congrArg Subtype.val (hcomm.is_comm.comm ⟨_, hmkV v hv⟩ ⟨_, hmkV w hw⟩)

end Erdos274
