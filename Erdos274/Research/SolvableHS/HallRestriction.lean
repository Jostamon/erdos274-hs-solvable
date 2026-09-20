/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.ExactCovering.Counting.Volume
import Erdos274.Research.SolvableHS.OrbitUnionBound

/-!
# Solvable HS: Lemma H (Hall restriction)

`SOLVABLE_HS_TRACK.md` §9.1.  Let `K ≤ G` be a `p`-complement (in a solvable
group one exists, by Hall).  Restricting an exact covering of `G` to a left
coset `x K` gives an exact covering of `K` in which

* every `p`-free part (`p ∤ [G : Xⱼ]`) survives **with its original index**;
* a `p`-divisible part contributes its `p′`-index `[K : K ⊓ Xᵢ]`.

The restriction itself is already in the repo: `Group.ExactCovering.fiberCover`
(`ExactCovering/Fibers.lean`) intersects a covering with a coset of any
subgroup, and `fiberCover_sum_inv_index` is the mass identity.  What this file
adds is the arithmetic that makes it Lemma H.

* `relIndex_eq_index_of_hall`: the index identity, in its natural
  Hall-subgroup generality — if `gcd(|K|, [G:K]) = 1` and `[G:K] ∣ |X|`, then
  `[K : K ⊓ X] = [G : X]`.  `relIndex_eq_index_of_pComplement` is the
  `p`-complement form used in §9.1: `K` a `p′`-group of `p`-power index and
  `p ∤ [G:X]`.
* `orbit_eq_univ_of_relIndex_eq_index`, `exists_mem_coset`,
  `coset_inter_nonempty`: `K X = G`, i.e. every left coset of `X` meets every
  left coset of `K`.  Proved through the `K`-orbit of the trivial coset in
  `G ⧸ X`, whose size is `[K : K ⊓ X]` (`ncard_orbit_subgroup`).
* `fiberPart_index`: the parts of the restricted covering have index
  `[K : K ⊓ Xᵢ]`.
* `mem_fiberIndex_of_relIndex_eq_index`: a `p`-free part is active in **every**
  coset — the coset-independent `J`-anchor of §9.1.
* `hall_restriction_mass`: Lemma H (3),
  `Σ_{i active, i ∉ J} 1/mᵢ = 1 − Σ_{j ∈ J} 1/nⱼ`, for any set `J` of parts
  whose relative index equals their index.

No research axiom occurs in this file.
-/

universe u v

namespace Erdos274

namespace HallRestriction

open MulAction Finset
open scoped Pointwise

variable {G : Type u} [Group G]

section Index

/-- **Lemma H (1)**, arithmetic core, in Hall generality.  If `|K|` is coprime
to `[G:K]` and `[G:K] ∣ |X|`, then `[K : K ⊓ X] = [G : X]`. -/
theorem relIndex_eq_index_of_hall [Finite G] {K X : Subgroup G}
    (hcop : Nat.Coprime (Nat.card K) K.index) (hdvd : K.index ∣ Nat.card X) :
    X.relIndex K = X.index := by
  have hk0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hm0 : K.index ≠ 0 := K.index_ne_zero_of_finite
  have ha0 : 0 < Nat.card (X.subgroupOf K) := Nat.card_pos
  -- `a = |K ⊓ X|` divides both `|K|` and `|X|`
  have hak : Nat.card (X.subgroupOf K) ∣ Nat.card K :=
    Subgroup.card_subgroup_dvd_card (X.subgroupOf K)
  have hcard : Nat.card (X.subgroupOf K) = Nat.card (X ⊓ K : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv
  have hax : Nat.card (X.subgroupOf K) ∣ Nat.card X := by
    rw [hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  -- the two Lagrange identities
  have hrel : X.relIndex K * Nat.card (X.subgroupOf K) = Nat.card K :=
    Subgroup.index_mul_card (X.subgroupOf K)
  have hgk : K.index * Nat.card K = Nat.card G := Subgroup.index_mul_card K
  have hgx : X.index * Nat.card X = Nat.card G := Subgroup.index_mul_card X
  -- split off the `p`-part of `|X|`
  obtain ⟨x', hx'⟩ := hdvd
  have hx'k : X.index * x' = Nat.card K := by
    have h1 : K.index * (X.index * x') = K.index * Nat.card K := by
      rw [hgk, ← hgx, hx']; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) h1
  have hx'0 : x' ≠ 0 := by
    rintro rfl
    simp only [Nat.mul_zero] at hx'k
    exact hk0 hx'k.symm
  -- `a ∣ x'`, since `a` is coprime to the index of `K`
  have hax' : Nat.card (X.subgroupOf K) ∣ x' := by
    have hcop_am : Nat.Coprime (Nat.card (X.subgroupOf K)) K.index :=
      Nat.Coprime.coprime_dvd_left hak hcop
    have h2 : Nat.card (X.subgroupOf K) ∣ K.index * x' := by
      rw [← hx']
      exact hax
    exact hcop_am.dvd_of_dvd_mul_left h2
  have hale : Nat.card (X.subgroupOf K) ≤ x' := Nat.le_of_dvd (Nat.pos_of_ne_zero hx'0) hax'
  -- the injection `K ⧸ (K ⊓ X) ↪ G ⧸ X`
  have hle : X.relIndex K ≤ X.index := by
    have hne : X.relIndex ⊤ ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      exact X.index_ne_zero_of_finite
    have h := Subgroup.relIndex_le_of_le_right (le_top : K ≤ ⊤) hne
    rwa [Subgroup.relIndex_top_right] at h
  refine Nat.eq_of_mul_eq_mul_right ha0 (Nat.le_antisymm ?_ ?_)
  · exact Nat.mul_le_mul_right _ hle
  · calc X.index * Nat.card (X.subgroupOf K)
        ≤ X.index * x' := Nat.mul_le_mul_left _ hale
      _ = Nat.card K := hx'k
      _ = X.relIndex K * Nat.card (X.subgroupOf K) := hrel.symm

/-- **Lemma H (1)** for a `p`-complement: if `K` is a `p′`-group of `p`-power
index and `p ∤ [G:X]`, then `[K : K ⊓ X] = [G : X]`. -/
theorem relIndex_eq_index_of_pComplement [Finite G] {p n : ℕ} (hp : p.Prime)
    {K X : Subgroup G} (hK : ¬ p ∣ Nat.card K) (hKi : K.index = p ^ n)
    (hX : ¬ p ∣ X.index) : X.relIndex K = X.index := by
  have hcop : Nat.Coprime (Nat.card K) K.index := by
    rw [hKi]
    exact Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hK).symm
  refine relIndex_eq_index_of_hall hcop ?_
  have hgx : X.index * Nat.card X = Nat.card G := Subgroup.index_mul_card X
  have hgk : K.index * Nat.card K = Nat.card G := Subgroup.index_mul_card K
  have hdvd : K.index ∣ X.index * Nat.card X := by
    rw [hgx, ← hgk]
    exact Dvd.intro _ rfl
  rw [hKi] at hdvd ⊢
  refine (Nat.Coprime.dvd_of_dvd_mul_left ?_ hdvd)
  exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hX)

end Index

section Cosets

variable [Finite G]

/-- If `[K : K ⊓ X] = [G : X]`, the `K`-orbit of the trivial coset is all of
`G ⧸ X`: this is `K X = G`. -/
theorem orbit_eq_univ_of_relIndex_eq_index {K X : Subgroup G}
    (h : X.relIndex K = X.index) :
    orbit K ((1 : G) : G ⧸ X) = Set.univ := by
  have h1 : (orbit K ((1 : G) : G ⧸ X)).ncard = X.index := by
    rw [ncard_orbit_subgroup, stabilizer_quotient, h]
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
  have h2 : (Set.univ : Set (G ⧸ X)).ncard = (orbit K ((1 : G) : G ⧸ X)).ncard := by
    rw [Set.ncard_univ, h1, Subgroup.index_eq_card]
  exact h2.le

/-- Every left coset of `X` meets `K`. -/
theorem exists_mem_coset {K X : Subgroup G} (h : X.relIndex K = X.index) (g : G) :
    ∃ y : G, y ∈ K ∧ y ∈ g • (X : Set G) := by
  have hmem : ((g : G) : G ⧸ X) ∈ orbit K ((1 : G) : G ⧸ X) := by
    rw [orbit_eq_univ_of_relIndex_eq_index h]
    exact Set.mem_univ _
  obtain ⟨k, hk⟩ := hmem
  refine ⟨(k : G), k.2, ?_⟩
  rw [mem_leftCoset_iff]
  refine QuotientGroup.eq.mp ?_
  have : ((k : G) : G ⧸ X) = ((g : G) : G ⧸ X) := by
    simpa [Subgroup.smul_def] using hk
  exact this.symm

/-- **Lemma H (1)**, coset form: every left coset of `X` meets every left coset
of `K`. -/
theorem coset_inter_nonempty {K X : Subgroup G} (h : X.relIndex K = X.index) (a b : G) :
    ((a • (X : Set G)) ∩ (b • (K : Set G))).Nonempty := by
  obtain ⟨y, hyK, hyX⟩ := exists_mem_coset h (b⁻¹ * a)
  refine ⟨b * y, ?_, ?_⟩
  · rw [mem_leftCoset_iff] at hyX ⊢
    have : (b⁻¹ * a)⁻¹ * y ∈ X := hyX
    simpa [mul_assoc] using this
  · rw [mem_leftCoset_iff]
    simpa using hyK

end Cosets

section Restriction

variable {ι : Type v} [Fintype ι]

/-- The parts of the restricted covering have the relative index
`mᵢ = [K : K ⊓ Xᵢ]`. -/
theorem fiberPart_index (P : Group.ExactCovering G ι) (K : Subgroup G) {x : G}
    (i : P.FiberIndex K x) :
    (P.fiberPart (x := x) K i).index = (P.parts i.1).relIndex K := rfl

/-- **Lemma H (2)**, the `J`-anchor: a part whose relative index equals its
index is active in *every* coset of `K`. -/
theorem mem_fiberIndex_of_relIndex_eq_index [Finite G] (P : Group.ExactCovering G ι)
    {K : Subgroup G} {j : ι} (h : (P.parts j).relIndex K = (P.parts j).index) (x : G) :
    ((P.reps j • (P.parts j : Set G)) ∩ (x • (K : Set G))).Nonempty :=
  coset_inter_nonempty h _ _

open Classical in
/-- **Lemma H (3)**: the mass identity for the restriction of an exact covering
to a coset of `K`.  The parts in `J` — in the application, the `p`-free ones,
by `relIndex_eq_index_of_pComplement` — keep their original index and are
present in every coset, so the remaining (`p`-divisible) parts carry the
complementary mass `1 − Σ_J 1/nⱼ`, independently of the coset. -/
theorem hall_restriction_mass [Finite G] (P : Group.ExactCovering G ι)
    (K : Subgroup G) (x : G) (J : Finset ι)
    (hJ : ∀ j ∈ J, (P.parts j).relIndex K = (P.parts j).index) :
    ∑ i ∈ (Finset.univ.filter fun i ↦
        ((P.reps i • (P.parts i : Set G)) ∩ (x • (K : Set G))).Nonempty) \ J,
          ((P.parts i).relIndex K : ℚ)⁻¹
      = 1 - ∑ j ∈ J, ((P.parts j).index : ℚ)⁻¹ := by
  classical
  set p : ι → Prop := fun i ↦
    ((P.reps i • (P.parts i : Set G)) ∩ (x • (K : Set G))).Nonempty with hp
  have hactive : ∑ i ∈ Finset.univ.filter p, ((P.parts i).relIndex K : ℚ)⁻¹ = 1 := by
    have hmem : ∀ i : ι, i ∈ Finset.univ.filter p ↔ p i := fun i ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsub : ∑ i ∈ Finset.univ.filter p, ((P.parts i).relIndex K : ℚ)⁻¹
        = ∑ i : P.FiberIndex K x, ((P.parts i.1).relIndex K : ℚ)⁻¹ :=
      Finset.sum_subtype _ hmem _
    rw [hsub, ← fiberCover_sum_inv_index P K x]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [fiberPart_index]
  have hJsub : J ⊆ Finset.univ.filter p := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      mem_fiberIndex_of_relIndex_eq_index P (hJ j hj) x⟩
  have hsplit := Finset.sum_sdiff (f := fun i ↦ ((P.parts i).relIndex K : ℚ)⁻¹) hJsub
  have hJsum : ∑ j ∈ J, ((P.parts j).relIndex K : ℚ)⁻¹
      = ∑ j ∈ J, ((P.parts j).index : ℚ)⁻¹ :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hJ j hj]
  rw [hactive] at hsplit
  rw [← hsplit, hJsum]
  ring

end Restriction

end HallRestriction

end Erdos274
