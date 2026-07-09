/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Mathlib

/-!
# Primary parts of a finite abelian group

For a finite abelian group `G` with `|G| = s * t`, `s` and `t` coprime, the
`s`-torsion subgroup `ker (·^s)` has cardinality exactly `s`.  This file
proves that and collects the coset-counting lemmas used in the proof of the
Herzog–Schönheim conjecture for finite abelian groups
(see `docs/erdos274/BLUEPRINT.md`).

## Main results

* `Erdos274.card_ker_powMonoidHom`: `|ker (·^s)| = s` when `|G| = s*t`, `(s,t)=1`.
* `Erdos274.inf_ker_powMonoidHom_eq_bot`: the `s`- and `t`-torsion intersect
  trivially.
* `Erdos274.card_inf_mul_card_map`: `|H ⊓ K| * |π_K(H)| = |H|` for the
  quotient map `π_K : G → G ⧸ K`.
* `Erdos274.smul_set_inter_smul_set_eq`: two intersecting cosets intersect in
  a coset of the intersection subgroup.
* `Erdos274.ncard_eq_sum_fiber_ncard`: counting a set fiberwise over `G ⧸ K`.
-/

namespace Erdos274

open scoped Pointwise

variable {G : Type*} [CommGroup G] [Finite G]

omit [Finite G] in
/-- Elements of the kernel of `·^s` have order dividing `s`. -/
lemma orderOf_dvd_of_mem_ker_powMonoidHom {s : ℕ} {g : G}
    (hg : g ∈ (powMonoidHom s : G →* G).ker) : orderOf g ∣ s :=
  orderOf_dvd_of_pow_eq_one hg

/-- If the order of every element of a subgroup `K` of a finite group is
coprime to `t`, then `|K|` is coprime to `t`. -/
private lemma coprime_card_of_forall_orderOf {K : Subgroup G} {t : ℕ}
    (h : ∀ g ∈ K, (orderOf g).Coprime t) : (Nat.card K).Coprime t := by
  by_contra hcon
  obtain ⟨r, hr, hrK, hrt⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype K := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := K) r
    (by rwa [← Nat.card_eq_fintype_card])
  have hxG : orderOf (x : G) = r := by
    rw [← hx]
    exact Subgroup.orderOf_coe x
  have hxco : Nat.gcd r t = 1 := hxG ▸ h x x.2
  exact hr.ne_one (Nat.dvd_one.mp (hxco ▸ Nat.dvd_gcd dvd_rfl hrt))

/-- In a finite abelian group of cardinality `s * t` with `s, t` coprime, the
`s`-torsion subgroup has cardinality exactly `s`. -/
theorem card_ker_powMonoidHom {s t : ℕ} (hst : s * t = Nat.card G)
    (hco : s.Coprime t) : Nat.card ((powMonoidHom s : G →* G).ker) = s := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have hs : 0 < s := Nat.pos_of_ne_zero fun h ↦ by simp [h, ← hst] at hG
  have ht : 0 < t := Nat.pos_of_ne_zero fun h ↦ by simp [h, ← hst] at hG
  set f : G →* G := powMonoidHom s with hf
  -- `|ker f|` divides `s`: it is coprime to `t` and divides `s * t`.
  have hKco : (Nat.card f.ker).Coprime t :=
    coprime_card_of_forall_orderOf fun g hg ↦
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_mem_ker_powMonoidHom hg) hco
  have hKdvd : Nat.card f.ker ∣ s :=
    hKco.dvd_of_dvd_mul_right (hst ▸ Subgroup.card_subgroup_dvd_card f.ker)
  -- `|range f|` divides `t`: elements `g^s` are killed by `t`.
  have hrco : (Nat.card f.range).Coprime s := by
    refine coprime_card_of_forall_orderOf fun g hg ↦ ?_
    obtain ⟨x, rfl⟩ := hg
    have hord : orderOf (f x) ∣ t := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hf, powMonoidHom_apply, ← pow_mul, hst]
      exact pow_card_eq_one'
    exact Nat.Coprime.coprime_dvd_left hord hco.symm
  have hrdvd : Nat.card f.range ∣ t := by
    refine hrco.dvd_of_dvd_mul_left ?_
    rw [hst]
    exact Subgroup.card_subgroup_dvd_card f.range
  -- Squeeze: `s * t = |range f| * |ker f|` with `|ker f| ≤ s`, `|range f| ≤ t`.
  have hcard : Nat.card f.range * Nat.card f.ker = s * t := by
    rw [hst, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h1 : Nat.card f.ker ≤ s := Nat.le_of_dvd hs hKdvd
  have h2 : Nat.card f.range ≤ t := Nat.le_of_dvd ht hrdvd
  rcases h1.lt_or_eq with h | h
  · exfalso
    have h3 : s * t < s * t := by
      calc s * t = Nat.card f.range * Nat.card f.ker := hcard.symm
        _ ≤ t * Nat.card f.ker := Nat.mul_le_mul_right _ h2
        _ < t * s := mul_lt_mul_of_pos_left h ht
        _ = s * t := mul_comm t s
    exact absurd h3 (lt_irrefl _)
  · exact h

/-- In a finite abelian group of cardinality `s * t` with `s, t` coprime, the
quotient by the `s`-torsion subgroup has cardinality exactly `t`. -/
theorem card_quotient_ker_powMonoidHom {s t : ℕ} (hst : s * t = Nat.card G)
    (hco : s.Coprime t) :
    Nat.card (G ⧸ (powMonoidHom s : G →* G).ker) = t := by
  have hG : 0 < Nat.card G := Nat.card_pos
  have hs : 0 < s := Nat.pos_of_ne_zero fun h ↦ by simp [h, ← hst] at hG
  have h1 : Nat.card G =
      Nat.card (G ⧸ (powMonoidHom s : G →* G).ker) *
        Nat.card ((powMonoidHom s : G →* G).ker) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [card_ker_powMonoidHom hst hco, ← hst, mul_comm s t] at h1
  exact Nat.eq_of_mul_eq_mul_right hs h1.symm

omit [Finite G] in
/-- The `s`- and `t`-torsion subgroups intersect trivially when `s, t` are
coprime. -/
theorem inf_ker_powMonoidHom_eq_bot {s t : ℕ} (hco : s.Coprime t) :
    (powMonoidHom s : G →* G).ker ⊓ (powMonoidHom t : G →* G).ker = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgs, hgt⟩ := Subgroup.mem_inf.mp hg
  have h1 : orderOf g ∣ Nat.gcd s t :=
    Nat.dvd_gcd (orderOf_dvd_of_mem_ker_powMonoidHom hgs)
      (orderOf_dvd_of_mem_ker_powMonoidHom hgt)
  rw [hco] at h1
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))

omit [Finite G] in
/-- For subgroups `H, K` of an abelian group, `|H ⊓ K| * |π_K(H)| = |H|`,
where `π_K : G → G ⧸ K` is the quotient map. -/
theorem card_inf_mul_card_map (H K : Subgroup G) :
    Nat.card (H ⊓ K : Subgroup G) * Nat.card (H.map (QuotientGroup.mk' K)) =
      Nat.card H := by
  set f := (QuotientGroup.mk' K).comp H.subtype with hf
  have hker : f.ker = (H ⊓ K).subgroupOf H := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      Subgroup.inf_subgroupOf_left K H]
    rfl
  have hrange : f.range = H.map (QuotientGroup.mk' K) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : Nat.card H =
      Nat.card (↥H ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange,
    hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    at h1
  rw [mul_comm]
  exact h1.symm

omit [Finite G] in
/-- A coset containing `y` equals the `y`-translate of the subgroup. -/
lemma smul_set_eq_of_mem {a y : G} {L : Subgroup G}
    (hy : y ∈ a • (L : Set G)) : a • (L : Set G) = y • (L : Set G) :=
  (leftCoset_eq_iff L).mpr ((mem_leftCoset_iff a).mp hy)

omit [Finite G] in
/-- Two intersecting cosets intersect in a coset of the intersection. -/
theorem smul_set_inter_smul_set_eq {H K : Subgroup G} {g k x : G}
    (hx : x ∈ g • (H : Set G) ∩ k • (K : Set G)) :
    g • (H : Set G) ∩ k • (K : Set G) = x • ((H ⊓ K : Subgroup G) : Set G) := by
  obtain ⟨hxH, hxK⟩ := hx
  rw [smul_set_eq_of_mem hxH, smul_set_eq_of_mem hxK, ← Set.smul_set_inter,
    ← Subgroup.coe_inf]

omit [Finite G] in
/-- A left coset has the cardinality of the subgroup. -/
lemma ncard_smul_coset (x : G) (H : Subgroup G) :
    (x • (H : Set G)).ncard = Nat.card H := by
  rw [Set.ncard_smul_set, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]

/-- Counting a set fiberwise over the quotient `G ⧸ K`. -/
lemma ncard_eq_sum_fiber_ncard (S : Set G) (K : Subgroup G) [Fintype (G ⧸ K)] :
    S.ncard = ∑ c : G ⧸ K, (S ∩ QuotientGroup.mk ⁻¹' {c}).ncard := by
  classical
  haveI : Fintype G := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise
      (f := fun x ↦ (QuotientGroup.mk x : G ⧸ K)) (t := Finset.univ)
      (fun x _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

section CosetHelpers

omit [Finite G] in
/-- If `L ⊓ P = ⊥`, the quotient map `G → G ⧸ P` embeds `L`. -/
lemma card_map_mk'_of_inf_eq_bot {L P : Subgroup G} (h : L ⊓ P = ⊥) :
    Nat.card (L.map (QuotientGroup.mk' P)) = Nat.card L := by
  have h1 := card_inf_mul_card_map L P
  rw [h] at h1
  simpa using h1

omit [Finite G] in
/-- If `P ⊓ Q = ⊥`, the quotient map `G → G ⧸ P` is injective on any coset
of `Q`. -/
lemma injOn_mk_smul_coset_of_inf_eq_bot {P Q : Subgroup G} (hPQ : P ⊓ Q = ⊥)
    (z : G) :
    Set.InjOn (QuotientGroup.mk : G → G ⧸ P) (z • (Q : Set G)) := by
  rintro u hu v hv huv
  obtain ⟨qu, hqu, rfl⟩ := hu
  obtain ⟨qv, hqv, rfl⟩ := hv
  have h1 : (z * qu)⁻¹ * (z * qv) ∈ P := (QuotientGroup.eq).mp huv
  have h2 : (z * qu)⁻¹ * (z * qv) ∈ Q := by
    have : (z * qu)⁻¹ * (z * qv) = qu⁻¹ * qv := by group
    rw [this]
    exact Q.mul_mem (Q.inv_mem hqu) hqv
  have h3 : (z * qu)⁻¹ * (z * qv) = 1 := by
    have := hPQ ▸ Subgroup.mem_inf.mpr ⟨h1, h2⟩
    simpa using this
  have h4 : qu = qv := by
    have h5 : (z * qu)⁻¹ * (z * qv) = qu⁻¹ * qv := by group
    rw [h5] at h3
    exact inv_mul_eq_one.mp h3
  simp [h4]

omit [Finite G] in
/-- The fiber of the quotient map over `mk z` is the coset `z • Q`. -/
lemma preimage_mk_singleton_eq (Q : Subgroup G) (z : G) :
    (QuotientGroup.mk ⁻¹' {(z : G ⧸ Q)} : Set G) = z • (Q : Set G) := by
  change {x : G | (x : G ⧸ Q) = (z : G ⧸ Q)} = z • (Q : Set G)
  exact QuotientGroup.eq_class_eq_leftCoset Q z

section
variable {G' : Type*} [CommGroup G']

omit [Finite G] in
/-- A monoid hom maps a coset onto a coset of the image subgroup. -/
lemma image_smul_coset (f : G →* G') (x : G) (L : Subgroup G) :
    f '' (x • (L : Set G)) = f x • ((L.map f : Subgroup G') : Set G') := by
  rw [Set.image_smul_distrib, Subgroup.coe_map]

end

omit [Finite G] in
/-- A `Finset.biUnion` over the subtype of a finset equals the plain
`biUnion`. -/
lemma biUnion_subtype_univ {κ : Type*} (J : Finset κ)
    (f : κ → Finset ℕ) [Fintype J] :
    (Finset.univ : Finset J).biUnion (fun j ↦ f j) = J.biUnion f := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Subtype.exists,
    exists_prop]

/-- The image in `G ⧸ K` of a coset of `L` has `|L.map (mk' K)|` elements. -/
lemma ncard_image_mk_smul_coset (K : Subgroup G) (x : G) (L : Subgroup G) :
    ((QuotientGroup.mk '' (x • (L : Set G))) : Set (G ⧸ K)).ncard =
      Nat.card (L.map (QuotientGroup.mk' K)) := by
  rw [show (QuotientGroup.mk : G → G ⧸ K) = (QuotientGroup.mk' K : G →* G ⧸ K)
      from rfl,
    image_smul_coset (QuotientGroup.mk' K) x L, ncard_smul_coset]

/-- A set saturated for the quotient by `P` (closed under the `P`-fibers of
its elements) has cardinality `|P|` times the cardinality of its image. -/
lemma ncard_eq_card_mul_ncard_image {P : Subgroup G} {S : Set G}
    [Fintype (G ⧸ P)]
    (hsat : ∀ x ∈ S, ∀ y : G,
      (QuotientGroup.mk y : G ⧸ P) = QuotientGroup.mk x → y ∈ S) :
    S.ncard = Nat.card P * (QuotientGroup.mk '' S : Set (G ⧸ P)).ncard := by
  classical
  rw [ncard_eq_sum_fiber_ncard S P]
  have hterm : ∀ c : G ⧸ P, (S ∩ QuotientGroup.mk ⁻¹' {c}).ncard =
      if c ∈ QuotientGroup.mk '' S then Nat.card P else 0 := by
    intro c
    by_cases hc : c ∈ QuotientGroup.mk '' S
    · rw [if_pos hc]
      obtain ⟨x, hxS, hxc⟩ := hc
      have hfib_sub : (QuotientGroup.mk ⁻¹' {c} : Set G) ⊆ S := by
        intro y hy
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
        exact hsat x hxS y (by rw [hy, ← hxc])
      rw [Set.inter_eq_self_of_subset_right hfib_sub]
      obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective c
      rw [← hz, preimage_mk_singleton_eq, ncard_smul_coset]
    · rw [if_neg hc]
      have hempty : S ∩ QuotientGroup.mk ⁻¹' {c} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨hyS, hyc⟩
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hyc
        exact hc ⟨y, hyS, hyc⟩
      rw [hempty, Set.ncard_empty]
  rw [Finset.sum_congr rfl (fun c _ ↦ hterm c), Finset.sum_ite,
    Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
  congr 1
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext c
  simp

end CosetHelpers

end Erdos274
