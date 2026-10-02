/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.KnownCases.Solvable.SevenJoin
public import Erdos274.KnownCases.Solvable.HallRestriction


/-!
# Coprime cells meet: the 7-chamber and the separation of exact fibres

`DECISION_LOG` D98 §§9, 13.  Inside one `F`-coset `δ`, the cell of part `j`
is a left coset of `Hⱼ ⊓ F`, a subgroup of index `ℓⱼ` in `F`.

* `exists_mul_of_coprime`: if `Y₁, Y₂ ≤ F` have coprime indices in `F`, then
  `F = Y₁Y₂`.  The indices force `[Y₁ : Y₁ ⊓ Y₂] = [F : Y₂]`, and then the
  `Y₁`-orbit of `Y₂` in `F/Y₂` is everything (`HallRestriction.exists_mem_coset`,
  applied inside `F`).
* `eq_of_meet_of_coprime`: **two parts with coprime local indices never
  share an `F`-coset**, since their cells in it would meet.  This is
  Margolis–Schnabel Lemma 2.2 inside a fibre.

Consequences for `SevenJoin.false_of_covering`:
* `sep_of_coprime`: exact-7 and exact-8 parts share no `F`-coset (`hsep`),
  because `7` and `2^{ord₇ 2}` are coprime.
* `seven_dvd_of_meet`, **the 7-chamber lemma**: a part sharing an `F`-coset
  with an exact-7 part has `7 ∣ ℓ`.
* `two_dvd_of_meet`: a part sharing an `F`-coset with an exact-8 part has
  `2 ∣ ℓ`.  The stronger exact-8 chamber (`2^{ord₇ 2} ∣ ℓ` or `7 ∣ ℓ`) is
  proved using the `AGL(1,8)` structure in `ExactEight`.

`false_of_covering_chamber` is `false_of_covering` with `hsep` and the
exact-7 half of `hch` discharged.  What is left is (CB) and the exact-8
chamber, stated with the `2 ∣ ℓ` this file already provides.
-/

@[expose] public section

namespace Erdos274

namespace Chamber

open QuotientShadow SevenJoin
open scoped Pointwise

universe u v

section Coprime

variable {G : Type u} [Group G] [Finite G]

/-- Coprime indices force `[Y₁ : Y₁ ⊓ Y₂] = [F : Y₂]`. -/
theorem relIndex_eq_of_coprime {Y₁ Y₂ F : Subgroup G} (h₁ : Y₁ ≤ F) (h₂ : Y₂ ≤ F)
    (hcop : Nat.Coprime (Y₁.relIndex F) (Y₂.relIndex F)) :
    Y₂.relIndex Y₁ = Y₂.relIndex F := by
  have hA : Y₂.relIndex Y₁ * Y₁.relIndex F = (Y₂ ⊓ Y₁).relIndex F := by
    rw [← Subgroup.inf_relIndex_right Y₂ Y₁,
      Subgroup.relIndex_mul_relIndex (Y₂ ⊓ Y₁) Y₁ F inf_le_right h₁]
  have hB : Y₁.relIndex Y₂ * Y₂.relIndex F = (Y₂ ⊓ Y₁).relIndex F := by
    rw [inf_comm, ← Subgroup.inf_relIndex_right Y₁ Y₂,
      Subgroup.relIndex_mul_relIndex (Y₁ ⊓ Y₂) Y₂ F inf_le_right h₂]
  have hdvd : Y₂.relIndex F ∣ Y₂.relIndex Y₁ := by
    have h : Y₂.relIndex F ∣ Y₂.relIndex Y₁ * Y₁.relIndex F := hA ▸ Dvd.intro_left _ hB
    exact hcop.symm.dvd_of_dvd_mul_right h
  have hle : Y₂.relIndex Y₁ ≤ Y₂.relIndex F :=
    Subgroup.relIndex_le_of_le_right h₁ (Y₂.subgroupOf F).index_ne_zero_of_finite
  have hpos : 0 < Y₂.relIndex Y₁ := Nat.pos_of_ne_zero (Y₂.subgroupOf Y₁).index_ne_zero_of_finite
  exact le_antisymm hle (Nat.le_of_dvd hpos hdvd)

/-- **`F = Y₁Y₂` for coprime indices.** -/
theorem exists_mul_of_coprime {Y₁ Y₂ F : Subgroup G} (h₁ : Y₁ ≤ F) (h₂ : Y₂ ≤ F)
    (hcop : Nat.Coprime (Y₁.relIndex F) (Y₂.relIndex F)) {f : G} (hf : f ∈ F) :
    ∃ a ∈ Y₁, ∃ b ∈ Y₂, f = a * b := by
  have hX : (Y₂.subgroupOf F).relIndex (Y₁.subgroupOf F) = (Y₂.subgroupOf F).index := by
    rw [Subgroup.relIndex_subgroupOf h₁]
    exact relIndex_eq_of_coprime h₁ h₂ hcop
  obtain ⟨y, hyK, hyX⟩ := HallRestriction.exists_mem_coset hX (⟨f, hf⟩ : F)
  rw [mem_leftCoset_iff] at hyX
  have h2 : ((⟨f, hf⟩ : F)⁻¹ * y : F) ∈ Y₂.subgroupOf F := hyX
  rw [Subgroup.mem_subgroupOf] at h2
  refine ⟨y, Subgroup.mem_subgroupOf.mp hyK, (y : G)⁻¹ * f, ?_, by group⟩
  simpa using Y₂.inv_mem h2

end Coprime

section Cells

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

/-- **Parts whose subgroups multiply out to `F` share no `F`-coset**: their
cells in it would meet. -/
theorem eq_of_meet_of_mul {j k : κ} {δ : G ⧸ F} (hδj : δ ∈ shadow C F j)
    (hδk : δ ∈ shadow C F k)
    (hmul : ∀ f ∈ F, ∃ a ∈ C.parts j ⊓ F, ∃ b ∈ C.parts k ⊓ F, f = a * b) : j = k := by
  obtain ⟨x₀, hx₀⟩ : (NormaliserSlice.piece C F j δ).Nonempty := hδj
  obtain ⟨y₀, hy₀⟩ : (NormaliserSlice.piece C F k δ).Nonempty := hδk
  have hf : x₀⁻¹ * y₀ ∈ F := by
    have hx := ((NormaliserSlice.mem_piece C F).mp hx₀).2
    have hy := ((NormaliserSlice.mem_piece C F).mp hy₀).2
    exact QuotientGroup.eq.mp (hx.trans hy.symm)
  obtain ⟨a, ha, b, hb, hab⟩ := hmul _ hf
  have hz : x₀ * a = y₀ * b⁻¹ := by
    calc x₀ * a = x₀ * (x₀⁻¹ * y₀) * b⁻¹ := by rw [hab]; group
      _ = y₀ * b⁻¹ := by group
  have hzj : x₀ * a ∈ NormaliserSlice.piece C F j δ :=
    (NormaliserSlice.mem_piece_iff_of_mem C F hx₀).mpr (by simpa using ha)
  have hzk : x₀ * a ∈ NormaliserSlice.piece C F k δ := by
    rw [hz]
    exact (NormaliserSlice.mem_piece_iff_of_mem C F hy₀).mpr
      (by simpa using (C.parts k ⊓ F).inv_mem hb)
  exact NormaliserSlice.eq_of_mem_cell C ((NormaliserSlice.mem_piece C F).mp hzj).1
    ((NormaliserSlice.mem_piece C F).mp hzk).1

/-- **Parts with coprime local indices share no `F`-coset.** -/
theorem eq_of_meet_of_coprime {j k : κ} {δ : G ⧸ F} (hδj : δ ∈ shadow C F j)
    (hδk : δ ∈ shadow C F k) (hcop : Nat.Coprime (loc C F j) (loc C F k)) : j = k := by
  have hcop' : Nat.Coprime ((C.parts j ⊓ F).relIndex F) ((C.parts k ⊓ F).relIndex F) := by
    rwa [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right]
  exact eq_of_meet_of_mul C F hδj hδk fun f hf ↦
    exists_mul_of_coprime inf_le_right inf_le_right hcop' hf

/-- A part sharing an `F`-coset with a part of prime local index `p` has
`p ∣ ℓ`. -/
theorem dvd_of_meet_of_prime {j k : κ} {δ : G ⧸ F} {p : ℕ} (hp : p.Prime)
    (hj : loc C F j = p) (hδj : δ ∈ shadow C F j) (hδk : δ ∈ shadow C F k) :
    p ∣ loc C F k := by
  by_contra h
  have hjk := eq_of_meet_of_coprime C F hδj hδk
    (by rw [hj]; exact (hp.coprime_iff_not_dvd).mpr h)
  subst hjk
  exact h (hj ▸ dvd_refl _)

/-- A part sharing an `F`-coset with a part of local index `p^a`, `a ≥ 1`, has
`p ∣ ℓ`. -/
theorem dvd_of_meet_of_prime_pow {j k : κ} {δ : G ⧸ F} {p a : ℕ} (hp : p.Prime)
    (ha : a ≠ 0) (hj : loc C F j = p ^ a) (hδj : δ ∈ shadow C F j) (hδk : δ ∈ shadow C F k) :
    p ∣ loc C F k := by
  by_contra h
  have hjk := eq_of_meet_of_coprime C F hδj hδk
    (by rw [hj]; exact Nat.Coprime.pow_left a ((hp.coprime_iff_not_dvd).mpr h))
  subst hjk
  exact h (hj ▸ dvd_pow_self p ha)

end Cells

section Seven

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

theorem orderOf_two_ne_zero : orderOf (2 : ZMod 7) ≠ 0 := by
  rw [SevenInstance.orderOf_two]
  norm_num

/-- **Separation**: exact-7 and exact-8 parts share no `F`-coset. -/
theorem sep_of_coprime {j k : κ} (hj : loc C F j = 7)
    (hk : loc C F k = 2 ^ orderOf (2 : ZMod 7)) :
    Disjoint (shadow C F j) (shadow C F k) := by
  rw [Set.disjoint_left]
  intro δ hδj hδk
  have hcop : Nat.Coprime 7 (2 ^ orderOf (2 : ZMod 7)) :=
    Nat.Coprime.pow_right _ (by norm_num)
  have hjk := eq_of_meet_of_coprime C F hδj hδk (by rw [hj, hk]; exact hcop)
  subst hjk
  rw [hj] at hk
  rw [← hk] at hcop
  norm_num at hcop

/-- **The 7-chamber lemma.** -/
theorem seven_dvd_of_meet {j k : κ} {δ : G ⧸ F} (hj : loc C F j = 7)
    (hδj : δ ∈ shadow C F j) (hδk : δ ∈ shadow C F k) : 7 ∣ loc C F k :=
  dvd_of_meet_of_prime C F (by norm_num) hj hδj hδk

/-- The parity consequence for a part meeting an exact-8 part.  The stronger
exact-eight conclusion is proved in `ExactEight`. -/
theorem two_dvd_of_meet {j k : κ} {δ : G ⧸ F} (hj : loc C F j = 2 ^ orderOf (2 : ZMod 7))
    (hδj : δ ∈ shadow C F j) (hδk : δ ∈ shadow C F k) : 2 ∣ loc C F k :=
  dvd_of_meet_of_prime_pow C F Nat.prime_two orderOf_two_ne_zero hj hδj hδk

/-- **`false_of_covering` with `hsep` and the 7-chamber discharged.**  The
remaining group-theoretic inputs are (CB) and the exact-8 chamber: a part
sharing an `F`-coset with an exact-8 part, whose local index is even (which
`two_dvd_of_meet` proves), has `7 ∣ ℓ` or `2^{ord₇ 2} ∣ ℓ`. -/
theorem false_of_covering_chamber [Group.IsSolvable G] [F.Normal]
    (hG : ∀ p, p.Prime → p ∣ Nat.card G → p ≤ 7)
    (hdist : Set.InjOn (fun j ↦ (C.parts j).index) (nonUniv C F))
    (hne : (nonUniv C F).Nonempty)
    (hCB : ∀ j ∈ nonUniv C F, 7 ∣ loc C F j ∨ 2 ^ orderOf (2 : ZMod 7) ∣ loc C F j ∨
      3 ^ orderOf (3 : ZMod 7) ∣ loc C F j ∨ 5 ^ orderOf (5 : ZMod 7) ∣ loc C F j)
    (h8 : ∀ j k, loc C F j = 2 ^ orderOf (2 : ZMod 7) →
      ∀ δ ∈ shadow C F j, δ ∈ shadow C F k → 2 ∣ loc C F k →
        7 ∣ loc C F k ∨ 2 ^ orderOf (2 : ZMod 7) ∣ loc C F k) : False := by
  refine false_of_covering C F hG hdist hne hCB ?_ fun j k hj hk ↦ sep_of_coprime C F hj hk
  rintro j k (hj | hj) δ hδj hδk
  · exact Or.inl (seven_dvd_of_meet C F hj hδj hδk)
  · exact h8 j k hj δ hδj hδk (two_dvd_of_meet C F hj hδj hδk)

end Seven

end Chamber

end Erdos274
