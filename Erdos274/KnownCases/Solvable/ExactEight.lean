/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.KnownCases.Solvable.Chamber
public import Erdos274.KnownCases.Solvable.CyclotomicBlock


/-!
# The exact-`(p+1)` chamber

`DECISION_LOG` D98 §§13–14.  At `p = 7` an exact-8 part has local index
`8 = 7 + 1`.  The chamber lemma asks that every part sharing an `F`-coset
with it have `7 ∣ ℓ` or `8 ∣ ℓ`.  The paper route went through
`F/core ≅ AGL(1,8)`.  This file proves it by a fixed-point count on the
`p + 1` cosets of `Y₀ = Hⱼ ⊓ F`, which needs neither solvability nor (CB).

* `transitive_or_dvd`.  Let `P ≤ Y` be a `p`-group that moves some coset of
  `Y₀`, where `[H : Y₀] = p + 1`.
  - `P` has exactly one fixed point `x₀` on `H/Y₀`, since the fixed points
    number `≡ p + 1 (mod p)` and are not all of `H/Y₀`.
  - The complement of the `Y`-orbit of `x₀` is `P`-invariant and has no
    `P`-fixed point, so its size is `0` or `p`.
  - Size `0`: `Y` is transitive on `H/Y₀`, so `H = Y₀Y`.  Size `p`: `Y`
    fixes `x₀`, so `Y` lies in a conjugate of `Y₀` and `(p+1) ∣ [H : Y]`.
* `dvd_of_meet_of_succ`, **the exact-`(p+1)` chamber**.  Let `F` have no
  nontrivial `p′`-quotient (`CyclotomicBlock.IsPResidual`).  A part sharing an
  `F`-coset with a part of local index `p + 1` has `p ∣ ℓ` or `(p+1) ∣ ℓ`.
  - If `p ∤ ℓ`, a conjugate `P` of a Sylow `p`-subgroup `Q` of `F` lies in
    `Y = Hₖ ⊓ F` (`CyclotomicBlock.exists_conj_mem_of_not_dvd`).
  - `P` moves some coset of `Y₀`: otherwise `Q` lies in the normal core of
    `Y₀`, a normal subgroup of `p′`-index, which is then `F`.
  - In the transitive case the two cells meet (`Chamber.eq_of_meet_of_mul`),
    so the parts coincide.
-/

@[expose] public section

namespace Erdos274

namespace ExactEight

open MulAction QuotientShadow SevenJoin Chamber CyclotomicBlock

universe u v

section Action

variable {H : Type u} [Group H] [Finite H]

/-- **A `p`-group moving `p + 1` cosets.** -/
theorem transitive_or_dvd {p : ℕ} [hp : Fact p.Prime] {Y₀ Y P : Subgroup H}
    (hP : IsPGroup p P) (hPY : P ≤ Y) (hY₀ : Y₀.index = p + 1)
    (hnt : ∃ x ∈ P, ∃ b : H, b * x * b⁻¹ ∉ Y₀) :
    (∀ h : H, ∃ a ∈ Y₀, ∃ b ∈ Y, h = a * b) ∨ (p + 1) ∣ Y.index := by
  classical
  have hp2 := hp.out.two_le
  have hX : Nat.card (H ⧸ Y₀) = p + 1 := hY₀
  -- the fixed points of `P` on `H/Y₀`: exactly one
  have hlt : (fixedPoints P (H ⧸ Y₀)).ncard < p + 1 := by
    obtain ⟨x, hx, b, hb⟩ := hnt
    have hne : ((b⁻¹ : H) : H ⧸ Y₀) ∉ fixedPoints P (H ⧸ Y₀) := by
      intro hfix
      have h := hfix ⟨x, hx⟩
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
      apply hb
      have e : b * x * b⁻¹ = ((x * b⁻¹)⁻¹ * b⁻¹)⁻¹ := by group
      rw [e]
      exact Y₀.inv_mem h
    rw [← hX, ← Set.ncard_univ]
    exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr fun h ↦ hne (h ▸ Set.mem_univ _))
  have hone : (fixedPoints P (H ⧸ Y₀)).ncard = 1 := by
    have hmod := hP.card_modEq_card_fixedPoints (H ⧸ Y₀)
    rw [hX, Nat.card_coe_set_eq] at hmod
    have hm : (p + 1) % p = (fixedPoints P (H ⧸ Y₀)).ncard % p := hmod
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < p)] at hm
    rcases Nat.lt_or_ge (fixedPoints P (H ⧸ Y₀)).ncard p with h | h
    · rw [Nat.mod_eq_of_lt h] at hm
      omega
    · rw [show (fixedPoints P (H ⧸ Y₀)).ncard = p by omega, Nat.mod_self] at hm
      omega
  obtain ⟨x₀, hx₀⟩ := Set.ncard_eq_one.mp hone
  -- the complement of the `Y`-orbit of `x₀`, as a `P`-set
  let S : SubMulAction P (H ⧸ Y₀) :=
    { carrier := (orbit Y x₀)ᶜ
      smul_mem' := by
        intro c z hz hmem
        apply hz
        obtain ⟨y, hy⟩ := mem_orbit_iff.mp hmem
        refine mem_orbit_iff.mpr ⟨⟨(c : H)⁻¹, Y.inv_mem (hPY c.2)⟩ * y, ?_⟩
        rw [mul_smul, hy]
        exact inv_smul_smul (c : H) z }
  have hS : Nat.card (fixedPoints P S) = 0 := by
    rw [Nat.card_eq_zero]
    refine Or.inl ⟨fun ⟨z, hz⟩ ↦ ?_⟩
    have hz' : (z : H ⧸ Y₀) ∈ fixedPoints P (H ⧸ Y₀) := fun c ↦ congrArg Subtype.val (hz c)
    rw [hx₀, Set.mem_singleton_iff] at hz'
    have hzS : (z : H ⧸ Y₀) ∉ orbit Y x₀ := z.2
    rw [hz'] at hzS
    exact hzS (mem_orbit_self x₀)
  have hdvd : p ∣ (orbit Y x₀)ᶜ.ncard := by
    have hmod := hP.card_modEq_card_fixedPoints S
    rw [hS] at hmod
    exact (Nat.modEq_zero_iff_dvd).mp hmod
  have hsum := Set.ncard_add_ncard_compl (orbit Y x₀)
  rw [hX] at hsum
  have hpos : 0 < (orbit Y x₀).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨x₀, mem_orbit_self x₀⟩
  rcases Nat.eq_zero_or_pos (orbit Y x₀)ᶜ.ncard with h0 | h0
  · -- `Y` is transitive on `H/Y₀`
    left
    have horb : orbit Y x₀ = Set.univ := by
      rw [Set.ncard_eq_zero, Set.compl_empty_iff] at h0
      exact h0
    intro h
    obtain ⟨y₁, hy₁⟩ := mem_orbit_iff.mp (horb ▸ Set.mem_univ ((h⁻¹ : H) : H ⧸ Y₀))
    obtain ⟨y₂, hy₂⟩ := mem_orbit_iff.mp (horb ▸ Set.mem_univ ((1 : H) : H ⧸ Y₀))
    have h3 : (y₁ * y₂⁻¹) • ((1 : H) : H ⧸ Y₀) = ((h⁻¹ : H) : H ⧸ Y₀) := by
      rw [← hy₂, ← hy₁, mul_smul, inv_smul_smul]
    rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
      QuotientGroup.eq] at h3
    set w : H := ((y₁ * y₂⁻¹ : Y) : H)
    refine ⟨(w⁻¹ * h⁻¹)⁻¹, Y₀.inv_mem h3, w⁻¹, Y.inv_mem (y₁ * y₂⁻¹).2, by group⟩
  · -- `Y` fixes `x₀`, so it lies in a conjugate of `Y₀`
    right
    have hle' : p ≤ (orbit Y x₀)ᶜ.ncard := Nat.le_of_dvd h0 hdvd
    have horb : (orbit Y x₀).ncard = 1 := by omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp horb
    have hfixY : ∀ y : Y, y • x₀ = x₀ := by
      intro y
      have e1 : y • x₀ ∈ orbit Y x₀ := mem_orbit x₀ y
      have e2 : x₀ ∈ orbit Y x₀ := mem_orbit_self x₀
      rw [ha, Set.mem_singleton_iff] at e1 e2
      exact e1.trans e2.symm
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x₀
    have hle : Y.map ((MulAut.conj g⁻¹ : H ≃* H) : H →* H) ≤ Y₀ := by
      rintro _ ⟨y, hy, rfl⟩
      have h := hfixY ⟨y, hy⟩
      rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
      change g⁻¹ * y * g⁻¹⁻¹ ∈ Y₀
      have e : g⁻¹ * y * g⁻¹⁻¹ = ((y * g)⁻¹ * g)⁻¹ := by group
      rw [e]
      exact Y₀.inv_mem h
    have := Subgroup.index_dvd_of_le hle
    rwa [hY₀, Subgroup.index_map_equiv] at this

end Action

section Cover

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

/-- **The exact-`(p+1)` chamber.** -/
theorem dvd_of_meet_of_succ {p : ℕ} [Fact p.Prime] (hres : IsPResidual p F) {j k : κ}
    {δ : G ⧸ F} (hj : loc C F j = p + 1) (hδj : δ ∈ shadow C F j) (hδk : δ ∈ shadow C F k) :
    p ∣ loc C F k ∨ (p + 1) ∣ loc C F k := by
  by_cases hpk : p ∣ loc C F k
  · exact Or.inl hpk
  right
  obtain ⟨S⟩ : Nonempty (Sylow p F) := inferInstance
  set Q' : Subgroup F := (S : Subgroup F)
  set Y₀ := (C.parts j).subgroupOf F
  set Y := (C.parts k).subgroupOf F
  have hQ' : IsPGroup p Q' := S.isPGroup'
  -- a conjugate `P` of `Q` inside `Y`
  obtain ⟨g, hg⟩ := CyclotomicBlock.exists_conj_mem_of_not_dvd hQ' hpk
  set P := Q'.map ((MulAut.conj g⁻¹ : F ≃* F) : F →* F)
  have hP : IsPGroup p P := hQ'.map _
  have hPY : P ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    change g⁻¹ * x * g⁻¹⁻¹ ∈ Y
    rw [inv_inv]
    exact hg x hx
  -- `P` moves a coset of `Y₀`
  have hnt : ∃ x ∈ P, ∃ b : F, b * x * b⁻¹ ∉ Y₀ := by
    by_contra hall
    push Not at hall
    have hQc : Q' ≤ Y₀.normalCore := by
      intro x hx b
      have h := hall (g⁻¹ * x * g⁻¹⁻¹) ⟨x, hx, rfl⟩ (b * g)
      have e : b * g * (g⁻¹ * x * g⁻¹⁻¹) * (b * g)⁻¹ = b * x * b⁻¹ := by group
      rwa [e] at h
    have hcore : Y₀.normalCore = ⊤ := hres _ inferInstance
      fun h ↦ S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hQc))
    have htop : Y₀ = ⊤ := top_le_iff.mp (hcore ▸ Y₀.normalCore_le)
    have h1 : loc C F j = 1 := by
      change Y₀.index = 1
      rw [htop, Subgroup.index_top]
    have := (Fact.out : p.Prime).two_le
    omega
  rcases transitive_or_dvd hP hPY hj hnt with hmul | hdvd
  · -- the cells meet, so the parts coincide
    have hjk : j = k := eq_of_meet_of_mul C F hδj hδk fun f hf ↦ by
      obtain ⟨a, ha, b, hb, hab⟩ := hmul ⟨f, hf⟩
      exact ⟨a, ⟨Subgroup.mem_subgroupOf.mp ha, a.2⟩, b, ⟨Subgroup.mem_subgroupOf.mp hb, b.2⟩,
        congrArg Subtype.val hab⟩
    subst hjk
    rw [hj]
  · exact hdvd

/-- **The exact-8 chamber** at `p = 7`: `2^{ord₇ 2} = 7 + 1`. -/
theorem exact_eight (hres : IsPResidual 7 F) {j k : κ} {δ : G ⧸ F}
    (hj : loc C F j = 2 ^ orderOf (2 : ZMod 7))
    (hδj : δ ∈ shadow C F j) (hδk : δ ∈ shadow C F k) :
    7 ∣ loc C F k ∨ 2 ^ orderOf (2 : ZMod 7) ∣ loc C F k := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h8 : 2 ^ orderOf (2 : ZMod 7) = 7 + 1 := by norm_num [SevenInstance.orderOf_two]
  rw [h8] at hj ⊢
  exact dvd_of_meet_of_succ C F hres hj hδj hδk

end Cover

end ExactEight

end Erdos274
