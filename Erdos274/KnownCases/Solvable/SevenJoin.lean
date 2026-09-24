/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.SevenInstance
import Erdos274.KnownCases.Solvable.DivisorWeight
import Erdos274.KnownCases.Solvable.QuotientShadow
import Mathlib.Tactic.NormNum.Prime

/-!
# The `p = 7` closure, from an exact covering

`DECISION_LOG` D98 §14.  `SevenInstance.seven` refutes the `p = 7` residual
from hypotheses on index vectors.  This file produces those hypotheses from an
exact covering `{gⱼHⱼ}` of a finite solvable group `G` and a normal subgroup
`F`, and leaves as hypotheses only the group theory that is not yet in Lean:
**(CB)** and the **chamber lemmas**.

Per part `j`:
* the shadow size `sⱼ = [HⱼF : F]` (`QuotientShadow.sz`), the head
  `hⱼ = [G:F]/sⱼ` (`head`), and the local index `ℓⱼ = [F : Hⱼ ⊓ F]` (`loc`);
* `index_eq_head_mul_loc`: `[G : Hⱼ] = hⱼ·ℓⱼ`.

The covering side of the argument:
* **Fibre counts.**  `card_mul_ncard_le_of_meet`: if every part meeting a set
  `Ω` of `F`-cosets lies in `T`, then `|F|·|Ω| ≤ ∑_{j∈T} |Hⱼ|`.  With
  `ncard_div_le` this reads `|Ω|/[G:F] ≤ ∑_{j∈T} 1/[G:Hⱼ]`.
* `not_le_of_meet`: a part sharing an `F`-coset with a non-universal part is
  itself non-universal.
* **Minimal heads.**  `minimals S` is an antichain with the same up-set as `S`.

`false_of_covering` is the join.  Lemma O enters through
`DivisorWeight.W_up_heads_le`.  The fibre counts give `pr A + pr B ≤ ν₇₈`, and
exact-7 and exact-8 fibres are disjoint (`hsep`).  The index vectors come from
`DivisorWeight.vec`.
-/

namespace Erdos274

namespace SevenJoin

open Set QuotientShadow ExpWeight ApexCharging DivisorWeight
open scoped ENNReal NNReal Pointwise

universe u v

/-! ### Minimal elements -/

section Minimals

variable {ι : Type*}

open Classical in
/-- The minimal elements of a finite set of vectors. -/
noncomputable def minimals (S : Finset (ι → ℕ)) : Finset (ι → ℕ) :=
  S.filter fun x ↦ ∀ y ∈ S, y ≤ x → y = x

theorem mem_minimals {S : Finset (ι → ℕ)} {x : ι → ℕ} :
    x ∈ minimals S ↔ x ∈ S ∧ ∀ y ∈ S, y ≤ x → y = x := by
  classical
  rw [minimals, Finset.mem_filter]

theorem minimals_subset (S : Finset (ι → ℕ)) : minimals S ⊆ S :=
  fun _ hx ↦ (mem_minimals.mp hx).1

theorem isAntichain_minimals (S : Finset (ι → ℕ)) :
    IsAntichain (· ≤ ·) (minimals S : Set (ι → ℕ)) := by
  intro x hx y hy hxy hle
  exact hxy ((mem_minimals.mp hy).2 x (mem_minimals.mp hx).1 hle)

theorem exists_minimals_le {S : Finset (ι → ℕ)} {x : ι → ℕ} (hx : x ∈ S) :
    ∃ m ∈ minimals S, m ≤ x := by
  obtain ⟨b, hbx, hb⟩ := (S.finite_toSet.isPWO).exists_le_minimal (Finset.mem_coe.mpr hx)
  exact ⟨b, mem_minimals.mpr ⟨hb.1, fun y hy hyb ↦ le_antisymm hyb (hb.2 hy hyb)⟩, hbx⟩

theorem up_minimals (S : Finset (ι → ℕ)) :
    up (minimals S : Set (ι → ℕ)) = up (S : Set (ι → ℕ)) := by
  ext z
  constructor
  · rintro ⟨h, hh, hz⟩
    exact ⟨h, minimals_subset S hh, hz⟩
  · rintro ⟨h, hh, hz⟩
    obtain ⟨m, hm, hmh⟩ := exists_minimals_le hh
    exact ⟨m, hm, hmh.trans hz⟩

theorem up_mono {S T : Set (ι → ℕ)} (h : S ⊆ T) : up S ⊆ up T :=
  fun _ ⟨x, hx, hz⟩ ↦ ⟨x, h hx, hz⟩

end Minimals

/-! ### Heads, local indices and fibre counts -/

section Covering

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

/-- The local index `ℓⱼ = [F : Hⱼ ⊓ F]`. -/
noncomputable def loc (j : κ) : ℕ := (C.parts j).relIndex F

/-- The head `hⱼ = [G : F]/sⱼ`. -/
noncomputable def head (j : κ) : ℕ := F.index / sz C F j

omit [Fintype G] in
theorem card_inf_mul_loc (j : κ) :
    Nat.card (C.parts j ⊓ F : Subgroup G) * loc C F j = Nat.card F := by
  have h := Subgroup.relIndex_inf_mul_relIndex (⊥ : Subgroup G) (C.parts j) F
  rwa [bot_inf_eq, Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h

omit [Fintype G] in
theorem loc_dvd_card (j : κ) : loc C F j ∣ Nat.card G :=
  (Subgroup.relIndex_dvd_card _ _).trans (Subgroup.card_subgroup_dvd_card F)

omit [Fintype G] in
/-- A part is universal exactly when its local index is `1`. -/
theorem le_of_loc_eq_one {j : κ} (h : loc C F j = 1) : F ≤ C.parts j :=
  Subgroup.relIndex_eq_one.mp h

/-- **Fibre count.**  If every part meeting `Ω` lies in `T`, the preimage of
`Ω` is covered by the cells of `T`. -/
theorem card_mul_ncard_le_of_meet (Ω : Set (G ⧸ F)) (T : Finset κ)
    (hT : ∀ j, ∀ δ ∈ Ω, δ ∈ shadow C F j → j ∈ T) :
    Nat.card F * Ω.ncard ≤ ∑ j ∈ T, Nat.card (C.parts j) := by
  classical
  rw [← card_ptsOf]
  have hsub : (QuotientGroup.mk ⁻¹' Ω : Set G) ⊆ (ptsOf C T : Set G) := by
    intro z hz
    obtain ⟨k, hk⟩ := C.exists_mem z
    have hks : ((z : G ⧸ F)) ∈ shadow C F k := by
      rw [mem_shadow_iff]
      exact ⟨(C.reps k)⁻¹ * z, (mem_leftCoset_iff _).mp hk, by simp⟩
    rw [Finset.mem_coe]
    exact Finset.mem_biUnion.mpr ⟨k, hT k _ hz hks, (MassForm.mem_cell C).mpr hk⟩
  have h1 := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset] at h1
  have h2 := QuotientGroup.card_preimage_mk F Ω
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h2
  rw [← h2]
  exact h1

/-- A part sharing an `F`-coset with a non-universal part is non-universal:
a universal part would contain the whole coset. -/
theorem not_le_of_meet {j k : κ} (hj : ¬ F ≤ C.parts j) {δ : G ⧸ F}
    (hδj : δ ∈ shadow C F j) (hδk : δ ∈ shadow C F k) : ¬ F ≤ C.parts k := by
  intro hle
  obtain ⟨h, hh, hδ⟩ := (mem_shadow_iff C F).mp hδj
  obtain ⟨h', hh', hδ'⟩ := (mem_shadow_iff C F).mp hδk
  have hq : (C.reps k * h')⁻¹ * (C.reps j * h) ∈ F := QuotientGroup.eq.mp (hδ'.trans hδ.symm)
  have hx : C.reps j * h ∈ C.reps k • (C.parts k : Set G) := by
    have := NormaliserSlice.mul_mem_cell C
      (show C.reps k * h' ∈ C.reps k • (C.parts k : Set G) from Set.smul_mem_smul_set hh')
      (hle hq)
    have e : C.reps k * h' * ((C.reps k * h')⁻¹ * (C.reps j * h)) = C.reps j * h := by group
    rwa [e] at this
  have hjc : C.reps j * h ∈ C.reps j • (C.parts j : Set G) := Set.smul_mem_smul_set hh
  have hjk := NormaliserSlice.eq_of_mem_cell C hjc hx
  exact hj (by rw [hjk]; exact hle)

omit [Fintype G] in
/-- **The fibre count as an index sum**: `|Ω|/[G:F] ≤ ∑_{j∈T} 1/[G:Hⱼ]`. -/
theorem ncard_div_le [Finite G] (Ω : Set (G ⧸ F)) (T : Finset κ)
    (hΩ : Nat.card F * Ω.ncard ≤ ∑ j ∈ T, Nat.card (C.parts j)) :
    ((Ω.ncard : ℝ≥0) / F.index : ℝ≥0) ≤ ∑ j ∈ T, ((C.parts j).index : ℝ≥0)⁻¹ := by
  rw [← NNReal.coe_le_coe]
  push_cast
  have hn0 : (0 : ℝ) < F.index := by
    exact_mod_cast Nat.pos_of_ne_zero F.index_ne_zero_of_finite
  have hG : (Nat.card F : ℝ) * F.index = Nat.card G := by
    exact_mod_cast Subgroup.card_mul_index F
  have hterm : ∀ j, ((C.parts j).index : ℝ)⁻¹ = Nat.card (C.parts j) / Nat.card G := fun j ↦ by
    have h : (Nat.card (C.parts j) : ℝ) * (C.parts j).index = Nat.card G := by
      exact_mod_cast (C.parts j).card_mul_index
    have hi : ((C.parts j).index : ℝ) ≠ 0 := by
      exact_mod_cast (C.parts j).index_ne_zero_of_finite
    have hc : (Nat.card (C.parts j) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := C.parts j)).ne'
    rw [← h]
    field_simp
  simp only [hterm, ← Finset.sum_div]
  have hΩ' : (Nat.card F : ℝ) * Ω.ncard ≤ ∑ j ∈ T, (Nat.card (C.parts j) : ℝ) := by
    exact_mod_cast hΩ
  have hG0 : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos
  rw [div_le_div_iff₀ hn0 hG0, ← hG]
  calc (Ω.ncard : ℝ) * (Nat.card F * F.index) = (Nat.card F * Ω.ncard) * F.index := by ring
    _ ≤ (∑ j ∈ T, (Nat.card (C.parts j) : ℝ)) * F.index := by gcongr

variable [F.Normal]

theorem head_mul_sz (j : κ) : head C F j * sz C F j = F.index :=
  Nat.div_mul_cancel (sz_dvd_index C F j)

theorem head_dvd_index (j : κ) : head C F j ∣ F.index :=
  Dvd.intro _ (head_mul_sz C F j)

theorem index_div_head (j : κ) : F.index / head C F j = sz C F j :=
  Nat.div_div_self (sz_dvd_index C F j) F.index_ne_zero_of_finite

/-- **`[G : Hⱼ] = hⱼ·ℓⱼ`**, the second isomorphism theorem in index form. -/
theorem index_eq_head_mul_loc (j : κ) : (C.parts j).index = head C F j * loc C F j := by
  have h1 := card_eq_mul_sz C F j
  have h2 := card_inf_mul_loc C F j
  have h3 := Subgroup.card_mul_index F
  have h4 := (C.parts j).card_mul_index
  have hs0 := sz_pos C F j
  have hI0 : 0 < Nat.card (C.parts j ⊓ F : Subgroup G) := Nat.card_pos
  obtain ⟨c, hc⟩ := sz_dvd_index C F j
  have hhead : head C F j = c := by rw [head, hc, Nat.mul_div_cancel_left _ hs0]
  rw [hhead]
  refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hI0 hs0) ?_
  calc Nat.card (C.parts j ⊓ F : Subgroup G) * sz C F j * (C.parts j).index
      = Nat.card (C.parts j) * (C.parts j).index := by rw [h1]
    _ = Nat.card F * F.index := by rw [h4, h3]
    _ = Nat.card (C.parts j ⊓ F : Subgroup G) * sz C F j * (c * loc C F j) := by
        rw [← h2, hc]; ring

end Covering

theorem coe_div_nat (N n : ℕ) (hn : n ≠ 0) :
    ((((N : ℝ≥0) / n : ℝ≥0)) : ℝ≥0∞) = (N : ℝ≥0∞) / n := by
  rw [ENNReal.coe_div (by exact_mod_cast hn)]
  simp

/-! ### Exponent data of a covering

The bridge from a covering to exponent vectors, shared by the general step-4
closure (`Step4Closure.false_of_covering`) and the `p = 7` closure below.
Fix primes `q : ι → ℕ` covering the prime divisors of `|G|`.  Per part `j`:
* `vec_head_add_vec_loc`: `v(dⱼ) = v(hⱼ) + v(ℓⱼ)`, from `dⱼ = hⱼℓⱼ`;
* `w_vec_head_add_vec_loc`: its weight is `1/dⱼ`;
* `injOn_vec_head_add_vec_loc`: distinct indices give distinct vectors;
* `W_up_heads_family_le`, `W_up_heads_nonUniv_le`: Lemma O on the heads,
  `W(up{v(hⱼ)}) ≤ Π·|⋃ shadows|/[G:F] ≤ Π·ν`. -/

section ExponentData

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G) [F.Normal]
  {ι : Type*} {q : ι → ℕ}

/-- **`v(dⱼ) = v(hⱼ) + v(ℓⱼ)`**: the index vector splits into head and local
parts. -/
theorem vec_head_add_vec_loc (hsm : Smooth q (Nat.card G)) (j : κ) :
    vec q (head C F j) + vec q (loc C F j) = vec q ((C.parts j).index) := by
  have hsmh : Smooth q (head C F j) :=
    (hsm.of_dvd F.index_dvd_card).of_dvd (head_dvd_index C F j)
  have hsml : Smooth q (loc C F j) := hsm.of_dvd (loc_dvd_card C F j)
  rw [index_eq_head_mul_loc C F j, vec_mul hsmh.1 hsml.1]

variable (hq : ∀ i, (q i).Prime) (hqi : Function.Injective q)
include hq hqi

/-- The weight of `v(hⱼ) + v(ℓⱼ)` is `1/[G : Hⱼ]`. -/
theorem w_vec_head_add_vec_loc [Fintype ι] (hsm : Smooth q (Nat.card G)) (j : κ) :
    w (ratio q) (vec q (head C F j) + vec q (loc C F j)) =
      ((((C.parts j).index : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [vec_head_add_vec_loc C F hsm j, w_vec hq hqi (hsm.of_dvd (C.parts j).index_dvd_card)]

/-- Parts with distinct indices have distinct vectors `v(hⱼ) + v(ℓⱼ)`. -/
theorem injOn_vec_head_add_vec_loc [Finite ι] (hsm : Smooth q (Nat.card G)) {J : Set κ}
    (hdist : Set.InjOn (fun j ↦ (C.parts j).index) J) :
    Set.InjOn (fun j ↦ vec q (head C F j) + vec q (loc C F j)) J := by
  intro a ha b hb h
  simp only [vec_head_add_vec_loc C F hsm] at h
  exact hdist ha hb (vec_injOn hq hqi (hsm.of_dvd (C.parts a).index_dvd_card)
    (hsm.of_dvd (C.parts b).index_dvd_card) h)

/-- **Lemma O on the heads of a family `T`**:
`W(up{v(hⱼ) : j ∈ T}) ≤ Π·|⋃_{j∈T} shadowⱼ|/[G:F]`. -/
theorem W_up_heads_family_le [Fintype ι] [Group.IsSolvable G] (hsm : Smooth q (Nat.card G))
    (T : Finset κ) :
    W (ratio q) (up (((T.image (head C F)).image (vec q) : Finset (ι → ℕ)) :
      Set (ι → ℕ))) ≤
        (PiN q : ℝ≥0∞) * (((((⋃ j ∈ T, shadow C F j).ncard : ℝ≥0) / F.index : ℝ≥0)) :
          ℝ≥0∞) := by
  classical
  have hH : ∀ h ∈ T.image (head C F), h ∣ F.index := by
    intro h hh
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hh
    exact head_dvd_index C F j
  have himg : (T.image (head C F)).image (F.index / ·) = T.image (sz C F) := by
    rw [Finset.image_image]
    exact Finset.image_congr fun j _ ↦ index_div_head C F j
  have hμ := divisorMass_le_ncard_shadows C F T
  rw [← himg] at hμ
  refine (W_up_heads_le hq hqi (hsm.of_dvd F.index_dvd_card) _ hH hμ).trans (le_of_eq ?_)
  rw [coe_div_nat _ _ F.index_ne_zero_of_finite, mul_div_assoc]

/-- **Lemma O over the non-universal parts**: `W(U) ≤ Π·ν`, where `U` is the
up-set of their heads and `ν = ∑ 1/[G : Hⱼ]` over them.  A part meeting a
non-universal shadow is non-universal, so the fibre count stays inside. -/
theorem W_up_heads_nonUniv_le [Fintype ι] [Group.IsSolvable G]
    (hsm : Smooth q (Nat.card G)) :
    W (ratio q) (up ((((nonUniv C F).image (head C F)).image (vec q) : Finset (ι → ℕ)) :
      Set (ι → ℕ))) ≤
        (PiN q : ℝ≥0∞) * ((∑ j ∈ nonUniv C F, ((C.parts j).index : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  classical
  refine (W_up_heads_family_le C F hq hqi hsm _).trans ?_
  gcongr
  refine ncard_div_le C F _ _ (card_mul_ncard_le_of_meet C F _ _ fun k δ hδ hδk ↦ ?_)
  obtain ⟨j, hj, hδj⟩ := Set.mem_iUnion₂.mp hδ
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, not_le_of_meet C F (Finset.mem_filter.mp hj).2 hδj hδk⟩

end ExponentData

/-! ### The join at `p = 7` -/

section Join

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

/-- **No exact covering realises the `p = 7` residual of step 4.**

The hypotheses are the setting and the group theory not yet formalised:
* the primes of `|G|` are at most `7`, the non-universal parts have distinct
  indices, and there is one;
* **(CB)**: a non-universal local index is divisible by `7`, `2^{ord₇ 2}`,
  `3^{ord₇ 3}` or `5^{ord₇ 5}`;
* **the chamber lemmas**: a part sharing an `F`-coset with an exact-7 or an
  exact-8 part has `7 ∣ ℓ` or `2^{ord₇ 2} ∣ ℓ`, and exact-7 and exact-8 parts
  share no `F`-coset.

The exact-8 index is `2^{ord₇ 2}`, not a literal: it is the index of the
primitive `𝔽₂[C₇]`-module. -/
theorem false_of_covering [Group.IsSolvable G] [F.Normal]
    (hG : ∀ p, p.Prime → p ∣ Nat.card G → p ≤ 7)
    (hdist : Set.InjOn (fun j ↦ (C.parts j).index) (nonUniv C F))
    (hne : (nonUniv C F).Nonempty)
    (hCB : ∀ j ∈ nonUniv C F, 7 ∣ loc C F j ∨ 2 ^ orderOf (2 : ZMod 7) ∣ loc C F j ∨
      3 ^ orderOf (3 : ZMod 7) ∣ loc C F j ∨ 5 ^ orderOf (5 : ZMod 7) ∣ loc C F j)
    (hch : ∀ j k, (loc C F j = 7 ∨ loc C F j = 2 ^ orderOf (2 : ZMod 7)) →
      ∀ δ ∈ shadow C F j, δ ∈ shadow C F k →
        7 ∣ loc C F k ∨ 2 ^ orderOf (2 : ZMod 7) ∣ loc C F k)
    (hsep : ∀ j k, loc C F j = 7 → loc C F k = 2 ^ orderOf (2 : ZMod 7) →
      Disjoint (shadow C F j) (shadow C F k)) : False := by
  classical
  set t := orderOf (2 : ZMod 7) with ht
  set q := SevenInstance.q
  have hq : ∀ i, (q i).Prime := SevenInstance.q_prime
  have hqi : Function.Injective q := SevenInstance.q_injective
  -- smoothness
  have hsm : Smooth q (Nat.card G) := by
    refine ⟨Nat.card_pos.ne', fun p hp ↦ ?_⟩
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hle := hG p hpp (Nat.dvd_of_mem_primeFactors hp)
    interval_cases p <;> first
      | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩
      | norm_num at hpp
  have hsml : ∀ j, Smooth q (loc C F j) := fun j ↦ hsm.of_dvd (loc_dvd_card C F j)
  -- the prime-power indices as vectors
  have e7 : vec q 7 = Pi.single 3 1 := vec_pow hq hqi 3 1
  have e8 : vec q (2 ^ t) = Pi.single 0 t := vec_pow hq hqi 0 t
  have e3 : vec q (3 ^ orderOf (3 : ZMod 7)) = Pi.single 1 (orderOf (3 : ZMod 7)) :=
    vec_pow hq hqi 1 _
  have e5 : vec q (5 ^ orderOf (5 : ZMod 7)) = Pi.single 2 (orderOf (5 : ZMod 7)) :=
    vec_pow hq hqi 2 _
  have s7 : Smooth q 7 := smooth_pow hq 3 1
  have s8 : Smooth q (2 ^ t) := smooth_pow hq 0 t
  have s3 : Smooth q (3 ^ orderOf (3 : ZMod 7)) := smooth_pow hq 1 _
  have s5 : Smooth q (5 ^ orderOf (5 : ZMod 7)) := smooth_pow hq 2 _
  -- the data
  set J := nonUniv C F with hJdef
  set hd : κ → Fin 4 → ℕ := fun j ↦ vec q (head C F j) with hhd_def
  set l : κ → Fin 4 → ℕ := fun j ↦ vec q (loc C F j) with hl_def
  have hwd : ∀ j, w (ratio q) (hd j + l j) = ((((C.parts j).index : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    w_vec_head_add_vec_loc C F hq hqi hsm
  set J7 := J.filter fun j ↦ loc C F j = 7 with hJ7
  set J8 := J.filter fun j ↦ loc C F j = 2 ^ t with hJ8
  set Ω7 : Set (G ⧸ F) := ⋃ j ∈ J7, shadow C F j with hΩ7
  set Ω8 : Set (G ⧸ F) := ⋃ j ∈ J8, shadow C F j with hΩ8
  set J78 := J.filter fun k ↦ ∃ δ ∈ Ω7 ∪ Ω8, δ ∈ shadow C F k with hJ78
  set HS := J.image hd with hHS
  set H₀ := minimals HS with hH₀
  set A := H₀.filter fun x ↦ ∃ j ∈ J7, hd j = x with hA
  set B := H₀.filter fun x ↦ ∃ j ∈ J8, hd j = x with hB
  set ν : ℝ≥0∞ := ∑ j ∈ J, w (ratio q) (hd j + l j) with hν
  set a₇ : ℝ≥0∞ := ((((Ω7.ncard : ℝ≥0) / F.index : ℝ≥0) : ℝ≥0∞)) with ha₇
  set a₈ : ℝ≥0∞ := ((((Ω8.ncard : ℝ≥0) / F.index : ℝ≥0) : ℝ≥0∞)) with ha₈
  have hWu : W (ratio q) univ = (PiN q : ℝ≥0∞) := W_univ_ratio hq
  have hmemJ : ∀ {j}, j ∈ J → ¬ F ≤ C.parts j := fun hj ↦ (Finset.mem_filter.mp hj).2
  -- a part meeting the shadow of a part in `J` is in `J`
  have hmeet : ∀ {j k δ}, j ∈ J → δ ∈ shadow C F j → δ ∈ shadow C F k → k ∈ J :=
    fun hj hδj hδk ↦ Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, not_le_of_meet C F (hmemJ hj) hδj hδk⟩
  -- the ν-sum in `ℝ≥0`
  have hνsum : ∀ T : Finset κ, ∑ j ∈ T, w (ratio q) (hd j + l j) =
      ((∑ j ∈ T, ((C.parts j).index : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := fun T ↦ by
    rw [ENNReal.ofNNReal_finsetSum]
    exact Finset.sum_congr rfl fun j _ ↦ hwd j
  -- Lemma O through the untruncated weight, for a family `T ⊆ J`
  have hLOT := W_up_heads_family_le C F hq hqi hsm
  -- `pr A + pr B ≤ ν₇₈`
  have hsepΩ : Disjoint Ω7 Ω8 := by
    rw [hΩ7, hΩ8, Set.disjoint_iUnion₂_left]
    intro j hj
    rw [Set.disjoint_iUnion₂_right]
    intro k hk
    exact hsep j k (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
  have hJ7J : ∀ {j}, j ∈ J7 → j ∈ J := fun hj ↦ (Finset.mem_filter.mp hj).1
  have hJ8J : ∀ {j}, j ∈ J8 → j ∈ J := fun hj ↦ (Finset.mem_filter.mp hj).1
  have hΩ78 : ∀ {δ}, δ ∈ Ω7 ∪ Ω8 → ∃ j ∈ J, (loc C F j = 7 ∨ loc C F j = 2 ^ t) ∧
      δ ∈ shadow C F j := by
    intro δ hδ
    rcases hδ with hδ | hδ
    · obtain ⟨j, hj, hδj⟩ := Set.mem_iUnion₂.mp hδ
      exact ⟨j, hJ7J hj, Or.inl (Finset.mem_filter.mp hj).2, hδj⟩
    · obtain ⟨j, hj, hδj⟩ := Set.mem_iUnion₂.mp hδ
      exact ⟨j, hJ8J hj, Or.inr (Finset.mem_filter.mp hj).2, hδj⟩
  have ha : a₇ + a₈ ≤ ∑ p ∈ J78, w (ratio q) (hd p + l p) := by
    rw [hνsum, ha₇, ha₈, ← ENNReal.coe_add, ENNReal.coe_le_coe, ← add_div, ← Nat.cast_add,
      ← Set.ncard_union_eq hsepΩ (Set.toFinite _) (Set.toFinite _)]
    refine ncard_div_le C F _ _ (card_mul_ncard_le_of_meet C F _ _ fun k δ hδ hδk ↦ ?_)
    obtain ⟨j, hj, -, hδj⟩ := hΩ78 hδ
    exact Finset.mem_filter.mpr ⟨hmeet hj hδj hδk, δ, hδ, hδk⟩
  -- the pieces of `seven`
  have hHSne : HS.Nonempty := hne.image _
  have hH₀ne : H₀.Nonempty := by
    obtain ⟨x, hx⟩ := hHSne
    obtain ⟨m, hm, -⟩ := exists_minimals_le hx
    exact ⟨m, hm⟩
  have hhd : ∀ p ∈ J, hd p ∈ up (H₀ : Set (Fin 4 → ℕ)) := by
    intro p hp
    obtain ⟨m, hm, hle⟩ := exists_minimals_le (Finset.mem_image_of_mem hd hp)
    exact ⟨m, hm, hle⟩
  have hdivl : ∀ {p} {x : ℕ} (hx : Smooth q x), vec q x ≤ l p ↔ x ∣ loc C F p :=
    fun hx ↦ vec_le_iff hx (hsml _).1
  have hCB' : ∀ p ∈ J, Pi.single 3 1 ≤ l p ∨ Pi.single 0 t ≤ l p ∨
      ∃ f ∈ ({Pi.single 1 (orderOf (3 : ZMod 7)), Pi.single 2 (orderOf (5 : ZMod 7))} :
        Finset (Fin 4 → ℕ)), f ≤ l p := by
    intro p hp
    rw [← e7, ← e8, ← e3, ← e5, hdivl s7, hdivl s8]
    rcases hCB p hp with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨_, Finset.mem_insert_self _ _, (hdivl s3).mpr h⟩)
    · exact Or.inr (Or.inr ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
        (hdivl s5).mpr h⟩)
  have h78 : ∀ p ∈ J78, Pi.single 3 1 ≤ l p ∨ Pi.single 0 t ≤ l p := by
    intro p hp
    obtain ⟨-, δ, hδ, hδp⟩ := Finset.mem_filter.mp hp
    obtain ⟨j, -, hjx, hδj⟩ := hΩ78 hδ
    rw [← e7, ← e8, hdivl s7, hdivl s8]
    exact hch j p hjx δ hδj hδp
  have hinj : Set.InjOn (fun p ↦ hd p + l p) J := injOn_vec_head_add_vec_loc C F hq hqi hsm hdist
  have hA' : ∀ p ∈ J, hd p ∈ H₀ → l p = Pi.single 3 1 → hd p ∈ A := by
    intro p hp hH hl
    rw [← e7] at hl
    have h7 : loc C F p = 7 := vec_injOn hq hqi (hsml p) s7 hl
    exact Finset.mem_filter.mpr ⟨hH, p, Finset.mem_filter.mpr ⟨hp, h7⟩, rfl⟩
  have hB' : ∀ p ∈ J, hd p ∈ H₀ → l p = Pi.single 0 t → hd p ∈ B := by
    intro p hp hH hl
    rw [← e8] at hl
    have h8 : loc C F p = 2 ^ t := vec_injOn hq hqi (hsml p) s8 hl
    exact Finset.mem_filter.mpr ⟨hH, p, Finset.mem_filter.mpr ⟨hp, h8⟩, rfl⟩
  -- Lemma O for `H₀`, `A` and `B`
  have hLO : W (ratio q) (up (H₀ : Set (Fin 4 → ℕ))) ≤ W (ratio q) univ * ν := by
    have hHS : HS = (J.image (head C F)).image (vec q) := by
      rw [hHS, Finset.image_image]
      rfl
    rw [hH₀, up_minimals, hHS, hWu, hν, hνsum]
    exact W_up_heads_nonUniv_le C F hq hqi hsm
  have hsubT : ∀ (T : Finset κ) (X : Finset (Fin 4 → ℕ)), (∀ x ∈ X, ∃ j ∈ T, hd j = x) →
      W (ratio q) (up (X : Set (Fin 4 → ℕ))) ≤
        W (ratio q) (up (((T.image (head C F)).image (vec q) : Finset (Fin 4 → ℕ)) :
          Set (Fin 4 → ℕ))) := by
    intro T X hX
    refine W_mono (up_mono fun x hx ↦ ?_)
    obtain ⟨j, hj, rfl⟩ := hX x hx
    rw [Finset.coe_image, Finset.coe_image]
    exact ⟨head C F j, ⟨j, hj, rfl⟩, rfl⟩
  have hLOA : W (ratio q) (up (A : Set (Fin 4 → ℕ))) ≤ W (ratio q) univ * a₇ := by
    rw [hWu]
    exact (hsubT J7 A fun x hx ↦ (Finset.mem_filter.mp hx).2).trans (hLOT J7)
  have hLOB : W (ratio q) (up (B : Set (Fin 4 → ℕ))) ≤ W (ratio q) univ * a₈ := by
    rw [hWu]
    exact (hsubT J8 B fun x hx ↦ (Finset.mem_filter.mp hx).2).trans (hLOT J8)
  exact SevenInstance.seven (t := t) (t₃ := orderOf (3 : ZMod 7)) (t₅ := orderOf (5 : ZMod 7))
    rfl rfl rfl (isAntichain_minimals HS) hH₀ne (Finset.filter_subset _ _) hd l hhd hCB' h78
    hinj hA' hB' ν a₇ a₈ le_rfl ha hLO hLOA hLOB

end Join

end SevenJoin

end Erdos274
