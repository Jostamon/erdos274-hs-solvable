/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.ApexCharging

/-!
# The apex-charging criterion (D98 §14), in general

`DECISION_LOG` D98 §14 (Sol's argument, with the `3⁶`/`5⁶` remainder bounded
crudely, which simplifies it and widens the margin).

**Data.**  Coordinates `i ≠ j`, shift length `t ≥ 1`, and a finite set `F` of
further witness vectors.  An antichain `H₀` of minimal heads, `U = up H₀`,
and subsets `A`, `B` (the minimal heads carrying an exact-`j` part and an
exact-`i` part).  A finite family `J` of *parts*, each with a head `hd p ∈ U`
and a local vector `l p`, whose points `hd p + l p` are distinct, and a
subfamily `J₇₈` (the parts meeting the exact regions).

**Hypotheses supplied by the group theory** (named as at `p = 7`):

* (CB) every `l p` lies above `δⱼ`, `t·δᵢ` or some `f ∈ F`;
* (chamber) every `l p` with `p ∈ J₇₈` lies above `δⱼ` or `t·δᵢ`;
* exactness: a part at a minimal head with `l = δⱼ` has its head in `A`, and
  one with `l = t·δᵢ` has its head in `B`;
* (fibres) `ν ≤ ∑_J w(point)` and `a₇ + a₈ ≤ ∑_{J₇₈} w(point)`;
* (Lemma O) `W(U) ≤ Π·ν`, `W(up A) ≤ Π·a₇`, `W(up B) ≤ Π·a₈`, `Π = W(ℕ^ι)`.

**Conclusion** (`closure_ineq`).  With `a = rⱼ`, `b = rᵢ^t`,
`γ = ∑_{1≤m<t} rᵢ^m` and `ε = ∑_{f∈F} w(f)`, if `γ ≤ 1` and
`b ≤ ab + aγ`, then

    2b + b·Π·b·a + 1 + Π·b·a ≤ b·Π·(b + a) + Π·(b + a + ε).

It is an inequality between numbers built from the ratios alone.
`SevenClosure.seven` evaluates it at `p = 7` and finds it false.

**Proof outline.**
1. The exact regions draw their indices from `(U+eᵢ) ∪ (U+eⱼ)` minus the
   unusable exact-7 apexes (K3).
2. All parts draw from the same set minus all unusable apexes, plus the
   `F`-shifts (K4).
3. The two Lemma O union bounds force the apexes to carry mass.
4. The charging lemma makes the defect `𝒟` pay for the apexes it absorbs.
-/

namespace Erdos274

namespace SevenClosure

open Set ExpWeight ApexCharging
open scoped ENNReal

variable {ι κ : Type*} [Fintype ι] {r : ι → ℝ≥0∞}

/-- Compatibility wrapper for the generic up-set weight bound. -/
theorem W_up_le (H₀ A : Finset (ι → ℕ)) :
    W r (up (H₀ : Set (ι → ℕ))) ≤ W r (up (A : Set (ι → ℕ))) + W r univ * ∑ h ∈ H₀ \ A, w r h :=
  ApexCharging.W_up_le H₀ A

/-! ### The criterion -/

variable [DecidableEq ι]

/-- **The apex-charging criterion.**  See the module docstring. -/
theorem closure_ineq (hr : ∀ k, r k ≠ ⊤) (hr0 : ∀ k, r k ≠ 0) (hPm : W r univ ≠ ⊤)
    {i j : ι} (hij : i ≠ j) {t : ℕ} (ht : 1 ≤ t) (F : Finset (ι → ℕ))
    {H₀ A B : Finset (ι → ℕ)} (hH₀ : IsAntichain (· ≤ ·) (H₀ : Set (ι → ℕ)))
    (hne : H₀.Nonempty)
    {J J₇₈ : Finset κ} (hJ : J₇₈ ⊆ J) (hd l : κ → ι → ℕ)
    (hhd : ∀ p ∈ J, hd p ∈ up (H₀ : Set (ι → ℕ)))
    (hCB : ∀ p ∈ J, Pi.single j 1 ≤ l p ∨ Pi.single i t ≤ l p ∨ ∃ f ∈ F, f ≤ l p)
    (h78 : ∀ p ∈ J₇₈, Pi.single j 1 ≤ l p ∨ Pi.single i t ≤ l p)
    (hinj : Set.InjOn (fun p ↦ hd p + l p) J)
    (hA : ∀ p ∈ J, hd p ∈ H₀ → l p = Pi.single j 1 → hd p ∈ A)
    (hB : ∀ p ∈ J, hd p ∈ H₀ → l p = Pi.single i t → hd p ∈ B)
    (ν a₇ a₈ : ℝ≥0∞)
    (hν : ν ≤ ∑ p ∈ J, w r (hd p + l p))
    (ha : a₇ + a₈ ≤ ∑ p ∈ J₇₈, w r (hd p + l p))
    (hLO : W r (up (H₀ : Set (ι → ℕ))) ≤ W r univ * ν)
    (hLOA : W r (up (A : Set (ι → ℕ))) ≤ W r univ * a₇)
    (hLOB : W r (up (B : Set (ι → ℕ))) ≤ W r univ * a₈)
    (hγ1 : ∑ m ∈ Finset.Ico 1 t, r i ^ m ≤ 1)
    (hγ : r i ^ t ≤ r j * r i ^ t + r j * ∑ m ∈ Finset.Ico 1 t, r i ^ m) :
    2 * r i ^ t + r i ^ t * W r univ * r i ^ t * r j + 1 + W r univ * r i ^ t * r j
      ≤ r i ^ t * W r univ * (r i ^ t + r j)
        + W r univ * (r i ^ t + r j + ∑ f ∈ F, w r f) := by
  classical
  -- notation
  set Pm := W r univ with hPmdef
  set U := W r (up (H₀ : Set (ι → ℕ))) with hUdef
  set a := r j with hadef
  set b := r i ^ t with hbdef
  set γ := ∑ m ∈ Finset.Ico 1 t, r i ^ m with hγdef
  set ε := ∑ f ∈ F, w r f with hεdef
  set ei : ι → ℕ := Pi.single i t with hei
  set ej : ι → ℕ := Pi.single j 1 with hej
  set D := defect (up (H₀ : Set (ι → ℕ))) ei ej with hD
  set Z₇ : Finset (ι → ℕ) := (H₀ \ A).image (· + ej) with hZ₇
  set Z₈ : Finset (ι → ℕ) := (H₀ \ B).image (· + ei) with hZ₈
  set Uni := shift ei (up (H₀ : Set (ι → ℕ))) ∪ shift ej (up (H₀ : Set (ι → ℕ))) with hUni
  set Z7s := ∑ h ∈ H₀ \ A, w r h with hZ7s
  set Z8s := ∑ h ∈ H₀ \ B, w r h with hZ8s
  set X7 := W r ((Z₇ : Set (ι → ℕ)) ∩ D) with hX7
  set Z7o := W r ((Z₇ : Set (ι → ℕ)) \ D) with hZ7o
  set Y8 := W r (((Z₈ : Set (ι → ℕ)) \ Z₇) ∩ D) with hY8
  set O := W r ((Z₇ : Set (ι → ℕ)) ∩ Z₈) with hO
  set Z8o := W r ((Z₈ : Set (ι → ℕ)) \ D) with hZ8o
  have hwei : w r ei = b := w_single r i t
  have hwej : w r ej = a := by rw [hej, w_single, pow_one]
  -- (a) the exact inclusion–exclusion
  have hIE : W r Uni + W r D + b * a * U = (b + a) * U := by
    have := W_shift_union_add_defect r (H₀ : Set (ι → ℕ)) ei ej
    rwa [hwei, hwej] at this
  -- (b) the apex masses split along `𝒟`
  have hZ7le : a * Z7s ≤ X7 + Z7o := by
    rw [← hwej, ← W_image_add, ← W_union_of_disjoint]
    · exact le_of_eq (by rw [inter_union_sdiff])
    · exact disjoint_sdiff_inter.symm
  have hZ8le : b * Z8s ≤ Z8o + Y8 + O := by
    rw [← hwei, ← W_image_add]
    refine (W_mono (T := (((Z₈ : Set (ι → ℕ)) \ D) ∪ ((((Z₈ : Set (ι → ℕ)) \ Z₇) ∩ D)))
        ∪ ((Z₇ : Set (ι → ℕ)) ∩ Z₈)) fun z hz ↦ ?_).trans ?_
    · by_cases hzD : z ∈ D
      · by_cases hz7 : z ∈ (Z₇ : Set (ι → ℕ))
        · exact Or.inr ⟨hz7, hz⟩
        · exact Or.inl (Or.inr ⟨⟨hz, hz7⟩, hzD⟩)
      · exact Or.inl (Or.inl ⟨hz, hzD⟩)
    · exact (W_union_le _ _).trans (add_le_add (W_union_le _ _) le_rfl)
  -- (c) the two union bounds
  have hUA : U ≤ W r (up (A : Set (ι → ℕ))) + Pm * Z7s := W_up_le H₀ A
  have hUB : U ≤ W r (up (B : Set (ι → ℕ))) + Pm * Z8s := W_up_le H₀ B
  -- membership facts for the part points
  have hZ7mem : ∀ z ∈ (Z₇ : Set (ι → ℕ)), ∃ h ∈ H₀, h ∉ A ∧ z = h + ej := by
    intro z hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    obtain ⟨hh0, hhA⟩ := Finset.mem_sdiff.1 hh
    exact ⟨h, hh0, hhA, rfl⟩
  have hZ8mem : ∀ z ∈ (Z₈ : Set (ι → ℕ)), ∃ h ∈ H₀, h ∉ B ∧ z = h + ei := by
    intro z hz
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hz)
    obtain ⟨hh0, hhB⟩ := Finset.mem_sdiff.1 hh
    exact ⟨h, hh0, hhB, rfl⟩
  have hZ7Uni : (Z₇ : Set (ι → ℕ)) ⊆ Uni := fun z hz ↦ by
    obtain ⟨h, hh, -, rfl⟩ := hZ7mem z hz
    exact Or.inr (add_mem_shift (mem_up_of_mem hh))
  have hZ8Uni : (Z₈ : Set (ι → ℕ)) ⊆ Uni := fun z hz ↦ by
    obtain ⟨h, hh, -, rfl⟩ := hZ8mem z hz
    exact Or.inl (add_mem_shift (mem_up_of_mem hh))
  -- a part with local vector above `eⱼ` or `eᵢ` avoids the unusable apexes
  have hnot7 : ∀ p ∈ J, (Pi.single j 1 ≤ l p ∨ Pi.single i t ≤ l p) →
      hd p + l p ∉ (Z₇ : Set (ι → ℕ)) \ D := by
    rintro p hp hl ⟨hz7, hnD⟩
    obtain ⟨h, hh, hhA, heq⟩ := hZ7mem _ hz7
    rcases apexJ_of_part hH₀ hij ht hh (hhd p hp) hl heq with ⟨hdh, hlj⟩ | hmem
    · exact hhA (hdh ▸ hA p hp (hdh ▸ hh) hlj)
    · exact hnD (heq ▸ hmem)
  have hnot8 : ∀ p ∈ J, (Pi.single j 1 ≤ l p ∨ Pi.single i t ≤ l p) →
      hd p + l p ∉ (Z₈ : Set (ι → ℕ)) \ D := by
    rintro p hp hl ⟨hz8, hnD⟩
    obtain ⟨h, hh, hhB, heq⟩ := hZ8mem _ hz8
    rcases apexI_of_part hH₀ hij ht hh (hhd p hp) hl heq with ⟨hdh, hli⟩ | hmem
    · exact hhB (hdh ▸ hB p hp (hdh ▸ hh) hli)
    · exact hnD (heq ▸ hmem)
  have hUniOf : ∀ p ∈ J, (Pi.single j 1 ≤ l p ∨ Pi.single i t ≤ l p) → hd p + l p ∈ Uni := by
    rintro p hp (hl | hl)
    · exact Or.inr (add_mem_shift_up (hhd p hp) hl)
    · exact Or.inl (add_mem_shift_up (hhd p hp) hl)
  -- (d) K3: the exact regions
  have hK3 : a₇ + a₈ + Z7o ≤ W r Uni := by
    have hmaps : ∀ p ∈ J₇₈, hd p + l p ∈ Uni \ ((Z₇ : Set (ι → ℕ)) \ D) := fun p hp ↦
      ⟨hUniOf p (hJ hp) (h78 p hp), hnot7 p (hJ hp) (h78 p hp)⟩
    have hsum := sum_le_W_of_mapsTo (r := r) J₇₈ (fun p ↦ hd p + l p)
      (hinj.mono (Finset.coe_subset.2 hJ)) hmaps
    have hsplit : W r (Uni \ ((Z₇ : Set (ι → ℕ)) \ D)) + Z7o = W r Uni := by
      rw [hZ7o, ← W_union_of_disjoint disjoint_sdiff_left, sdiff_union_of_subset
        (sdiff_subset.trans hZ7Uni)]
    calc a₇ + a₈ + Z7o ≤ W r (Uni \ ((Z₇ : Set (ι → ℕ)) \ D)) + Z7o := by
          gcongr; exact ha.trans hsum
      _ = W r Uni := hsplit
  -- (e) the charging lemma, with `∑_{m<t} = 1 + γ`
  have hcharge : (1 + γ) * X7 + Y8 ≤ W r D := by
    have hβ : ∑ m ∈ Finset.range t, r i ^ m = 1 + γ := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero]
    have := charging r (t := t) (A := A) (B := B) hH₀ hij
    rwa [hβ] at this
  have hX7D : X7 ≤ W r D :=
    ((le_mul_of_one_le_left zero_le le_self_add).trans le_self_add).trans hcharge
  -- (f) K4: every part
  have hK4 : ν + Z7o + Z8o ≤ W r Uni + ε * U := by
    set Qs := ((Z₇ : Set (ι → ℕ)) ∪ Z₈) \ D with hQs
    set R35 := ⋃ f ∈ F, shift f (up (H₀ : Set (ι → ℕ))) with hR35
    have hmaps : ∀ p ∈ J, hd p + l p ∈ (Uni \ Qs) ∪ R35 := by
      intro p hp
      rcases hCB p hp with hl | hl | ⟨f, hf, hle⟩
      · refine Or.inl ⟨hUniOf p hp (Or.inl hl), ?_⟩
        rintro ⟨hz | hz, hnD⟩
        · exact hnot7 p hp (Or.inl hl) ⟨hz, hnD⟩
        · exact hnot8 p hp (Or.inl hl) ⟨hz, hnD⟩
      · refine Or.inl ⟨hUniOf p hp (Or.inr hl), ?_⟩
        rintro ⟨hz | hz, hnD⟩
        · exact hnot7 p hp (Or.inr hl) ⟨hz, hnD⟩
        · exact hnot8 p hp (Or.inr hl) ⟨hz, hnD⟩
      · exact Or.inr (mem_iUnion₂.2 ⟨f, hf, add_mem_shift_up (hhd p hp) hle⟩)
    have hsum := sum_le_W_of_mapsTo (r := r) J (fun p ↦ hd p + l p) hinj hmaps
    have hQsub : Qs ⊆ Uni := sdiff_subset.trans (union_subset hZ7Uni hZ8Uni)
    have hQsplit : W r Qs = Z7o + Z8o := by
      rw [hQs, union_sdiff_distrib, W_union_of_disjoint]
      rw [Set.disjoint_left]
      rintro z ⟨hz7, hnD⟩ ⟨hz8, -⟩
      obtain ⟨h, hh, -, rfl⟩ := hZ7mem z hz7
      obtain ⟨h', hh', -, heq⟩ := hZ8mem _ hz8
      exact hnD (apex_eq_mem_defect hH₀ hij ht hh hh' heq)
    have hR : W r R35 ≤ ε * U := by
      calc W r R35 ≤ ∑ f ∈ F, W r (shift f (up (H₀ : Set (ι → ℕ)))) := W_biUnion_le r F _
        _ = ε * U := by rw [hεdef, Finset.sum_mul]; simp only [W_shift]; rfl
    calc ν + Z7o + Z8o = ν + W r Qs := by rw [hQsplit, add_assoc]
      _ ≤ W r ((Uni \ Qs) ∪ R35) + W r Qs := by gcongr; exact hν.trans hsum
      _ ≤ W r (Uni \ Qs) + ε * U + W r Qs := by
          gcongr; exact (W_union_le _ _).trans (add_le_add le_rfl hR)
      _ = W r Uni + ε * U := by
          rw [add_right_comm, ← W_union_of_disjoint disjoint_sdiff_left,
            sdiff_union_of_subset hQsub]
  -- (g) the doubly-apexed points lie in `𝒟`
  have hOX : O ≤ X7 := W_mono fun z ⟨hz7, hz8⟩ ↦ by
    refine ⟨hz7, ?_⟩
    obtain ⟨h, hh, -, rfl⟩ := hZ7mem z hz7
    obtain ⟨h', hh', -, heq⟩ := hZ8mem _ hz8
    exact apex_eq_mem_defect hH₀ hij ht hh hh' heq
  -- finiteness and positivity
  have hane : a ≠ ⊤ := hr j
  have hbne : b ≠ ⊤ := ENNReal.pow_ne_top (hr i)
  have hZ7sne : Z7s ≠ ⊤ := ENNReal.sum_ne_top.2 fun h _ ↦ w_ne_top hr h
  have hUne : U ≠ ⊤ := ne_top_of_le_ne_top hPm (W_mono (subset_univ _))
  have hU0 : U ≠ 0 := by
    obtain ⟨h, hh⟩ := hne
    have : w r h * Pm ≤ U := by rw [hPmdef, ← W_Ici]; exact W_mono fun z hz ↦ ⟨h, hh, hz⟩
    exact (lt_of_lt_of_le (ENNReal.mul_pos (w_ne_zero hr0 h)
      (lt_of_lt_of_le one_pos one_le_W_univ).ne') this).ne'
  -- K3': the exact regions pay for the exact-7 apexes
  have hK3' : a₇ + a₈ + a * Z7s + b * a * U ≤ (b + a) * U :=
    calc a₇ + a₈ + a * Z7s + b * a * U ≤ a₇ + a₈ + (X7 + Z7o) + b * a * U := by gcongr
      _ ≤ a₇ + a₈ + (W r D + Z7o) + b * a * U := by gcongr
      _ = (a₇ + a₈ + Z7o) + W r D + b * a * U := by ring
      _ ≤ W r Uni + W r D + b * a * U := by gcongr
      _ = (b + a) * U := hIE
  -- (I'): the two union bounds
  have hI : 2 * U + Pm * (a * Z7s + b * a * U) ≤ Pm * ((b + a) * U) + Pm * Z7s + Pm * Z8s :=
    calc 2 * U + Pm * (a * Z7s + b * a * U)
        ≤ (Pm * a₇ + Pm * Z7s) + (Pm * a₈ + Pm * Z8s) + Pm * (a * Z7s + b * a * U) := by
          rw [two_mul]; gcongr
          · exact hUA.trans (by gcongr)
          · exact hUB.trans (by gcongr)
      _ = Pm * (a₇ + a₈ + a * Z7s + b * a * U) + Pm * Z7s + Pm * Z8s := by ring
      _ ≤ Pm * ((b + a) * U) + Pm * Z7s + Pm * Z8s := by gcongr
  -- the charge: `𝒟` pays for the apexes it absorbs
  have hch : γ * (a * Z7s) + b * Z8s ≤ W r D + Z7o + Z8o :=
    calc γ * (a * Z7s) + b * Z8s ≤ γ * (X7 + Z7o) + (Z8o + Y8 + O) := by gcongr
      _ ≤ (γ * X7 + Z7o) + (Z8o + Y8 + X7) := by
          rw [mul_add]; gcongr
          exact mul_le_of_le_one_left zero_le hγ1
      _ = ((1 + γ) * X7 + Y8) + Z7o + Z8o := by ring
      _ ≤ W r D + Z7o + Z8o := by gcongr
  -- (II'): every part
  have hII : U + Pm * (γ * (a * Z7s) + b * Z8s) + Pm * (b * a * U)
      ≤ Pm * ((b + a) * U + ε * U) :=
    calc U + Pm * (γ * (a * Z7s) + b * Z8s) + Pm * (b * a * U)
        ≤ Pm * ν + Pm * (W r D + Z7o + Z8o) + Pm * (b * a * U) := by gcongr
      _ = Pm * ((ν + Z7o + Z8o) + W r D + b * a * U) := by ring
      _ ≤ Pm * ((W r Uni + ε * U) + W r D + b * a * U) := by gcongr
      _ = Pm * ((W r Uni + W r D + b * a * U) + ε * U) := by ring
      _ = Pm * ((b + a) * U + ε * U) := by rw [hIE]
  -- multiply (I') by `b`, use `b ≤ ab + aγ`, cancel `ab·Pm·Z7s`
  have hIb : b * Pm * (a * Z7s) + (2 * b * U + b * Pm * (b * a * U))
      ≤ b * Pm * (a * Z7s) + (b * Pm * ((b + a) * U) + Pm * (γ * (a * Z7s) + b * Z8s)) := by
    have h1 : b * (2 * U + Pm * (a * Z7s + b * a * U))
        ≤ b * (Pm * ((b + a) * U) + Pm * Z7s + Pm * Z8s) := by gcongr
    have h2 : b * (Pm * Z7s) ≤ (a * b + a * γ) * (Pm * Z7s) := by gcongr
    calc b * Pm * (a * Z7s) + (2 * b * U + b * Pm * (b * a * U))
        = b * (2 * U + Pm * (a * Z7s + b * a * U)) := by ring
      _ ≤ b * (Pm * ((b + a) * U) + Pm * Z7s + Pm * Z8s) := h1
      _ = b * Pm * ((b + a) * U) + b * (Pm * Z7s) + b * Pm * Z8s := by ring
      _ ≤ b * Pm * ((b + a) * U) + (a * b + a * γ) * (Pm * Z7s) + b * Pm * Z8s := by gcongr
      _ = b * Pm * (a * Z7s) + (b * Pm * ((b + a) * U) + Pm * (γ * (a * Z7s) + b * Z8s)) := by ring
  have hfin : b * Pm * (a * Z7s) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hbne hPm) (ENNReal.mul_ne_top hane hZ7sne)
  have hIb' := ENNReal.le_of_add_le_add_left hfin hIb
  -- combine, and cancel `U`
  have hfinal : (2 * b + b * Pm * b * a + 1 + Pm * b * a) * U
      ≤ (b * Pm * (b + a) + Pm * (b + a + ε)) * U :=
    calc (2 * b + b * Pm * b * a + 1 + Pm * b * a) * U
        = (2 * b * U + b * Pm * (b * a * U)) + (U + Pm * (b * a * U)) := by ring
      _ ≤ (b * Pm * ((b + a) * U) + Pm * (γ * (a * Z7s) + b * Z8s)) + (U + Pm * (b * a * U)) := by
          gcongr
      _ = b * Pm * ((b + a) * U) + (U + Pm * (γ * (a * Z7s) + b * Z8s) + Pm * (b * a * U)) := by
          ring
      _ ≤ b * Pm * ((b + a) * U) + Pm * ((b + a) * U + ε * U) := by gcongr
      _ = (b * Pm * (b + a) + Pm * (b + a + ε)) * U := by ring
  exact (ENNReal.mul_le_mul_iff_left hU0 hUne).1 hfinal

end SevenClosure

end Erdos274
