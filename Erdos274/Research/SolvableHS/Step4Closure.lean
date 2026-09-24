/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.Research.SolvableHS.SevenJoin
import Erdos274.Arithmetic.PrimeOrder

/-!
# The step-4 closure at a general prime

`DECISION_LOG` D98 §3.  Let `F ◁ G`, `p` the largest prime of `|G|`, and
suppose every non-universal part has `p ∣ ℓⱼ` or `q^{ord_p q} ∣ ℓⱼ` for a prime
`q < p` (for `F = KQ` this is (CB), `SevenCB.cb_loc`).  Put `U = up{v(hⱼ)}`
and `ν = Σ_{non-universal} 1/dⱼ`.  Then:

* every non-universal `v(dⱼ) = v(hⱼ) + v(ℓⱼ)` lies in `A ∪ ⋃_q B_q`, with
  `A = U + e_p` and `B_q = U + f_q e_q`;
* the indices are distinct, so `ν ≤ W(A ∪ ⋃ B_q)`;
* `B_q` contains `C_q = U + e_p + f_q e_q ⊆ A`, so only `B_q ∖ C_q` is new:
  `W(A ∪ ⋃ B_q) ≤ (1/p + (1 − 1/p)·Σ_q q^{−f_q})·W(U)` (`union_shift_bound`);
* Lemma O: `W(U) ≤ Π·ν`, with `Π = ∏_{q ∣ |G|} q/(q−1) ≤ Π_p·p/(p−1)`.

So `ν ≤ Π_p·(1/(p−1) + S_p)·ν`, and **`Π_p·(S_p + 1/(p−1)) < 1` refutes the
covering** (`false_of_covering`).  This is D98's `Δ₁⁴ < 1` with the exact
`δ_p` replaced by `S_p ≥ δ_p`, and it needs no (SNBU): the only correlation
used is the inclusion `C_q ⊆ A ∩ B_q`.  At `p = 5` it gives `1263/1296 < 1`,
where the plain union bound (`1781/1728`) does not close; D98 §6's caveat
that `p = 5` needs (SNBU) is therefore withdrawn.
-/

namespace Erdos274

namespace Step4Closure

open Set QuotientShadow ExpWeight ApexCharging DivisorWeight SevenJoin SevenClosure PrimeOrder
open scoped ENNReal NNReal

universe u v

/-! ### The refined union bound -/

section Abstract

variable {ι κ α : Type*} [Fintype ι]

omit [Fintype ι] in
theorem shift_add_subset (H : Set (ι → ℕ)) (e f : ι → ℕ) :
    shift (e + f) (up H) ⊆ shift f (up H) ∩ shift e (up H) := by
  intro z hz
  obtain ⟨h, hh, hle⟩ := mem_shift_up.1 hz
  refine ⟨mem_shift_up.2 ⟨h, hh, le_trans ?_ hle⟩, mem_shift_up.2 ⟨h, hh, le_trans ?_ hle⟩⟩
  · exact add_le_add le_rfl le_add_self
  · exact add_le_add le_rfl le_self_add

/-- **The refined union bound.**  If distinct points `g j` lie in
`(U + e₀) ∪ ⋃ₐ (U + eₐ)`, then
`∑ⱼ w(gⱼ) + ∑ₐ w(e₀)w(eₐ)W(U) ≤ (w(e₀) + ∑ₐ w(eₐ))·W(U)`: the part of
`U + eₐ` inside `U + e₀ + eₐ ⊆ U + e₀` is not counted twice. -/
theorem union_shift_bound (r : ι → ℝ≥0∞) (H : Set (ι → ℕ)) (e₀ : ι → ℕ) (s : Finset α)
    (e : α → ι → ℕ) (J : Finset κ) (g : κ → ι → ℕ) (hinj : Set.InjOn g J)
    (hg : ∀ j ∈ J, g j ∈ shift e₀ (up H) ∪ ⋃ a ∈ s, shift (e a) (up H)) :
    ∑ j ∈ J, w r (g j) + ∑ a ∈ s, w r e₀ * w r (e a) * W r (up H) ≤
      (w r e₀ + ∑ a ∈ s, w r (e a)) * W r (up H) := by
  classical
  set U := up H with hU
  set A := shift e₀ U with hA
  set B : α → Set (ι → ℕ) := fun a ↦ shift (e a) U with hB
  set Cc : α → Set (ι → ℕ) := fun a ↦ shift (e₀ + e a) U with hCc
  have hC : ∀ a, Cc a ⊆ B a ∩ A := fun a ↦ shift_add_subset H e₀ (e a)
  have hX : ∀ j ∈ J, g j ∈ A ∪ ⋃ a ∈ s, (B a \ Cc a) := by
    intro j hj
    rcases hg j hj with h | h
    · exact Or.inl h
    · obtain ⟨a, ha, hga⟩ := mem_iUnion₂.1 h
      by_cases hc : g j ∈ Cc a
      · exact Or.inl (hC a hc).2
      · exact Or.inr (mem_iUnion₂.2 ⟨a, ha, hga, hc⟩)
  have hWC : ∀ a, W r (Cc a) = w r e₀ * w r (e a) * W r U := fun a ↦ by
    simp only [hCc, W_shift, w_add]
  have hWB : ∀ a, W r (B a \ Cc a) + W r (Cc a) = W r (B a) := fun a ↦ by
    rw [← W_union_of_disjoint disjoint_sdiff_left,
      sdiff_union_of_subset fun z hz ↦ (hC a hz).1]
  calc ∑ j ∈ J, w r (g j) + ∑ a ∈ s, w r e₀ * w r (e a) * W r U
      ≤ W r (A ∪ ⋃ a ∈ s, (B a \ Cc a)) + ∑ a ∈ s, W r (Cc a) := by
        gcongr with a ha
        · exact sum_le_W_of_mapsTo J g hinj hX
        · rw [hWC]
    _ ≤ (W r A + ∑ a ∈ s, W r (B a \ Cc a)) + ∑ a ∈ s, W r (Cc a) := by
        gcongr
        exact (W_union_le _ _).trans (add_le_add le_rfl (W_biUnion_le r s _))
    _ = W r A + ∑ a ∈ s, W r (B a) := by
        rw [add_assoc, ← Finset.sum_add_distrib]
        simp only [hWB]
    _ = (w r e₀ + ∑ a ∈ s, w r (e a)) * W r U := by
        simp only [hA, hB, W_shift, add_mul, Finset.sum_mul]

end Abstract

/-! ### The arithmetic of the constants -/

section Constants

/-- `∏_{q ∈ Q} (1 − 1/q)⁻¹ ≤ Π_p·p/(p−1)` for a set of primes `q ≤ p`. -/
theorem prod_le_piBelow {p : ℕ} (hp : p.Prime) {Q : Finset ℕ}
    (hQ : ∀ x ∈ Q, x.Prime ∧ x ≤ p) :
    ∏ x ∈ Q, (1 - (x : ℝ)⁻¹)⁻¹ ≤ (piBelow p : ℝ) * ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hsub : Q ⊆ insert p p.primesBelow := by
    intro x hx
    obtain ⟨hxp, hle⟩ := hQ x hx
    rcases hle.lt_or_eq with hlt | rfl
    · exact Finset.mem_insert_of_mem (Nat.mem_primesBelow.mpr ⟨hlt, hxp⟩)
    · exact Finset.mem_insert_self _ _
  have hprime : ∀ x ∈ insert p p.primesBelow, x.Prime := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hp
    · exact Nat.prime_of_mem_primesBelow hx
  have hle : ((mertensProd Q : ℚ) : ℝ) ≤ ((mertensProd (insert p p.primesBelow) : ℚ) : ℝ) :=
    Rat.cast_le.mpr (mertensProd_le_of_subset hprime hsub)
  have hnot : p ∉ p.primesBelow := fun h ↦ lt_irrefl p (Nat.lt_of_mem_primesBelow h)
  have hL : ∏ x ∈ Q, (1 - (x : ℝ)⁻¹)⁻¹ = ((mertensProd Q : ℚ) : ℝ) := by
    rw [mertensProd, Rat.cast_prod]
    refine Finset.prod_congr rfl fun x hx ↦ ?_
    have hx1 : (1 : ℝ) < x := by exact_mod_cast (hQ x hx).1.one_lt
    push_cast
    field_simp
  have hR : ((mertensProd (insert p p.primesBelow) : ℚ) : ℝ) =
      (piBelow p : ℝ) * ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [mertensProd, Finset.prod_insert hnot, piBelow_def, mertensProd]
    push_cast
    ring
  rw [hL, ← hR]
  exact hle

/-- `∑_{q ∈ Q} q^{−ord_p q} ≤ S_p` for a set of primes `q < p`. -/
theorem sum_le_sOrd {p : ℕ} {Q : Finset ℕ} (hQ : ∀ x ∈ Q, x.Prime ∧ x < p) :
    ∑ x ∈ Q, ((x : ℝ) ^ ordMod p x)⁻¹ ≤ (sOrd p : ℝ) := by
  have hsub : Q ⊆ p.primesBelow := fun x hx ↦
    Nat.mem_primesBelow.mpr ⟨(hQ x hx).2, (hQ x hx).1⟩
  rw [sOrd_def]
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity

end Constants

/-! ### The join -/

section Join

variable {G : Type u} [Group G] [Fintype G] {κ : Type v} [Fintype κ]
  (C : Group.ExactCovering G κ) (F : Subgroup G)

omit [Fintype G] in
/-- **The step-4 closure at a general prime.**  If every non-universal local
index is divisible by `p` or by `q^{ord_p q}` for a prime `q < p`, and
`Π_p·(S_p + 1/(p−1)) < 1`, there is no non-universal part: the hypotheses
are the setting (`p` the largest prime of `|G|`, distinct non-universal
indices, one of them) and (CB). -/
theorem false_of_covering [Finite G] [Group.IsSolvable G] [F.Normal] {p : ℕ}
    [hp : Fact p.Prime]
    (hpG : p ∣ Nat.card G) (hG : ∀ q, q.Prime → q ∣ Nat.card G → q ≤ p)
    (hdist : Set.InjOn (fun j ↦ (C.parts j).index) (nonUniv C F))
    (hne : (nonUniv C F).Nonempty)
    (hCB : ∀ j ∈ nonUniv C F, p ∣ loc C F j ∨
      ∃ q, q.Prime ∧ q < p ∧ q ^ ordMod p q ∣ loc C F j)
    (hcrit : piBelow p * (sOrd p + 1 / ((p : ℚ) - 1)) < 1) : False := by
  classical
  have := Fintype.ofFinite G
  set n := Nat.card G with hndef
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  -- the prime coordinates
  let ι := {x // x ∈ n.primeFactors}
  let q : ι → ℕ := Subtype.val
  have hq : ∀ i, (q i).Prime := fun i ↦ Nat.prime_of_mem_primeFactors i.2
  have hqi : Function.Injective q := Subtype.val_injective
  have hsm : Smooth q n := ⟨hn0, fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hsmn : Smooth q F.index := hsm.of_dvd F.index_dvd_card
  have hsmh : ∀ j, Smooth q (head C F j) := fun j ↦ hsmn.of_dvd (head_dvd_index C F j)
  have hsml : ∀ j, Smooth q (loc C F j) := fun j ↦ hsm.of_dvd (loc_dvd_card C F j)
  have hsmd : ∀ j, Smooth q ((C.parts j).index) := fun j ↦
    hsm.of_dvd (C.parts j).index_dvd_card
  -- the data
  set J := nonUniv C F with hJdef
  set hd : κ → ι → ℕ := fun j ↦ vec q (head C F j) with hhd_def
  set l : κ → ι → ℕ := fun j ↦ vec q (loc C F j) with hl_def
  have hdl : ∀ j, hd j + l j = vec q ((C.parts j).index) := fun j ↦ by
    rw [index_eq_head_mul_loc C F j, vec_mul (hsmh j).1 (hsml j).1]
  have hwd : ∀ j, w (ratio q) (hd j + l j) = ((((C.parts j).index : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    fun j ↦ by rw [hdl, w_vec hq hqi (hsmd j)]
  set νN : ℝ≥0 := ∑ j ∈ J, ((C.parts j).index : ℝ≥0)⁻¹ with hνN
  have hνsum : ∑ j ∈ J, w (ratio q) (hd j + l j) = (νN : ℝ≥0∞) := by
    rw [hνN, ENNReal.ofNNReal_finsetSum]
    exact Finset.sum_congr rfl fun j _ ↦ hwd j
  have hmemJ : ∀ {j}, j ∈ J → ¬ F ≤ C.parts j := fun hj ↦ (Finset.mem_filter.mp hj).2
  have hmeet : ∀ {j k δ}, j ∈ J → δ ∈ shadow C F j → δ ∈ shadow C F k → k ∈ J :=
    fun hj hδj hδk ↦ Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, not_le_of_meet C F (hmemJ hj) hδj hδk⟩
  -- Lemma O: `W(U) ≤ Π·ν`
  set HS := J.image hd with hHS
  have hLO : W (ratio q) (up (HS : Set (ι → ℕ))) ≤ (PiN q : ℝ≥0∞) * νN := by
    have hH : ∀ h ∈ J.image (head C F), h ∣ F.index := by
      intro h hh
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hh
      exact head_dvd_index C F j
    have himg : (J.image (head C F)).image (F.index / ·) = J.image (sz C F) := by
      rw [Finset.image_image]
      exact Finset.image_congr fun j _ ↦ index_div_head C F j
    have hμ := divisorMass_le_ncard_shadows C F J
    rw [← himg] at hμ
    have hHS' : HS = (J.image (head C F)).image (vec q) := by
      rw [hHS, Finset.image_image]
      rfl
    rw [hHS']
    calc W (ratio q) (up (((J.image (head C F)).image (vec q) : Finset (ι → ℕ)) :
            Set (ι → ℕ)))
        ≤ (PiN q : ℝ≥0∞) * (((((⋃ j ∈ J, shadow C F j).ncard : ℝ≥0) / F.index : ℝ≥0)) :
            ℝ≥0∞) := by
          refine (W_up_heads_le hq hqi hsmn _ hH hμ).trans (le_of_eq ?_)
          rw [coe_div_nat _ _ F.index_ne_zero_of_finite, mul_div_assoc]
      _ ≤ (PiN q : ℝ≥0∞) * νN := by
          gcongr
          refine ncard_div_le C F _ _ (card_mul_ncard_le_of_meet C F _ _ fun k δ hδ hδk ↦ ?_)
          obtain ⟨j, hj, hδj⟩ := Set.mem_iUnion₂.mp hδ
          exact hmeet hj hδj hδk
  -- the shifts
  have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.out, hpG, hn0⟩
  have hsp : Smooth q p := hsm.of_dvd hpG
  set e₀ := vec q p with he₀
  set s : Finset ι := Finset.univ.filter fun i ↦ q i < p with hs
  set e : ι → ι → ℕ := fun i ↦ vec q (q i ^ ordMod p (q i)) with he
  have hse : ∀ i, Smooth q (q i ^ ordMod p (q i)) := fun i ↦ smooth_pow hq i _
  have hg : ∀ j ∈ J, hd j + l j ∈ shift e₀ (up (HS : Set (ι → ℕ))) ∪
      ⋃ i ∈ s, shift (e i) (up (HS : Set (ι → ℕ))) := by
    intro j hj
    have hhd : hd j ∈ up (HS : Set (ι → ℕ)) :=
      mem_up_of_mem (Finset.mem_coe.mpr (Finset.mem_image_of_mem hd hj))
    rcases hCB j hj with h | ⟨q', hq', hq'p, hdvd⟩
    · exact Or.inl (add_mem_shift_up hhd ((vec_le_iff hsp (hsml j).1).mpr h))
    · have hord : 0 < ordMod p q' :=
        ordMod_pos hp.out (Nat.not_dvd_of_pos_of_lt hq'.pos hq'p)
      have hq'n : q' ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq',
        ((dvd_pow_self q' hord.ne').trans hdvd).trans (loc_dvd_card C F j), hn0⟩
      refine Or.inr (mem_iUnion₂.2 ⟨⟨q', hq'n⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq'p⟩,
        add_mem_shift_up hhd ((vec_le_iff (hse ⟨q', hq'n⟩) (hsml j).1).mpr hdvd)⟩)
  have hinj : Set.InjOn (fun j ↦ hd j + l j) J := by
    intro a ha b hb h
    simp only [hdl] at h
    exact hdist ha hb (vec_injOn hq hqi (hsmd a) (hsmd b) h)
  have hkey := union_shift_bound (ratio q) (HS : Set (ι → ℕ)) e₀ s e J
    (fun j ↦ hd j + l j) hinj hg
  -- everything is finite
  set W₀ := W (ratio q) (up (HS : Set (ι → ℕ))) with hW₀
  have hW₀top : W₀ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hLO
  obtain ⟨WN, hWN⟩ : ∃ WN : ℝ≥0, W₀ = WN := ⟨W₀.toNNReal, (ENNReal.coe_toNNReal hW₀top).symm⟩
  have hw₀ : w (ratio q) e₀ = (((p : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := w_vec hq hqi hsp
  have hwe : ∀ i, w (ratio q) (e i) =
      ((((q i ^ ordMod p (q i) : ℕ) : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) := fun i ↦ w_vec hq hqi (hse i)
  simp only [hνsum, hw₀, hwe, hWN] at hkey
  rw [hWN] at hLO
  norm_cast at hkey hLO
  -- to the reals
  have hkeyR := NNReal.coe_le_coe.mpr hkey
  have hLOR := NNReal.coe_le_coe.mpr hLO
  push_cast at hkeyR hLOR
  set S : ℝ := ∑ i ∈ s, ((q i : ℝ) ^ ordMod p (q i))⁻¹ with hS
  set νR : ℝ := (νN : ℝ) with hνR
  set Pr : ℝ := (PiN q : ℝ) with hPr
  have hk : νR + (p : ℝ)⁻¹ * S * WN ≤ ((p : ℝ)⁻¹ + S) * WN := by
    rw [hS, Finset.mul_sum, Finset.sum_mul]
    exact hkeyR
  -- the constants
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hPi : Pr ≤ (piBelow p : ℝ) * ((p : ℝ) / ((p : ℝ) - 1)) := by
    have h := prod_le_piBelow hp.out (Q := n.primeFactors) fun x hx ↦
      ⟨Nat.prime_of_mem_primeFactors hx,
        hG x (Nat.prime_of_mem_primeFactors hx) (Nat.dvd_of_mem_primeFactors hx)⟩
    refine le_of_eq_of_le ?_ h
    rw [hPr, PiN, NNReal.coe_prod]
    rw [← Finset.prod_coe_sort n.primeFactors]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [NNReal.coe_inv, coe_one_sub_ratioN hq i]
  have hSle : S ≤ (sOrd p : ℝ) := by
    have h := sum_le_sOrd (p := p) (Q := n.primeFactors.filter (· < p)) fun x hx ↦
      ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    refine le_of_eq_of_le ?_ h
    rw [hS, hs, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_coe_sort n.primeFactors]
  have hcritR : (piBelow p : ℝ) * ((sOrd p : ℝ) + 1 / ((p : ℝ) - 1)) < 1 := by
    exact_mod_cast hcrit
  -- `ν > 0`
  have hνpos : 0 < νR := by
    rw [hνR, hνN, NNReal.coe_sum]
    exact Finset.sum_pos (fun i _ ↦ by
      have : (0 : ℝ) < (C.parts i).index := by
        exact_mod_cast Nat.pos_of_ne_zero (C.parts i).index_ne_zero_of_finite
      push_cast
      positivity) hne
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hW0 : (0 : ℝ) ≤ WN := WN.2
  have hPi0 : 0 ≤ (piBelow p : ℝ) := by exact_mod_cast piBelow_nonneg p
  -- `ν ≤ (1/p + (1 − 1/p)S)·W(U)`
  have hν1 : νR ≤ ((p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * S) * WN := by nlinarith
  have hc0 : 0 ≤ (p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * S := by
    have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1.le
    have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith
  have hcPr : ((p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * S) * Pr < 1 := by
    have hpS : (p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * S ≤ (p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * (sOrd p : ℝ) := by
      have : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
        have := inv_le_one_of_one_le₀ hp1.le; linarith
      nlinarith
    have hPr0 : 0 ≤ Pr := NNReal.coe_nonneg _
    calc ((p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * S) * Pr
        ≤ ((p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * (sOrd p : ℝ)) *
            ((piBelow p : ℝ) * ((p : ℝ) / ((p : ℝ) - 1))) := by
          apply mul_le_mul hpS hPi hPr0
          have := sOrd_nonneg p
          have : (0 : ℝ) ≤ (sOrd p : ℝ) := by exact_mod_cast this
          have : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
            have := inv_le_one_of_one_le₀ hp1.le; linarith
          positivity
      _ = (piBelow p : ℝ) * ((sOrd p : ℝ) + 1 / ((p : ℝ) - 1)) := by
          have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have h2 : (p : ℝ) ≠ 0 := by linarith
          field_simp
          ring
      _ < 1 := hcritR
  have hWle : (WN : ℝ) ≤ Pr * νR := hLOR
  nlinarith [mul_le_mul_of_nonneg_left hWle hc0]

end Join

end Step4Closure

end Erdos274
