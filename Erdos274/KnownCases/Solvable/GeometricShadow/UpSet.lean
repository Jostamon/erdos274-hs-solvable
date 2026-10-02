/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.Arithmetic.DivisorMass
public import Mathlib.NumberTheory.Divisors


/-! # Divisor-closed events for truncated geometric weights -/

@[expose] public section

namespace Erdos274
namespace GeometricShadow

open Finset
open Classical in
/-- The event `Z ∈ U` of §9.22 §2, realised on the sample space `r.divisors`:
those `d ∣ r` dividing one of the shadow sizes `s ∈ S`. -/
noncomputable def upSet (r : ℕ) (S : Finset ℕ) : Finset ℕ :=
  r.divisors.filter fun d ↦ ∃ s ∈ S, d ∣ s

theorem mem_upSet {r d : ℕ} {S : Finset ℕ} :
    d ∈ upSet r S ↔ d ∈ r.divisors ∧ ∃ s ∈ S, d ∣ s := by
  classical
  simp only [upSet, Finset.mem_filter]

/-- The event is the divisor closure of the shadow sizes — which is exactly
what `divisorMass` measures. -/
theorem upSet_eq_divisorClosure {r : ℕ} {S : Finset ℕ} (hr : r ≠ 0)
    (hS : ∀ s ∈ S, s ∣ r) : upSet r S = divisorClosure S := by
  ext d
  simp only [mem_upSet, divisorClosure, Finset.mem_biUnion]
  constructor
  · rintro ⟨-, s, hsS, hds⟩
    refine ⟨s, hsS, Nat.mem_divisors.mpr ⟨hds, ?_⟩⟩
    rintro rfl
    exact hr (Nat.eq_zero_of_zero_dvd (hS 0 hsS))
  · rintro ⟨s, hsS, hd⟩
    rw [Nat.mem_divisors] at hd
    exact ⟨Nat.mem_divisors.mpr ⟨hd.1.trans (hS s hsS), hr⟩, s, hsS, hd.1⟩

/-- The event is upward closed in the geometric coordinates `y = v(r) − v(d)`,
i.e. downward closed under divisibility of `d`. -/
theorem upSet_dvd_closed {r d e : ℕ} {S : Finset ℕ} (hd : d ∈ upSet r S) (he : e ∣ d) :
    e ∈ upSet r S := by
  rw [mem_upSet] at hd ⊢
  obtain ⟨hdr, s, hsS, hds⟩ := hd
  rw [Nat.mem_divisors] at hdr
  exact ⟨Nat.mem_divisors.mpr ⟨he.trans hdr.1, hdr.2⟩, s, hsS, he.trans hds⟩

/-- The event in head form: with `sⱼ = r / hⱼ`, the event `Z ∈ U` is
`∃ j, hⱼ · d ∣ r`, manifestly the upward closure of the `v(hⱼ)`. -/
theorem mem_upSet_heads {r d : ℕ} {H : Finset ℕ} (hr : r ≠ 0) (hH : ∀ h ∈ H, h ∣ r) :
    d ∈ upSet r (H.image fun h ↦ r / h) ↔ d ∣ r ∧ ∃ h ∈ H, h * d ∣ r := by
  rw [mem_upSet, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdr, -⟩, s, hs, hds⟩
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨hdr, h, hh, (Nat.dvd_div_iff_mul_dvd (hH h hh)).mp hds⟩
  · rintro ⟨hdr, h, hh, hhd⟩
    exact ⟨⟨hdr, hr⟩, r / h, Finset.mem_image_of_mem _ hh,
      (Nat.dvd_div_iff_mul_dvd (hH h hh)).mpr hhd⟩


end GeometricShadow
end Erdos274
