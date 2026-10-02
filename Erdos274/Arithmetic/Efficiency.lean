/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.Arithmetic.DivisorMass
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring


/-!
# Lemma E: the Mertens efficiency bound

`SOLVABLE_HS_TRACK.md` §9.14.  For a set `Q` of primes put
`M(Q) = Π_{q ∈ Q} q/(q−1)`.  If every `s ∈ R` is positive with all prime
factors in `Q`, then

    Σ_{s ∈ R} s  ≤  M(Q) · μ(D(R)).

That is, the efficiency `c = Σ_R s / μ(D(R))` of Lemma O is at most `M(Q)`
(Sun 2004's product), rather than BFF's crude `p − 1`.

**Proof.**  `φ(s) = s · Π_{q ∣ s} (1 − 1/q)` and `(q/(q−1))(1 − 1/q) = 1`, so
`M(Q) φ(s) = s · Π_{q ∈ Q, q ∤ s} q/(q−1) ≥ s`.  Sum over `R`, and use
`R ⊆ D(R)`, so `Σ_R φ(s) ≤ μ(D(R))`.

No research axiom occurs in this file.
-/

@[expose] public section

namespace Erdos274

open Finset

/-- `M(Q) = Π_{q ∈ Q} q/(q−1)`. -/
noncomputable def mertensProd (Q : Finset ℕ) : ℚ := ∏ q ∈ Q, (q : ℚ) / (q - 1)

lemma mertensProd_factor_nonneg {q : ℕ} (hq : q.Prime) : 0 ≤ (q : ℚ) / (q - 1) := by
  have : (2 : ℚ) ≤ q := by exact_mod_cast hq.two_le
  apply div_nonneg <;> linarith

lemma one_le_mertensProd_factor {q : ℕ} (hq : q.Prime) : 1 ≤ (q : ℚ) / (q - 1) := by
  have : (2 : ℚ) ≤ q := by exact_mod_cast hq.two_le
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma one_le_mertensProd_factor_of_two_le {q : ℕ} (hq : 2 ≤ q) :
    1 ≤ (q : ℚ) / (q - 1) := by
  have hq' : (2 : ℚ) ≤ q := by exact_mod_cast hq
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma mertensProd_nonneg {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) : 0 ≤ mertensProd Q :=
  Finset.prod_nonneg fun q hq ↦ mertensProd_factor_nonneg (hQ q hq)

theorem mertensProd_le_of_subset_two_le {Q Q' : Finset ℕ} (hQ' : ∀ q ∈ Q', 2 ≤ q)
    (hsub : Q ⊆ Q') : mertensProd Q ≤ mertensProd Q' := by
  have hrest : 1 ≤ ∏ q ∈ Q' \ Q, (q : ℚ) / (q - 1) := by
    refine Finset.prod_induction _ (fun x : ℚ ↦ 1 ≤ x)
      (fun a b ha hb ↦ one_le_mul_of_one_le_of_one_le ha hb) le_rfl ?_
    intro q hq
    exact one_le_mertensProd_factor_of_two_le (hQ' q (Finset.mem_sdiff.mp hq).1)
  have hQ0 : 0 ≤ mertensProd Q :=
    Finset.prod_nonneg fun q hq ↦
      (le_trans (by norm_num) (one_le_mertensProd_factor_of_two_le (hQ' q (hsub hq))))
  have hsplit : (∏ q ∈ Q' \ Q, (q : ℚ) / (q - 1)) * mertensProd Q = mertensProd Q' :=
    Finset.prod_sdiff hsub
  nlinarith

/-- `s ≤ M(Q) · φ(s)` when every prime factor of `s` lies in `Q`. -/
theorem le_mertensProd_mul_totient {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {s : ℕ}
    (hsQ : s.primeFactors ⊆ Q) : (s : ℚ) ≤ mertensProd Q * s.totient := by
  have hcancel : ∀ q ∈ s.primeFactors, (q : ℚ) / (q - 1) * (1 - (q : ℚ)⁻¹) = 1 := by
    intro q hq
    have h2 : (2 : ℚ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le
    have hq1 : (q : ℚ) - 1 ≠ 0 := by linarith
    have hq0 : (q : ℚ) ≠ 0 := by linarith
    field_simp
  have hsplit : mertensProd Q =
      (∏ q ∈ Q \ s.primeFactors, (q : ℚ) / (q - 1)) *
        ∏ q ∈ s.primeFactors, (q : ℚ) / (q - 1) :=
    (Finset.prod_sdiff hsQ).symm
  have hrest : 1 ≤ ∏ q ∈ Q \ s.primeFactors, (q : ℚ) / (q - 1) := by
    refine Finset.prod_induction _ (fun x : ℚ ↦ 1 ≤ x)
      (fun a b ha hb ↦ one_le_mul_of_one_le_of_one_le ha hb) le_rfl ?_
    intro q hq
    exact one_le_mertensProd_factor (hQ q (Finset.mem_sdiff.mp hq).1)
  have hkey : mertensProd Q * s.totient =
      (∏ q ∈ Q \ s.primeFactors, (q : ℚ) / (q - 1)) * s := by
    rw [Nat.totient_eq_mul_prod_factors, hsplit]
    have hone : (∏ q ∈ s.primeFactors, (q : ℚ) / (q - 1)) *
        ∏ q ∈ s.primeFactors, (1 - (q : ℚ)⁻¹) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one hcancel
    calc (∏ q ∈ Q \ s.primeFactors, (q : ℚ) / (q - 1)) *
          (∏ q ∈ s.primeFactors, (q : ℚ) / (q - 1)) *
          ((s : ℚ) * ∏ q ∈ s.primeFactors, (1 - (q : ℚ)⁻¹))
        = (∏ q ∈ Q \ s.primeFactors, (q : ℚ) / (q - 1)) * s *
          ((∏ q ∈ s.primeFactors, (q : ℚ) / (q - 1)) *
            ∏ q ∈ s.primeFactors, (1 - (q : ℚ)⁻¹)) := by ring
      _ = (∏ q ∈ Q \ s.primeFactors, (q : ℚ) / (q - 1)) * s := by rw [hone, mul_one]
  rw [hkey]
  have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg s
  nlinarith

/-- `M(·)` is monotone in the prime set: every factor `q/(q−1)` is at least `1`,
so enlarging the set of primes enlarges the product.

This is what licenses replacing `M_G′ = M(primes of |G| other than p)` by
`Π_p = M(primes below p)` when `p` is the largest prime divisor of `|G|`. -/
theorem mertensProd_le_of_subset {Q Q' : Finset ℕ} (hQ' : ∀ q ∈ Q', q.Prime)
    (hsub : Q ⊆ Q') : mertensProd Q ≤ mertensProd Q' :=
  mertensProd_le_of_subset_two_le (fun q hq ↦ (hQ' q hq).two_le) hsub

/-- **Lemma E.**  If every `s ∈ R` is positive with prime factors in `Q`, then
`Σ_{s ∈ R} s ≤ M(Q) · μ(D(R))`. -/
theorem sum_le_mertensProd_mul_divisorMass {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime)
    {R : Finset ℕ} (hR : ∀ s ∈ R, 0 < s ∧ s.primeFactors ⊆ Q) :
    ∑ s ∈ R, (s : ℚ) ≤ mertensProd Q * divisorMass R := by
  have hRD : R ⊆ divisorClosure R := by
    intro s hs
    exact Finset.mem_biUnion.mpr
      ⟨s, hs, Nat.mem_divisors.mpr ⟨dvd_rfl, (hR s hs).1.ne'⟩⟩
  calc ∑ s ∈ R, (s : ℚ) ≤ ∑ s ∈ R, mertensProd Q * s.totient :=
        Finset.sum_le_sum fun s hs ↦ le_mertensProd_mul_totient hQ (hR s hs).2
    _ = mertensProd Q * (mass R : ℚ) := by
        rw [← Finset.mul_sum]
        simp [mass]
    _ ≤ mertensProd Q * divisorMass R := by
        apply mul_le_mul_of_nonneg_left _ (mertensProd_nonneg hQ)
        exact_mod_cast mass_mono hRD

end Erdos274
