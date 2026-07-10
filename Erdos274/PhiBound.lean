/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Star.Basic

/-!
# Totient bounds for the Herzog–Schönheim conjecture, abelian case

Two arithmetic ingredients of the Berger–Felzenbaum–Fraenkel argument
(see `docs/erdos274/BLUEPRINT.md`):

* `Erdos274.le_mul_totient`: if every prime factor of `d` is at most `M`,
  then `d ≤ M * φ(d)`;
* `Erdos274.sum_totient_biUnion_le`: regrouping a totient sum over the
  divisors of the numbers `m j * p ^ a j` (with `p ∤ m j`) by `p`-free part.
-/

namespace Erdos274

open Finset

/-- All positive divisors of at least one member of `R`. -/
def divisorClosure (R : Finset ℕ) : Finset ℕ := R.biUnion Nat.divisors

/-- Totient mass of a finite set of natural numbers. -/
def mass (S : Finset ℕ) : ℕ := ∑ d ∈ S, d.totient

/-- Divisor mass of a finite set of sizes. -/
def divisorMass (R : Finset ℕ) : ℕ := mass (divisorClosure R)

/-- Blueprint notation for divisor mass. -/
abbrev μ : Finset ℕ → ℕ := divisorMass

@[simp] lemma divisorClosure_empty : divisorClosure ∅ = ∅ := by
  simp [divisorClosure]

@[simp] lemma mass_empty : mass ∅ = 0 := by simp [mass]

@[simp] lemma divisorMass_empty : divisorMass ∅ = 0 := by simp [divisorMass]

@[simp] lemma divisorClosure_singleton (m : ℕ) :
    divisorClosure {m} = m.divisors := by simp [divisorClosure]

/-- Gauss's totient identity says that a singleton size has mass equal to
that size. -/
@[simp] lemma divisorMass_singleton (m : ℕ) : divisorMass {m} = m := by
  simp [divisorMass, mass, Nat.sum_totient]

/-- The scaling identity for a singleton family. -/
lemma divisorMass_mul_singleton (k m : ℕ) :
    divisorMass {k * m} = k * divisorMass {m} := by simp

/-- Divisor closure is monotone. -/
lemma divisorClosure_mono {R T : Finset ℕ} (hRT : R ⊆ T) :
    divisorClosure R ⊆ divisorClosure T := by
  intro d hd
  obtain ⟨m, hmR, hdm⟩ := Finset.mem_biUnion.mp hd
  exact Finset.mem_biUnion.mpr ⟨m, hRT hmR, hdm⟩

/-- Totient mass is monotone under inclusion. -/
lemma mass_mono {S T : Finset ℕ} (hST : S ⊆ T) : mass S ≤ mass T := by
  exact Finset.sum_le_sum_of_subset hST

/-- Divisor mass is monotone under inclusion of size sets. -/
lemma divisorMass_mono {R T : Finset ℕ} (hRT : R ⊆ T) :
    divisorMass R ≤ divisorMass T :=
  mass_mono (divisorClosure_mono hRT)

/-- Totient mass is subadditive over a union. -/
lemma mass_union_le (S T : Finset ℕ) : mass (S ∪ T) ≤ mass S + mass T := by
  classical
  have hdis : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hunion : S ∪ T = S ∪ (T \ S) := by ext x; simp
  rw [mass, hunion, Finset.sum_union hdis, mass, mass]
  exact Nat.add_le_add_left
    (Finset.sum_le_sum_of_subset (show T \ S ⊆ T from Finset.sdiff_subset)) _

/-- Splitting a set into a difference and an intersection splits its mass. -/
lemma mass_sdiff_add_mass_inter (S T : Finset ℕ) :
    mass (S \ T) + mass (S ∩ T) = mass S := by
  classical
  rw [mass, mass, mass, ← Finset.sum_union (Finset.disjoint_sdiff_inter S T),
    Finset.sdiff_union_inter]

/-- Inclusion–exclusion for totient mass. -/
lemma mass_union_add_mass_inter (S T : Finset ℕ) :
    mass (S ∪ T) + mass (S ∩ T) = mass S + mass T := by
  classical
  have hu : mass (S ∪ T) = mass S + mass (T \ S) := by
    rw [mass, mass, mass, show S ∪ T = S ∪ (T \ S) from by ext x; simp,
      Finset.sum_union Finset.disjoint_sdiff]
  rw [hu, add_assoc, Finset.inter_comm S T, mass_sdiff_add_mass_inter]

/-- Totient mass is subadditive over a finite indexed union. -/
lemma mass_biUnion_le {I : Type*} (s : Finset I)
    (F : I → Finset ℕ) : mass (s.biUnion F) ≤ ∑ i ∈ s, mass (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (mass_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- Divisor closure turns a union of size sets into a union. -/
lemma divisorClosure_union (R T : Finset ℕ) :
    divisorClosure (R ∪ T) = divisorClosure R ∪ divisorClosure T := by
  ext d
  simp [divisorClosure, or_and_right, exists_or]

/-- Divisor mass is subadditive over a union of size sets. -/
lemma divisorMass_union_le (R T : Finset ℕ) :
    divisorMass (R ∪ T) ≤ divisorMass R + divisorMass T := by
  rw [divisorMass, divisorClosure_union]
  exact mass_union_le _ _

/-- If every prime factor of `d` is at most `M`, then `d ≤ M * φ(d)`.
Induction on the largest prime factor `q` of `d`: writing `d = q ^ e * d'`
with `q ∤ d'`, the totient is multiplicative and `d' ≤ (q - 1) * φ(d')`. -/
theorem le_mul_totient :
    ∀ {d : ℕ}, 0 < d → ∀ {M : ℕ}, 1 ≤ M →
      (∀ q ∈ d.primeFactors, q ≤ M) → d ≤ M * d.totient := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd M hM hfac
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd) with h1 | h1
    · simpa [← h1] using hM
    -- `d ≥ 2`: split off the largest prime factor `q`.
    obtain ⟨q, hq_mem, hq_max⟩ :=
      Finset.exists_max_image d.primeFactors id
        ⟨d.minFac, Nat.mem_primeFactors.mpr
          ⟨Nat.minFac_prime (by omega), d.minFac_dvd, hd.ne'⟩⟩
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hqd : q ∣ d := Nat.dvd_of_mem_primeFactors hq_mem
    set e := d.factorization q with he
    set d' := d / q ^ e with hd'
    have hsplit : q ^ e * d' = d := Nat.ordProj_mul_ordCompl_eq_self d q
    have hd'pos : 0 < d' := Nat.ordCompl_pos q hd.ne'
    have hqe : 0 < e := hq.factorization_pos_of_dvd hd.ne' hqd
    have hd'lt : d' < d :=
      Nat.div_lt_self hd (Nat.one_lt_pow hqe.ne' hq.one_lt)
    -- Prime factors of `d'` are `< q`, hence `≤ q - 1`.
    have hfac' : ∀ r ∈ d'.primeFactors, r ≤ q - 1 := by
      intro r hr
      obtain ⟨hrp, hrd', -⟩ := Nat.mem_primeFactors.mp hr
      have hd'd : d' ∣ d := Nat.ordCompl_dvd d q
      have hrd : r ∈ d.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hrp, hrd'.trans hd'd, hd.ne'⟩
      have hrq : r ≠ q := by
        rintro rfl
        exact Nat.not_dvd_ordCompl hq hd.ne' hrd'
      have := hq_max r hrd
      simp only [id] at this
      omega
    have hIH : d' ≤ (q - 1) * d'.totient :=
      ih d' hd'lt hd'pos (by have := hq.two_le; omega) hfac'
    -- Assemble: `d = q^e * d' ≤ q^e * (q-1) * φ(d') = q * φ(d) ≤ M * φ(d)`.
    have htot : d.totient = q ^ (e - 1) * (q - 1) * d'.totient := by
      rw [← hsplit, Nat.totient_mul
        (Nat.Coprime.pow_left e (Nat.coprime_ordCompl hq hd.ne')),
        Nat.totient_prime_pow hq hqe]
    calc d = q ^ e * d' := hsplit.symm
      _ ≤ q ^ e * ((q - 1) * d'.totient) := Nat.mul_le_mul_left _ hIH
      _ = q * (q ^ (e - 1) * (q - 1) * d'.totient) := by
          rw [show q ^ e = q * q ^ (e - 1) from by
            rw [← pow_succ', Nat.sub_add_cancel hqe]]
          ring
      _ = q * d.totient := by rw [htot]
      _ ≤ M * d.totient := Nat.mul_le_mul_right _ (hfac q hq_mem)

variable {κ : Type*} [Fintype κ]

/-- Regrouping a totient sum over divisors by `p`-free parts: with `p ∤ m j`,
the totient sum over all divisors of the numbers `m j * p ^ a j` is at most
the totient sum over divisors `d'` of the `m j`, each weighted by `p ^ A(d')`
where `A(d')` is the largest `a j` among indices with `d' ∣ m j`. -/
theorem sum_totient_biUnion_le {p : ℕ} (hp : p.Prime) (m a : κ → ℕ)
    (hm : ∀ j, ¬ p ∣ m j) (hm0 : ∀ j, 0 < m j) :
    ∑ d ∈ univ.biUnion fun j ↦ (m j * p ^ a j).divisors, d.totient ≤
      ∑ d' ∈ univ.biUnion fun j ↦ (m j).divisors,
        d'.totient * p ^ ((univ.filter fun j ↦ d' ∣ m j).sup a) := by
  classical
  set D : Finset ℕ := univ.biUnion fun j ↦ (m j * p ^ a j).divisors with hD
  set D' : Finset ℕ := univ.biUnion fun j ↦ (m j).divisors with hD'
  set ψ : ℕ → ℕ := fun d ↦ ordCompl[p] d with hψ
  -- Membership unpacking: any `d ∈ D` has `p`-free part dividing some `m j`
  -- and `p`-exponent at most the corresponding `a j`.
  have hkey : ∀ d ∈ D, ∃ j, ψ d ∣ m j ∧ d.factorization p ≤ a j := by
    intro d hd
    obtain ⟨j, -, hdj⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hdj
    refine ⟨j, ?_, ?_⟩
    · have h1 := Nat.ordCompl_dvd_ordCompl_of_dvd hdvd p
      rwa [Nat.ordCompl_mul, Nat.ordCompl_self_pow hp,
        show ordCompl[p] (m j) = m j by
          simp [Nat.factorization_eq_zero_of_not_dvd (hm j)], mul_one] at h1
    · have h2 := (Nat.factorization_le_iff_dvd
        (Nat.pos_of_mem_divisors hdj).ne' hne).mpr hdvd
      have h3 := Finsupp.le_def.mp h2 p
      rwa [Nat.factorization_mul (hm0 j).ne' (pow_ne_zero _ hp.pos.ne'),
        hp.factorization_pow, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (hm j), Finsupp.single_eq_same,
        zero_add] at h3
  have hmaps : ∀ d ∈ D, ψ d ∈ D' := fun d hd ↦ by
    obtain ⟨j, hj, -⟩ := hkey d hd
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
      Nat.mem_divisors.mpr ⟨hj, (hm0 j).ne'⟩⟩
  -- Fiber the sum over the `p`-free part.
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun d ↦ d.totient)]
  refine Finset.sum_le_sum fun d' hd' ↦ ?_
  set A := (univ.filter fun j ↦ d' ∣ m j).sup a with hA
  have hd'p : ¬ p ∣ d' := by
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hd'
    exact fun hdvd ↦ hm j (hdvd.trans (Nat.mem_divisors.mp hj).1)
  -- Reindex the fiber by the `p`-exponent.
  have hfib : ∀ d ∈ D.filter fun d ↦ ψ d = d', d' * p ^ d.factorization p = d := by
    intro d hd
    obtain ⟨-, hdψ⟩ := Finset.mem_filter.mp hd
    rw [← hdψ, hψ, mul_comm]
    exact Nat.ordProj_mul_ordCompl_eq_self d p
  have hinj : ∀ x ∈ D.filter fun d ↦ ψ d = d', ∀ y ∈ D.filter fun d ↦ ψ d = d',
      x.factorization p = y.factorization p → x = y := fun x hx y hy hxy ↦ by
    rw [← hfib x hx, ← hfib y hy, hxy]
  calc ∑ d ∈ D.filter (fun d ↦ ψ d = d'), d.totient
      = ∑ c ∈ (D.filter fun d ↦ ψ d = d').image fun d ↦ d.factorization p,
          (d' * p ^ c).totient := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun d hd ↦ by rw [hfib d hd]
    _ ≤ ∑ c ∈ Finset.range (A + 1), (d' * p ^ c).totient := by
        refine Finset.sum_le_sum_of_subset fun c hc ↦ ?_
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨hdD, -⟩ := Finset.mem_filter.mp hd
        obtain ⟨j, hj1, hj2⟩ := hkey d hdD
        have : d.factorization p ≤ A := by
          refine le_trans hj2 (Finset.le_sup ?_)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
            (Finset.mem_filter.mp hd).2 ▸ hj1⟩
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
    _ = d'.totient * ∑ c ∈ Finset.range (A + 1), (p ^ c).totient := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        exact Nat.totient_mul
          (Nat.Coprime.pow_right c ((hp.coprime_iff_not_dvd.mpr hd'p).symm))
    _ = d'.totient * p ^ A := by
        congr 1
        have := Nat.sum_totient (p ^ A)
        rwa [Nat.divisors_prime_pow hp, Finset.sum_map] at this

end Erdos274
