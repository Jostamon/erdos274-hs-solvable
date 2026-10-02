/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
module

public import Erdos274.KnownCases.Solvable.SevenCB
public import Erdos274.KnownCases.Solvable.Step4Structure
public import Erdos274.KnownCases.Solvable.Step4Closure
public import Erdos274.KnownCases.Solvable.Step4Criterion
public import Erdos274.KnownCases.Solvable.SmallPrimes
public import Erdos274.KnownCases.Solvable.Minimality


/-!
# Step 4, and the least counterexample

`DECISION_LOG` D98.  A least solvable counterexample to Herzog–Schönheim has
an exact covering with pairwise distinct indices, `k ≥ 2` parts, and HS for
every smaller solvable group.  `false_of_minimal` shows there is none.  Let
`p` be the largest prime of `|G|`.

* `p ≤ 3` (`false_of_small_primes`).  Indices of distinct parts are never
  coprime (`eq_of_coprime_index`), so either every index is even or every
  index is divisible by `3`.  No index is `2` (`index_ne_two`: the other parts
  would partition the index-2 subgroup, a smaller counterexample).  Then
  `∑ 1/dᵢ` falls short of `1` against `∏_{q ∣ |G|} q/(q−1) ≤ 3`.
* `p ≥ 5`.  `Step4Structure.exists_structure` gives `F = O^{p′}(G) ◁ G`, with
  no nontrivial `p′`-quotient.  Some part
  is non-universal, or the covering descends to `G/F`.
  - If the criterion `Π_p·(S_p + 1/(p−1)) < 1` holds:
    `Step4Closure.false_of_covering`, with (CB) from `SevenCB.cb_loc`.
  - Otherwise `p = 7`, the only prime `p ≥ 5` at which it fails
    (`Step4Criterion.step4Crit_iff_ne_seven`): `SevenCB.false_of_structure`.

**Step 4 is the case `p² ∣ |G|`.  The argument never uses the exponent of
`p`**: the localisation `F = O^{p′}(G)`, (CB), the chambers and the closure
hold when `p ∥ |G|` too.  So this also closes step 3, and `herzog_schonheim_of_solvable`
is HS for every finite solvable group, by strong induction on `|G|`.
-/

@[expose] public section

namespace Erdos274

namespace Step4

open QuotientShadow SevenJoin ExpWeight ApexCharging DivisorWeight SevenClosure PrimeOrder
open scoped ENNReal NNReal Pointwise

universe u v

variable {G : Type u} [Group G] {κ : Type v} [Fintype κ]

/-! ### The least counterexample -/

/-- **A least solvable counterexample does not exist.**  `G` is finite and
solvable, `C` an exact covering with at least two parts and pairwise distinct
indices, and every smaller finite solvable group satisfies HS. -/
theorem false_of_minimal [Finite G] [Group.IsSolvable G] (C : Group.ExactCovering G κ)
    (hκ : 1 < Fintype.card κ) (hinj : Function.Injective fun i ↦ (C.parts i).index)
    (hmin : AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim.{u, v} (Nat.card G)) :
    False := by
  classical
  have := Fintype.ofFinite G
  have hnt : Nontrivial G := exactCovering_nontrivial_of_one_lt_card C hκ
  set n := Nat.card G with hndef
  have hn1 : 1 < n := Finite.one_lt_card
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn1
  -- `p`, the largest prime of `|G|`
  set p := n.primeFactors.max' hne with hpdef
  have hpmem : p ∈ n.primeFactors := Finset.max'_mem _ _
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpG : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
  have hmax : ∀ q, q.Prime → q ∣ n → q ≤ p := fun q hq hqn ↦
    Finset.le_max' _ _ (Nat.mem_primeFactors.mpr ⟨hq, hqn, Nat.card_pos.ne'⟩)
  by_cases hp3 : p ≤ 3
  · exact false_of_small_primes C hκ hinj (index_ne_two C hinj hmin)
      fun q hq hqn ↦ (hmax q hq hqn).trans hp3
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hFn, hFbot, hres⟩ := Step4Structure.exists_structure (p := p) hpG
  have hdist : Set.InjOn (fun j ↦ (C.parts j).index) (nonUniv C F) := hinj.injOn
  -- some part is non-universal, or the covering descends to `G/F`
  have hneU : (nonUniv C F).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hall : ∀ j, F ≤ C.parts j := fun j ↦ by
      by_contra h
      have hj : j ∈ nonUniv C F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hempty] at hj
      exact Finset.notMem_empty _ hj
    exact false_of_nontrivial_normal_subgroup_in_all_parts
      C hκ hinj hmin F hFbot hall
  have h5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by rintro h; rw [h] at hp; norm_num at hp
    omega
  by_cases hc : Step4Criterion.step4Crit p
  · refine Step4Closure.false_of_covering C F hpG hmax hdist hneU (fun j hj ↦ ?_) hc
    by_cases hpj : p ∣ loc C F j
    · exact Or.inl hpj
    right
    obtain ⟨q, hq, hqp, hqG, hdvd⟩ :=
      SevenCB.cb_loc C F hres (Finset.mem_filter.mp hj).2 hpj
    exact ⟨q, hq, lt_of_le_of_ne (hmax q hq hqG) hqp, hdvd⟩
  · -- the criterion fails only at `7`
    have hp7 : p = 7 := Step4Criterion.eq_seven_of_not_step4Crit hp h5 hc
    clear_value p
    subst hp7
    exact SevenCB.false_of_structure C F hres hmax hdist hneU

/-- **Herzog–Schönheim for finite solvable groups.**  In a partition of a
finite solvable group into at least two left cosets, two of the subgroups have
the same index. -/
theorem herzog_schonheim_of_solvable (G : Type u) [Group G] [Finite G]
    [Group.IsSolvable G] : GroupSatisfiesHerzogSchonheim.{u, v} G := by
  suffices h : ∀ N : ℕ, ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G = N → GroupSatisfiesHerzogSchonheim.{u, v} G from h _ G rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro G _ _ _ hG ι _ P hι
    by_contra hno
    push Not at hno
    have hinj : Function.Injective fun i ↦ (P.parts i).index := fun i j h ↦ by
      by_contra hij
      exact hno i j hij h
    have hmin : AllFiniteSolvableGroupsBelowSatisfyHerzogSchonheim.{u, v} (Nat.card G) :=
      fun Q _ _ _ hQ ↦ ih (Nat.card Q) (hG ▸ hQ) Q rfl
    exact false_of_minimal P hι hinj hmin

end Step4

end Erdos274
