/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.KnownCases.Solvable.CyclotomicBlock
import Mathlib.GroupTheory.Sylow

/-!
# The step-4 localisation `F = KQ`

`SOLVABLE_HS_TRACK.md` §9.21 addendum 1, `DECISION_LOG` D98 §6.  Let `G` be a
finite solvable group and `p` a prime dividing `|G|`.  This file constructs
`K, Q ≤ G` with
* `K ◁ G` a `p′`-group and `Q ≠ 1` a `p`-group;
* `F = K ⊔ Q ◁ G`;
* `[K,Q] = K`.

These are exactly the hypotheses of `SevenCB.false_of_structure` and of the
general-`p` closure.

The construction.
* `N` is maximal among the normal `p′`-subgroups, and `V` is minimal among
  the normal subgroups strictly above `N`.  Then `V/N` is minimal normal in the
  solvable group `G/N`, so every `v ∈ V` has `v^q ∈ N` for a prime `q`.  If
  `q ≠ p` then `V` would be a larger normal `p′`-subgroup; so `q = p`, and
  `[V : N]` is a power of `p`.
* `Q` is a Sylow `p`-subgroup of `V`.  Then `V = N ⊔ Q`, as `[V : N ⊔ Q]`
  divides both `[V : N]`, a power of `p`, and `[V : Q]`, which is prime to `p`.
  Frattini gives `G = N_G(Q)·V`.
* `K = [N, Q]`.  Every `n ∈ N` is `k·c` with `k ∈ K` and `c ∈ N` centralising
  `Q`: `nQn⁻¹ ≤ KQ` is a `p`-subgroup and `Q` has `p′`-index in `KQ`, so some
  `h ∈ KQ` conjugates it back into `Q` (`exists_conj_mem_of_not_dvd`), and an
  element of `N` normalising `Q` centralises it (`N ⊓ Q = 1`).  This is the
  coprime-action identity `N = K·C_N(Q)`, proved with no Schur–Zassenhaus.
* Hence `[k c, y] = [k, y]` for `y ∈ Q`, so `[N,Q] ≤ [K,Q]`: `[K,Q] = K`.
* `K` and `KQ` are normalised by `N`, `Q` and `N_G(Q)`, which generate `G`.
-/

namespace Erdos274

namespace Step4Structure

open scoped Pointwise commutatorElement

universe u

variable {G : Type u} [Group G]

/-! ### Normalisers -/

/-- `N_G(A) ⊓ N_G(B)` normalises `[A,B]`: conjugation commutes with the
commutator (`Subgroup.map_commutator`). -/
theorem inf_normalizer_le_normalizer_commutator (A B : Subgroup G) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_inf, Subgroup.mem_normalizer_iff_map_conj_eq,
    Subgroup.mem_normalizer_iff_map_conj_eq] at hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, hg.1, hg.2]

variable [Finite G]

/-- In a finite group, conjugating a subgroup into itself normalises it. -/
theorem mem_normalizer_of_conj_mem {g : G} {A : Subgroup G} (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

/-! ### Coprimality -/

/-- An element of a normal `p′`-subgroup that normalises a `p`-subgroup
centralises it. -/
theorem commute_of_normalizes {p : ℕ} [Fact p.Prime] {N Q : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (hQ : IsPGroup p Q) {c : G} (hc : c ∈ N)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G)) {y : G} (hy : y ∈ Q) : c * y = y * c := by
  have hbot : N ⊓ Q = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hN).symm.pow_right k
  have h1 : c * y * c⁻¹ * y⁻¹ ∈ Q :=
    Q.mul_mem ((Subgroup.mem_normalizer_iff.mp hcQ y).mp hy) (Q.inv_mem hy)
  have h2 : c * y * c⁻¹ * y⁻¹ ∈ N := by
    have : y * c⁻¹ * y⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hc) y
    have e : c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) := by group
    rw [e]
    exact N.mul_mem hc this
  have h3 : c * y * c⁻¹ * y⁻¹ ∈ N ⊓ Q := ⟨h2, h1⟩
  rw [hbot, Subgroup.mem_bot] at h3
  calc c * y = (c * y * c⁻¹ * y⁻¹) * (y * c) := by group
    _ = y * c := by rw [h3, one_mul]

/-- **`N = K·C_N(Q)`** for `K = [N,Q]`, `N ◁ G` a `p′`-group and `Q` a
`p`-group normalising `N`. -/
theorem exists_mul_centralizing {p : ℕ} [Fact p.Prime] {N Q : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (hQ : IsPGroup p Q) (hK : (⁅N, Q⁆ : Subgroup G).Normal)
    {n : G} (hn : n ∈ N) :
    ∃ k ∈ ⁅N, Q⁆, ∃ c ∈ N, c ∈ Subgroup.normalizer (Q : Set G) ∧ n = k * c := by
  set K : Subgroup G := ⁅N, Q⁆ with hKdef
  have hKN : K ≤ N := Subgroup.commutator_le_left N Q
  set L := K ⊔ Q with hL
  -- `nQn⁻¹ ≤ KQ`
  have hnL : ∀ y ∈ Q, n * y * n⁻¹ ∈ L := fun y hy ↦ by
    have e : n * y * n⁻¹ = ⁅n, y⁆ * y := by simp only [commutatorElement_def]; group
    rw [e]
    exact L.mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hn hy))
      (Subgroup.mem_sup_right hy)
  -- `Q` has `p′`-index in `KQ`
  have hidx : ¬ p ∣ (Q.subgroupOf L).index := by
    change ¬ p ∣ Q.relIndex L
    rw [hL, sup_comm, CyclotomicBlock.relIndex_sup_normal]
    intro h
    exact hN ((h.trans (Subgroup.relIndex_dvd_card _ _)).trans (Subgroup.card_dvd_of_le hKN))
  -- the conjugate `nQn⁻¹`, inside `KQ`
  set Qn := Q.map (MulAut.conj n).toMonoidHom with hQn
  have hQnL : IsPGroup p (Qn.subgroupOf L) :=
    (hQ.map _).comap_of_injective L.subtype L.subtype_injective
  obtain ⟨h, hh⟩ := CyclotomicBlock.exists_conj_mem_of_not_dvd hQnL hidx
  have hm : (h : G)⁻¹ * n ∈ Subgroup.normalizer (Q : Set G) := by
    refine mem_normalizer_of_conj_mem fun y hy ↦ ?_
    have hyL : (⟨n * y * n⁻¹, hnL y hy⟩ : L) ∈ Qn.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨y, hy, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have h2 := hh _ hyL
    rw [Subgroup.mem_subgroupOf] at h2
    have e : (h : G)⁻¹ * n * y * ((h : G)⁻¹ * n)⁻¹ = (h : G)⁻¹ * (n * y * n⁻¹) * h := by group
    rw [e]
    simpa using h2
  -- write `h = k x` with `k ∈ K`, `x ∈ Q`
  have hh' : (h : G) ∈ ((K ⊔ Q : Subgroup G) : Set G) := h.2
  rw [Subgroup.normal_mul K Q] at hh'
  obtain ⟨k, hk, x, hx, hkx⟩ := hh'
  refine ⟨k, hk, k⁻¹ * n, N.mul_mem (N.inv_mem (hKN hk)) hn, ?_, by group⟩
  have e : k⁻¹ * n = x * ((h : G)⁻¹ * n) := by rw [← hkx]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer (H := Q) hx) hm

/-! ### The construction -/

/-- **The step-4 localisation.**  In a finite solvable group with `p ∣ |G|`
there are `K ◁ G` a `p′`-group and `Q ≠ 1` a `p`-group with `K ⊔ Q ◁ G` and
`[K,Q] = K`. -/
theorem exists_structure [Group.IsSolvable G] {p : ℕ} [hp : Fact p.Prime]
    (hpG : p ∣ Nat.card G) :
    ∃ K Q : Subgroup G, K.Normal ∧ (K ⊔ Q).Normal ∧ IsPGroup p Q ∧ Q ≠ ⊥ ∧
      ¬ p ∣ Nat.card K ∧ ⁅K, Q⁆ = K := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun S : Subgroup G ↦ (S : Set G)) SetLike.coe_injective
  -- `N`: maximal among the normal `p′`-subgroups
  obtain ⟨N, -, hNmax⟩ := Finite.exists_le_maximal
    (p := fun X : Subgroup G ↦ X.Normal ∧ ¬ p ∣ Nat.card X) (a := ⊥)
    ⟨inferInstance, by rw [Subgroup.card_bot]; exact hp.out.not_dvd_one⟩
  obtain ⟨hNn, hNp⟩ := hNmax.prop
  have hNtop : N ≠ ⊤ := by
    rintro rfl
    exact hNp (by rwa [Subgroup.card_top])
  -- `V`: minimal among the normal subgroups strictly above `N`
  let S : Set (Subgroup G) := {V | V.Normal ∧ N < V}
  have htopS : ⊤ ∈ S := ⟨inferInstance, lt_top_iff_ne_top.mpr hNtop⟩
  obtain ⟨V, -, hVmin⟩ := (Set.toFinite S).isPWO.exists_le_minimal htopS
  obtain ⟨hVn, hNV⟩ := hVmin.prop
  -- `V/N` is a minimal normal section, hence of prime exponent `q`
  have := hNn
  obtain ⟨q, hq, hexpV, -⟩ := exists_prime_of_minimal_normal_section hVn hNV
    fun V' hV'n hNV' hV'V ↦ le_antisymm hV'V (hVmin.2 ⟨hV'n, hNV'⟩ hV'V)
  -- `[V : N]` is a power of `q`
  have : (N.subgroupOf V).Normal := hNn.subgroupOf V
  have : Fact q.Prime := ⟨hq⟩
  have hVNq : IsPGroup q (V ⧸ N.subgroupOf V) := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hexpV v v.2
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hVNq
  have hrel : N.relIndex V = q ^ c := hc
  have hcardV : Nat.card N * N.relIndex V = Nat.card V := by
    have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) N V bot_le hNV.le
    rwa [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h
  -- `q = p`
  have hqp : q = p := by
    by_contra hne
    have hpV : ¬ p ∣ Nat.card V := by
      rw [← hcardV, hrel]
      intro h
      rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
      · exact hNp h
      · exact hne ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp (hp.out.dvd_of_dvd_pow h)).symm
    exact hNV.not_ge (hNmax.2 ⟨hVn, hpV⟩ hNV.le)
  subst hqp
  -- `Q`: a Sylow `p`-subgroup of `V`
  obtain ⟨P⟩ : Nonempty (Sylow q V) := inferInstance
  set Q : Subgroup G := (P : Subgroup V).map V.subtype with hQdef
  have hQ : IsPGroup q Q := P.isPGroup'.map V.subtype
  have hQV : Q ≤ V := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQsub : Q.subgroupOf V = P := Subgroup.comap_map_eq_self_of_injective V.subtype_injective _
  -- `V = N ⊔ Q`
  have hVNQ : V ≤ N ⊔ Q := by
    have hXV : N ⊔ Q ≤ V := sup_le hNV.le hQV
    have h1 : (N ⊔ Q).relIndex V ∣ N.relIndex V :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex N (N ⊔ Q) V le_sup_left hXV)
    have h2 : (N ⊔ Q).relIndex V ∣ Q.relIndex V :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex Q (N ⊔ Q) V le_sup_right hXV)
    have h3 : ¬ q ∣ Q.relIndex V := by
      change ¬ q ∣ (Q.subgroupOf V).index
      rw [hQsub]
      exact P.not_dvd_index
    rw [hrel] at h1
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp.out).mp h1
    rcases j with _ | j
    · exact Subgroup.relIndex_eq_one.mp (by simpa using hjeq)
    · exact absurd ((dvd_pow_self q (Nat.succ_ne_zero j)).trans (hjeq ▸ h2)) h3
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, sup_bot_eq] at hVNQ
    exact hNV.not_ge hVNQ
  -- Frattini: `N_G(Q) ⊔ V = G`
  have hFr : Subgroup.normalizer (Q : Set G) ⊔ V = ⊤ := Sylow.normalizer_sup_eq_top P
  -- `K = [N, Q]`
  set K : Subgroup G := ⁅N, Q⁆ with hKdef
  have hKN : K ≤ N := Subgroup.commutator_le_left N Q
  -- anything normalised by `N_G(Q)`, `N` and `Q` is normal
  have hgen : ∀ X : Subgroup G, Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer X →
      N ≤ Subgroup.normalizer X → Q ≤ Subgroup.normalizer X → X.Normal := by
    intro X h1 h2 h3
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hFr]
    exact sup_le h1 (hVNQ.trans (sup_le h2 h3))
  have hKnorm : K.Normal := hgen K
    ((le_inf Subgroup.le_normalizer_of_normal le_rfl).trans
      (inf_normalizer_le_normalizer_commutator N Q))
    (Subgroup.normalizer_commutator_ge_left N Q) (Subgroup.normalizer_commutator_ge_right N Q)
  have := hKnorm
  -- `N = K·C_N(Q)`
  have hsplit := fun n (hn : n ∈ N) ↦ exists_mul_centralizing hNp hQ hKnorm hn
  have hFnorm : (K ⊔ Q).Normal := by
    refine hgen _ ((le_inf Subgroup.le_normalizer_of_normal le_rfl).trans
        (K.inf_normalizer_le_normalizer_sup Q)) (fun n hn ↦ ?_)
      (le_sup_right.trans (Subgroup.le_normalizer (H := K ⊔ Q)))
    obtain ⟨k, hk, c, hcN, hcQ, rfl⟩ := hsplit n hn
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (H := K ⊔ Q) (Subgroup.mem_sup_left hk))
      (K.inf_normalizer_le_normalizer_sup Q
        ⟨Subgroup.le_normalizer_of_normal (K := ⊤) (Subgroup.mem_top c), hcQ⟩)
  refine ⟨K, Q, hKnorm, hFnorm, hQ, hQne, fun h ↦ hNp (h.trans (Subgroup.card_dvd_of_le hKN)),
    le_antisymm (Subgroup.commutator_le_left K Q) ?_⟩
  -- `[N,Q] ≤ [K,Q]`
  rw [hKdef, Subgroup.commutator_le]
  intro n hn y hy
  obtain ⟨k, hk, c, hcN, hcQ, rfl⟩ := hsplit n hn
  have hcy : c * y = y * c := commute_of_normalizes hNp hQ hcN hcQ hy
  have e : ⁅k * c, y⁆ = ⁅k, y⁆ := by
    simp only [commutatorElement_def]
    calc k * c * y * (k * c)⁻¹ * y⁻¹ = k * (c * y) * c⁻¹ * k⁻¹ * y⁻¹ := by group
      _ = k * (y * c) * c⁻¹ * k⁻¹ * y⁻¹ := by rw [hcy]
      _ = k * y * k⁻¹ * y⁻¹ := by group
  rw [e]
  exact Subgroup.commutator_mem_commutator hk hy

end Step4Structure

end Erdos274
