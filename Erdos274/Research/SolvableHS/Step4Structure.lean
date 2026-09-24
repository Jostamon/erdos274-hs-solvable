/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.Research.SolvableHS.CyclotomicBlock
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

/-! ### Conjugation invariance -/

/-- `g` maps `A` into itself by conjugation. -/
def Normalizes (g : G) (A : Subgroup G) : Prop := ∀ x ∈ A, g * x * g⁻¹ ∈ A

theorem Normalizes.mul {g h : G} {A : Subgroup G} (hg : Normalizes g A) (hh : Normalizes h A) :
    Normalizes (g * h) A := fun x hx ↦ by
  have e : g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group
  rw [e]
  exact hg _ (hh x hx)

theorem normalizes_of_mem {g : G} {A : Subgroup G} (hg : g ∈ A) : Normalizes g A :=
  fun _ hx ↦ A.mul_mem (A.mul_mem hg hx) (A.inv_mem hg)

theorem normalizes_of_normal {g : G} {A : Subgroup G} (hA : A.Normal) : Normalizes g A :=
  fun x hx ↦ hA.conj_mem x hx g

theorem normalizes_of_mem_normalizer {g : G} {A : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) : Normalizes g A :=
  fun x hx ↦ (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem Normalizes.commutator {g : G} {A B : Subgroup G} (hA : Normalizes g A)
    (hB : Normalizes g B) : Normalizes g ⁅A, B⁆ := by
  have key : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.commutator_mem_commutator (hA x hx) (hB y hy)
  intro x hx
  have h := key hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

theorem Normalizes.sup {g : G} {A B : Subgroup G} (hA : Normalizes g A) (hB : Normalizes g B) :
    Normalizes g (A ⊔ B) := by
  have key : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun x hx ↦ ?_) (fun x hx ↦ ?_) <;>
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · exact Subgroup.mem_sup_left (hA x hx)
    · exact Subgroup.mem_sup_right (hB x hx)
  intro x hx
  have h := key hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

/-- `[A,B]` is normalised by `A`. -/
theorem normalizes_commutator_left {A B : Subgroup G} {a : G} (ha : a ∈ A) :
    Normalizes a ⁅A, B⁆ := by
  have key : ⁅A, B⁆ ≤ ⁅A, B⁆.comap (MulAut.conj a).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : a * ⁅x, y⁆ * a⁻¹ = ⁅a * x, y⁆ * ⁅a, y⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (A.mul_mem ha hx) hy)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ha hy))
  intro x hx
  have h := key hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

/-- `[A,B]` is normalised by `B`. -/
theorem normalizes_commutator_right {A B : Subgroup G} {b : G} (hb : b ∈ B) :
    Normalizes b ⁅A, B⁆ := by
  rw [Subgroup.commutator_comm]
  exact normalizes_commutator_left hb

/-- A subgroup that every element normalises is normal. -/
theorem normal_of_normalizes {A : Subgroup G} (h : ∀ g, Normalizes g A) : A.Normal :=
  ⟨fun x hx g ↦ h g x hx⟩

variable [Finite G]

/-- In a finite group, conjugating a subgroup into itself normalises it. -/
theorem mem_normalizer_of_normalizes {g : G} {A : Subgroup G} (h : Normalizes g A) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx ↦ ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, e⟩ := hx
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
  have : y = x := by simpa using e
  exact this ▸ hy

/-! ### Coprimality -/

/-- A `p`-subgroup of a `p′`-group is trivial. -/
theorem eq_bot_of_pGroup_of_le {p : ℕ} [hp : Fact p.Prime] {X N : Subgroup G}
    (hX : IsPGroup p X) (hXN : X ≤ N) (hN : ¬ p ∣ Nat.card N) : X = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  have hdvd : Nat.card X ∣ Nat.card N := Subgroup.card_dvd_of_le hXN
  cases k with
  | zero => exact Subgroup.eq_bot_of_card_eq X (by simpa using hk)
  | succ k =>
    exact absurd ((dvd_pow_self p (Nat.succ_ne_zero k)).trans (hk ▸ hdvd)) hN

/-- An element of a normal `p′`-subgroup that normalises a `p`-subgroup
centralises it. -/
theorem commute_of_normalizes {p : ℕ} [Fact p.Prime] {N Q : Subgroup G} [N.Normal]
    (hN : ¬ p ∣ Nat.card N) (hQ : IsPGroup p Q) {c : G} (hc : c ∈ N) (hcQ : Normalizes c Q)
    {y : G} (hy : y ∈ Q) : c * y = y * c := by
  have hbot : N ⊓ Q = ⊥ := eq_bot_of_pGroup_of_le hQ.to_inf_right inf_le_left hN
  have h1 : c * y * c⁻¹ * y⁻¹ ∈ Q := Q.mul_mem (hcQ y hy) (Q.inv_mem hy)
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
    ∃ k ∈ ⁅N, Q⁆, ∃ c ∈ N, Normalizes c Q ∧ n = k * c := by
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
  have hm : Normalizes ((h : G)⁻¹ * n) Q := by
    intro y hy
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
  exact (normalizes_of_mem hx).mul hm

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
  -- `V/N` is minimal normal in `G/N`
  set A₀ := V.map (QuotientGroup.mk' N) with hA₀
  have hA₀n : A₀.Normal := Subgroup.Normal.map hVn _ (QuotientGroup.mk'_surjective N)
  have hA₀ne : A₀ ≠ ⊥ := by
    rw [hA₀, Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact fun h ↦ hNV.not_ge h
  have hA₀min : ∀ N' : Subgroup (G ⧸ N), N'.Normal → N' ≠ ⊥ → N' ≤ A₀ → N' = A₀ := by
    intro N' hN'n hN'ne hN'le
    set V' := N'.comap (QuotientGroup.mk' N) with hV'
    have hV'n : V'.Normal := Subgroup.Normal.comap hN'n _
    have hNV' : N ≤ V' := by
      intro n hn
      rw [hV', Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
      exact N'.one_mem
    have hV'V : V' ≤ V := by
      calc V' ≤ A₀.comap (QuotientGroup.mk' N) := Subgroup.comap_mono hN'le
        _ = V ⊔ N := by rw [hA₀, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
        _ = V := sup_eq_left.mpr hNV.le
    have hNV'ne : N ≠ V' := by
      intro h
      apply hN'ne
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) N',
        ← hV', ← h, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hV'S : V' ∈ S := ⟨hV'n, lt_of_le_of_ne hNV' hNV'ne⟩
    have hVV' : V = V' := le_antisymm (hVmin.2 hV'S hV'V) hV'V
    rw [hA₀, hVV', hV', Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]
  obtain ⟨q, a, hq, -, -, -, hexp⟩ := minimal_normal_is_elementary_abelian hA₀n hA₀ne hA₀min
  have hexpV : ∀ v ∈ V, v ^ q ∈ N := by
    intro v hv
    have h := congrArg Subtype.val (hexp ⟨_, Subgroup.mem_map_of_mem _ hv⟩)
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply] at h
    rw [← QuotientGroup.mk_pow] at h
    exact (QuotientGroup.eq_one_iff _).mp h
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
  have hgen : ∀ X : Subgroup G, (∀ g ∈ Subgroup.normalizer (Q : Set G), Normalizes g X) →
      (∀ n ∈ N, Normalizes n X) → (∀ y ∈ Q, Normalizes y X) → X.Normal := by
    intro X h1 h2 h3
    refine normal_of_normalizes fun g ↦ ?_
    have hg : g ∈ ((Subgroup.normalizer (Q : Set G) ⊔ V : Subgroup G) : Set G) := by
      rw [hFr]; trivial
    rw [Subgroup.mul_normal] at hg
    obtain ⟨a, ha, v, hv, rfl⟩ := hg
    have hv' : v ∈ ((N ⊔ Q : Subgroup G) : Set G) := hVNQ hv
    rw [Subgroup.normal_mul] at hv'
    obtain ⟨n, hn, y, hy, rfl⟩ := hv'
    exact (h1 a ha).mul ((h2 n hn).mul (h3 y hy))
  have hKnorm : K.Normal := hgen K
    (fun g hg ↦ (normalizes_of_normal hNn).commutator (normalizes_of_mem_normalizer hg))
    (fun n hn ↦ normalizes_commutator_left hn) (fun y hy ↦ normalizes_commutator_right hy)
  -- `N = K·C_N(Q)`
  have hsplit := fun n (hn : n ∈ N) ↦ exists_mul_centralizing hNp hQ hKnorm hn
  have hFnorm : (K ⊔ Q).Normal := by
    refine hgen _ (fun g hg ↦ (normalizes_of_normal hKnorm).sup (normalizes_of_mem_normalizer hg))
      (fun n hn ↦ ?_) (fun y hy ↦ normalizes_of_mem (Subgroup.mem_sup_right hy))
    obtain ⟨k, hk, c, hcN, hcQ, rfl⟩ := hsplit n hn
    exact (normalizes_of_mem (Subgroup.mem_sup_left hk)).mul
      ((normalizes_of_normal hKnorm).sup hcQ)
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
