/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.FiniteGroup.MinimalNormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Field.ZMod

/-!
# (CB), the cyclotomic block lemma

`SOLVABLE_HS_TRACK.md` §9.19 §3 (statement and paper proof due to OpenAI GPT-5.6
Sol).  This file proves it by the shorter route of `DECISION_LOG` D98 §14,
which needs neither primitive permutation groups (Robinson 7.2.6) nor `GL(a,q)`.

> **(CB).**  Let `H` be a finite solvable group, `p` a prime, `K ◁ H` a
> `p′`-subgroup and `Q ≤ H` a `p`-subgroup with `[K,Q] = K`.  If `W < K` is
> `Q`-invariant, then some prime `q ∣ |K|` has `q^{ord_p q} ∣ [K : W]`.

* `orderOf_le_of_fixedPoints`: if a `p`-group acts nontrivially by
  automorphisms on a group of order `q^c`, with `q ≠ p`, then `ord_p q ≤ c`.
  The fixed points form a subgroup of order `q^b` with `b < c`, and
  `q^c ≡ q^b (mod p)` (`IsPGroup.card_modEq_card_fixedPoints`).
* `cyclotomic_block`, the core.  Take `M ⊇ W` maximal among the proper
  `Q`-invariant subgroups of `K`, `N` the normal core of `M`, and `V` minimal
  among the normal subgroups with `N < V ≤ K`.
  - `V/N` is minimal normal in the solvable group `H/N`, hence elementary
    abelian of exponent a prime `q` (`minimal_normal_is_elementary_abelian`).
  - `V ⊄ M`, so `M ⊔ V = K` and `[K : M] = [V : V ⊓ M]`.
  - `V ⊓ M` is normal in `V`, and `Q` acts on `A = V/(V ⊓ M)`, a `q`-group.
  - The action is nontrivial: otherwise every `⁅k, x⁆` lies in `M`, so
    `K = [K,Q] ≤ M`.
* `cyclotomic_block_index`: the form the covering uses.  If `K ⊔ Q = H` and
  `Y < H` has `p ∤ [H : Y]`, then `q^{ord_p q} ∣ [H : Y]` for some prime
  `q ∣ |K|`.  A fixed point of `Q` on `H/Y` conjugates `Q` into `Y`, and then
  `[H : Y] = [K : K ⊓ Y]`.
-/

namespace Erdos274

namespace CyclotomicBlock

open MulAction
open scoped Pointwise

universe u

/-! ### The fixed-point count -/

/-- **A `p`-group acting nontrivially on a group of order `q^c` forces
`ord_p q ≤ c`.** -/
theorem orderOf_le_of_fixedPoints {p q c : ℕ} [hp : Fact p.Prime] (hq : q.Prime)
    (hpq : p ≠ q) {P A : Type*} [Group P] [Group A] [Finite A]
    [MulDistribMulAction P A]
    (hP : IsPGroup p P) (hA : Nat.card A = q ^ c) (hnt : ∃ (x : P) (a : A), x • a ≠ a) :
    orderOf (q : ZMod p) ≤ c := by
  set Fx := FixedPoints.subgroup P A
  obtain ⟨b, hbc, hb⟩ : ∃ b ≤ c, Nat.card Fx = q ^ b :=
    (Nat.dvd_prime_pow hq).mp (hA ▸ Subgroup.card_subgroup_dvd_card Fx)
  have hbne : b ≠ c := by
    rintro rfl
    obtain ⟨x, a, hxa⟩ := hnt
    have htop : Fx = ⊤ := Subgroup.eq_top_of_card_eq Fx (hb.trans hA.symm)
    have hmem : a ∈ Fx := by rw [htop]; exact Subgroup.mem_top a
    exact hxa ((FixedPoints.mem_subgroup P A a).mp hmem x)
  have hmod := hP.card_modEq_card_fixedPoints A
  have hfix : Nat.card (fixedPoints P A) = Nat.card Fx := rfl
  rw [hfix, hb, hA] at hmod
  have hZ : ((q : ZMod p)) ^ c = (q : ZMod p) ^ b := by
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp.out hq).mp h)
  have hone : (q : ZMod p) ^ (c - b) = 1 := by
    have h := hZ
    rw [← Nat.sub_add_cancel hbc, pow_add] at h
    exact (mul_eq_right₀ (pow_ne_zero _ hq0)).mp h
  have hdvd := orderOf_dvd_of_pow_eq_one hone
  have hpos : 0 < c - b := by omega
  exact (Nat.le_of_dvd hpos hdvd).trans (Nat.sub_le c b)

/-! ### Index arithmetic -/

variable {H : Type u} [Group H]

/-- `[M ⊔ V : M] = [V : M ⊓ V]` for `V` normal. -/
theorem relIndex_sup_normal [Finite H] (M V : Subgroup H) [V.Normal] :
    M.relIndex (M ⊔ V) = (M ⊓ V).relIndex V := by
  have h1 := Subgroup.relIndex_mul_relIndex (M ⊓ V) M (M ⊔ V) inf_le_left le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex (M ⊓ V) V (M ⊔ V) inf_le_right le_sup_right
  have h3 : V.relIndex (M ⊔ V) = (M ⊓ V).relIndex M := by
    rw [Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_right V M, inf_comm]
  rw [h3, ← h1, mul_comm] at h2
  have h0 : (M ⊓ V).relIndex M ≠ 0 := ((M ⊓ V).subgroupOf M).index_ne_zero_of_finite
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) h2).symm

/-- Conjugating by an element of the normaliser keeps a subgroup's elements in it. -/
theorem conj_mem_of_mem_normalizer {X : Subgroup H} {x y : H}
    (hx : x ∈ Subgroup.normalizer (X : Set H)) (hy : y ∈ X) : x * y * x⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.mp hx y).mp hy

/-- A subgroup normalising `M` normalises `M ⊔ V` when `V` is normal. -/
theorem le_normalizer_sup {Q M V : Subgroup H} [V.Normal]
    (hM : Q ≤ Subgroup.normalizer (M : Set H)) :
    Q ≤ Subgroup.normalizer ((M ⊔ V : Subgroup H) : Set H) :=
  (le_inf hM Subgroup.le_normalizer_of_normal).trans (M.inf_normalizer_le_normalizer_sup V)

section Core

variable [Finite H]

/-- **(CB), the cyclotomic block lemma.** -/
theorem cyclotomic_block [Group.IsSolvable H] {p : ℕ} [Fact p.Prime] {K Q W : Subgroup H}
    [K.Normal] (hQ : IsPGroup p Q) (hK : ¬ p ∣ Nat.card K) (hKQ : ⁅K, Q⁆ = K)
    (hWK : W ≤ K) (hWne : W ≠ K) (hWQ : Q ≤ Subgroup.normalizer (W : Set H)) :
    ∃ q, q.Prime ∧ q ∣ Nat.card K ∧ q ^ orderOf (q : ZMod p) ∣ W.relIndex K := by
  classical
  have : Finite (Subgroup H) :=
    Finite.of_injective (fun S : Subgroup H ↦ (S : Set H)) SetLike.coe_injective
  -- `M`: maximal among the proper `Q`-invariant subgroups of `K` above `W`
  obtain ⟨M, hWM, hMmax⟩ := Finite.exists_le_maximal
    (p := fun M : Subgroup H ↦ W ≤ M ∧ M ≤ K ∧ M ≠ K ∧ Q ≤ Subgroup.normalizer (M : Set H))
    ⟨le_rfl, hWK, hWne, hWQ⟩
  obtain ⟨-, hMK, hMne, hMQ⟩ := hMmax.prop
  -- `N`: the normal core of `M`
  set N := M.normalCore with hNdef
  have hNM : N ≤ M := M.normalCore_le
  -- `V`: minimal among the normal subgroups with `N < V ≤ K`
  let S : Set (Subgroup H) := {V | V.Normal ∧ N < V ∧ V ≤ K}
  have hKS : K ∈ S := ⟨inferInstance, lt_of_le_of_ne (hNM.trans hMK)
    (fun h ↦ hMne (le_antisymm hMK (h ▸ hNM))), le_rfl⟩
  obtain ⟨V, -, hVmin⟩ := (Set.toFinite S).isPWO.exists_le_minimal hKS
  obtain ⟨hVn, hNV, hVK⟩ := hVmin.prop
  -- `V/N` is a minimal normal section, hence elementary abelian
  obtain ⟨q, hq, hexpV, hcommV⟩ := exists_prime_of_minimal_normal_section hVn hNV
    fun V' hV'n hNV' hV'V ↦ le_antisymm hV'V (hVmin.2 ⟨hV'n, hNV', hV'V.trans hVK⟩ hV'V)
  have : Fact q.Prime := ⟨hq⟩
  -- consequences in `H`
  have hconjM : ∀ v ∈ V, ∀ d ∈ V ⊓ M, v * d * v⁻¹ ∈ M := by
    intro v hv d hd
    have hvd : ((v : H ⧸ N)) * d = d * v := hcommV v hv d hd.1
    have h : ((v * d * v⁻¹ : H) : H ⧸ N) = d := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hvd, mul_inv_cancel_right]
    have hn : (v * d * v⁻¹)⁻¹ * d ∈ N := QuotientGroup.eq.mp h
    have e : v * d * v⁻¹ = d * ((v * d * v⁻¹)⁻¹ * d)⁻¹ := by group
    rw [e]
    exact M.mul_mem hd.2 (M.inv_mem (hNM hn))
  -- `M ⊔ V = K`
  have hVM : ¬ V ≤ M := fun h ↦ hNV.not_ge (Subgroup.normal_le_normalCore.mpr h)
  have hsup : M ⊔ V = K := by
    by_contra hne
    have hmem : W ≤ M ⊔ V ∧ M ⊔ V ≤ K ∧ M ⊔ V ≠ K ∧
        Q ≤ Subgroup.normalizer ((M ⊔ V : Subgroup H) : Set H) :=
      ⟨hWM.trans le_sup_left, sup_le hMK hVK, hne, le_normalizer_sup hMQ⟩
    exact hVM ((hMmax.2 hmem le_sup_left).trans' le_sup_right)
  -- the quotient `A = V/(V ⊓ M)`
  set D' := (V ⊓ M).subgroupOf V with hD'
  have hD'n : D'.Normal := ⟨fun n hn g ↦ by
    rw [hD', Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(g * n * g⁻¹).2, hconjM g g.2 n hn⟩⟩
  have hcardA : Nat.card (V ⧸ D') = M.relIndex K := by
    rw [← hsup, relIndex_sup_normal, inf_comm]
    rfl
  -- the action of `Q` on `A` by conjugation
  have hmapD : ∀ x : Q, D'.map (MulAut.conjNormal (x : H) : V ≃* V).toMonoidHom = D' := by
    intro x
    have hin : ∀ y : Q, ∀ z : V, z ∈ D' → MulAut.conjNormal (y : H) z ∈ D' := by
      intro y z hz
      rw [hD', Subgroup.mem_subgroupOf] at hz ⊢
      rw [MulAut.conjNormal_apply]
      exact ⟨Subgroup.Normal.conj_mem inferInstance _ z.2 _,
        conj_mem_of_mem_normalizer (hMQ y.2) hz.2⟩
    refine le_antisymm ?_ fun z hz ↦ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hin x z hz
    · refine ⟨(MulAut.conjNormal (x : H))⁻¹ z, ?_, by simp⟩
      have := hin x⁻¹ z hz
      simpa using this
  let φ : Q →* MulAut (V ⧸ D') :=
    { toFun := fun x ↦ QuotientGroup.congr D' D' (MulAut.conjNormal (x : H)) (hmapD x)
      map_one' := by
        ext a
        induction a using QuotientGroup.induction_on
        simp [QuotientGroup.congr_mk]
      map_mul' := by
        intro x y
        ext a
        induction a using QuotientGroup.induction_on
        simp only [QuotientGroup.congr_mk, MulAut.mul_apply, Subgroup.coe_mul, map_mul]
        rfl }
  let _ : MulDistribMulAction Q (V ⧸ D') := MulDistribMulAction.compHom _ φ
  have hsmul : ∀ (x : Q) (v : V), x • ((v : V ⧸ D')) =
      ((MulAut.conjNormal (x : H) v : V) : V ⧸ D') := fun x v ↦ rfl
  -- the action is nontrivial, because `[K,Q] = K`
  have hnt : ∃ (x : Q) (a : V ⧸ D'), x • a ≠ a := by
    by_contra hall
    push Not at hall
    have hfix : ∀ x ∈ Q, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ M := by
      intro x hx v hv
      have h := hall ⟨x, hx⟩ ((⟨v⁻¹, V.inv_mem hv⟩ : V) : V ⧸ D')
      rw [hsmul, QuotientGroup.eq, hD', Subgroup.mem_subgroupOf] at h
      have h2 := h.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at h2
      have e : x * v * x⁻¹ * v⁻¹ = (x * v⁻¹ * x⁻¹)⁻¹ * v⁻¹ := by group
      rw [e]
      exact h2
    have hle : ⁅K, Q⁆ ≤ M := by
      rw [Subgroup.commutator_le]
      intro k hk x hx
      have hk' : k ∈ ((M ⊔ V : Subgroup H) : Set H) := hsup ▸ hk
      rw [Subgroup.mul_normal M V] at hk'
      obtain ⟨m, hm, v, hv, rfl⟩ := hk'
      rw [commutatorElement_def]
      have e : m * v * x * (m * v)⁻¹ * x⁻¹ =
          m * (x * v * x⁻¹ * v⁻¹)⁻¹ * (x * m⁻¹ * x⁻¹) := by group
      rw [e]
      exact M.mul_mem (M.mul_mem hm (M.inv_mem (hfix x hx v hv)))
        (conj_mem_of_mem_normalizer (hMQ hx) (M.inv_mem hm))
    exact hMne (le_antisymm hMK (hKQ ▸ hle))
  -- `A` is a `q`-group
  have hAq : IsPGroup q (V ⧸ D') := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H v =>
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hD',
        Subgroup.mem_subgroupOf]
      exact ⟨(v ^ q).2, hNM (by simpa using hexpV v v.2)⟩
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp hAq
  -- `q ≠ p`, as `q ∣ |K|`
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨x, a, hxa⟩ := hnt
    rw [pow_zero] at hc
    have : Subsingleton (V ⧸ D') := (Nat.card_eq_one_iff_unique.mp hc).1
    exact hxa (Subsingleton.elim _ _)
  have hqK : q ∣ Nat.card K := by
    refine (dvd_pow_self q hc0).trans ?_
    rw [← hc, hcardA]
    exact Subgroup.relIndex_dvd_card M K
  have hpq : p ≠ q := fun h ↦ hK (h ▸ hqK)
  have hord := orderOf_le_of_fixedPoints hq hpq hQ hc hnt
  refine ⟨q, hq, hqK, ?_⟩
  calc q ^ orderOf (q : ZMod p) ∣ q ^ c := pow_dvd_pow q hord
    _ = M.relIndex K := hc.symm.trans hcardA
    _ ∣ W.relIndex K := Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex W M K hWM hMK)

/-- **A `p`-group conjugates into a subgroup of `p′`-index**: `Q` fixes a point
`gY` of `H/Y`, since `p ∤ |H/Y|`, and then `g⁻¹Qg ≤ Y`. -/
theorem exists_conj_mem_of_not_dvd {p : ℕ} [Fact p.Prime] {Q Y : Subgroup H}
    (hQ : IsPGroup p Q) (hpY : ¬ p ∣ Y.index) : ∃ g : H, ∀ x ∈ Q, g⁻¹ * x * g ∈ Y := by
  classical
  obtain ⟨c, hc⟩ : (fixedPoints Q (H ⧸ Y)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hmod := hQ.card_modEq_card_fixedPoints (H ⧸ Y)
    rw [hne] at hmod
    simp only [Nat.card_of_isEmpty] at hmod
    exact hpY ((Nat.modEq_zero_iff_dvd).mp hmod)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨g, fun x hx ↦ ?_⟩
  have h := hc ⟨x⁻¹, Q.inv_mem hx⟩
  rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
  simpa [mul_assoc] using h

/-- **(CB) in index form.**  If `K ⊔ Q = H` and `Y < H` has `p ∤ [H : Y]`, then
some prime `q ∣ |K|` has `q^{ord_p q} ∣ [H : Y]`. -/
theorem cyclotomic_block_index [Group.IsSolvable H] {p : ℕ} [Fact p.Prime]
    {K Q Y : Subgroup H} [K.Normal] (hQ : IsPGroup p Q) (hK : ¬ p ∣ Nat.card K)
    (hKQ : ⁅K, Q⁆ = K) (hsup : K ⊔ Q = ⊤) (hY : Y ≠ ⊤) (hpY : ¬ p ∣ Y.index) :
    ∃ q, q.Prime ∧ q ∣ Nat.card K ∧ q ^ orderOf (q : ZMod p) ∣ Y.index := by
  obtain ⟨g, hgx⟩ := exists_conj_mem_of_not_dvd hQ hpY
  -- conjugate `Y` so that it contains `Q`
  set Y₁ := Y.map ((MulAut.conj g : H ≃* H) : H →* H) with hY₁
  have hidx : Y₁.index = Y.index := Subgroup.index_map_equiv Y (MulAut.conj g)
  have hQY : Q ≤ Y₁ := by
    intro x hx
    refine ⟨g⁻¹ * x * g, hgx x hx, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group
  have hY₁ : Y₁ ≠ ⊤ := by
    intro h
    apply hY
    rw [← Subgroup.index_eq_one, ← hidx, h, Subgroup.index_top]
  -- `W = Y₁ ⊓ K` is a proper `Q`-invariant subgroup of `K`
  have hWQ : Q ≤ Subgroup.normalizer ((Y₁ ⊓ K : Subgroup H) : Set H) :=
    (le_inf (hQY.trans Subgroup.le_normalizer) Subgroup.le_normalizer_of_normal).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Y₁) (K := K))
  have hsup₁ : Y₁ ⊔ K = ⊤ :=
    eq_top_iff.mpr (hsup ▸ sup_le le_sup_right (hQY.trans le_sup_left))
  have hWne : Y₁ ⊓ K ≠ K := by
    intro h
    apply hY₁
    rw [← hsup₁]
    exact (sup_eq_left.mpr (inf_eq_right.mp h)).symm
  have hYW : Y.index = (Y₁ ⊓ K).relIndex K := by
    rw [← hidx, ← Subgroup.relIndex_top_right, ← hsup₁, relIndex_sup_normal]
  rw [hYW]
  exact cyclotomic_block hQ hK hKQ inf_le_right hWne hWQ

end Core

end CyclotomicBlock

end Erdos274
