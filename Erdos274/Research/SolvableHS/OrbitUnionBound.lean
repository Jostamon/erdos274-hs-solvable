/-
Copyright (c) 2026 Murali Menon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Murali Menon
-/
import Erdos274.Arithmetic.DivisorMass
import Erdos274.FiniteGroup.PrimeNormalChain
import Erdos274.FiniteGroup.PrimaryPart
import Erdos274.FiniteGroup.SolvablePrimeNormalChain
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Solvable HS: the orbit union bound (Lemma O)

`SOLVABLE_HS_TRACK.md` §9.5.  Let `G` act on a finite set `Ω`, let `H ≤ G`
carry a prime-normal chain, and let `Oᵢ` be orbits of subgroups `Kᵢ ≤ H`.
If every `|Oᵢ|` is coprime to the order of every point stabiliser in `H` along
`Oᵢ`, then

    Σ_{d ∣ some |Oᵢ|} φ(d) ≤ |⋃ Oᵢ|.

For `Ω = G ⧸ X` this is the orbit union bound on `X∖G` of the track; for the
regular action (`X = 1`) it is Sun 2004, Theorem 3.1 (`UnionBound.lean`).

**Coset convention.**  The track states Lemma O for *right* cosets `X∖G`, with
`K` acting by right multiplication, `Xy ↦ Xyk`.  Mathlib's `G ⧸ X` is the type
of *left* cosets `yX`, with `G` acting by left multiplication, `k • yX = kyX`.
Inversion `Xy ↦ y⁻¹X` is a bijection `X∖G ≃ G ⧸ X` carrying `Xyk` to
`k⁻¹ • y⁻¹X`.  Since `k ↦ k⁻¹` is a bijection of `K`, it maps each `K`-orbit on
`X∖G` onto a `K`-orbit on `G ⧸ X` of the same size.  It preserves unions, and
it carries point stabilisers `K ∩ y⁻¹Xy` to point stabilisers. So
`mass_le_ncard_iUnion_orbit_quotient` is exactly the track's statement.  The
general theorem `mass_le_ncard_iUnion_orbit` is stated for an arbitrary
`G`-set, so it is convention-free.

The proof inducts along the chain.  At a step `L ◁ H` of prime index `q`,
each orbit either stays a single `(Kᵢ ⊓ L)`-orbit or splits into `q` of them
(`card_orbit_inf_mul_relIndex`); splitting forces `q ∣ |Oᵢ|`, so by
coprimality it only happens where the stabilisers lie in `L`, and there the
`L`-orbits carry a `H ⧸ L`-valued label that the split pieces run through.
The divisor arithmetic is `mass_biUnion_le_sum_mass_fiber`.

No research axiom occurs in this file.
-/

namespace Erdos274

open MulAction Finset

universe u v w

variable {G : Type u} [Group G] {Ω : Type v} [MulAction G Ω]

section Helpers

/-- The stabiliser in a subgroup `K` is the stabiliser in `G` restricted to `K`. -/
lemma stabilizer_subgroup_eq (K : Subgroup G) (x : Ω) :
    stabilizer K x = (stabilizer G x).subgroupOf K := by
  ext k
  simp [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]

/-- Orbit–stabiliser for a subgroup, as a relative index. -/
lemma ncard_orbit_subgroup (K : Subgroup G) (x : Ω) :
    (orbit K x).ncard = (stabilizer G x).relIndex K := by
  rw [← index_stabilizer, stabilizer_subgroup_eq]
  rfl

/-- At a normal step `L ◁ H` of prime index `q`, a subgroup `A ≤ H` meets `L`
with relative index `1` or `q`. -/
lemma relIndex_eq_one_or_of_prime {H L A : Subgroup G} (hAH : A ≤ H)
    (hN : (L.subgroupOf H).Normal) (hq : (L.relIndex H).Prime) :
    L.relIndex A = 1 ∨ L.relIndex A = L.relIndex H := by
  have hdvd : L.relIndex A ∣ L.relIndex H := by
    rw [← Subgroup.relIndex_subgroupOf hAH]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  exact (Nat.dvd_prime hq).mp hdvd

/-- **Orbit splitting identity.**  For `K ≤ G`, `L ≤ G` and a point `x`:
`|O_{K ⊓ L}(x)| · [K : K ⊓ L] = [K_x : K_x ⊓ L] · |O_K(x)|`. -/
lemma card_orbit_inf_mul_relIndex (K L : Subgroup G) (x : Ω) :
    (orbit (K ⊓ L : Subgroup G) x).ncard * L.relIndex K =
      L.relIndex (stabilizer G x ⊓ K) * (orbit K x).ncard := by
  rw [ncard_orbit_subgroup, ncard_orbit_subgroup]
  have h1 := Subgroup.relIndex_inf_mul_relIndex (stabilizer G x) L K
  have h2 := Subgroup.relIndex_inf_mul_relIndex L (stabilizer G x) K
  rw [inf_comm L K, inf_comm (stabilizer G x) L] at *
  rw [h1, ← h2]

/-- A subgroup all of whose `y`-conjugates (`y ∈ H`) lie in `L ◁ H` lies in
`L`: transport of "`≤ L`" along conjugation inside `H`. -/
lemma le_of_conj_le {H L A : Subgroup G} (hLH : L ≤ H)
    (hN : (L.subgroupOf H).Normal) {y : G} (hy : y ∈ H)
    (h : ∀ s ∈ A, y * s * y⁻¹ ∈ L) : A ≤ L := by
  intro s hs
  have hys := h s hs
  have hmem : (⟨y * s * y⁻¹, hLH hys⟩ : H) ∈ L.subgroupOf H := hys
  have := hN.conj_mem _ hmem ⟨y⁻¹, H.inv_mem hy⟩
  simpa [Subgroup.mem_subgroupOf, mul_assoc] using this

end Helpers

section Label

/-! ### The `H ⧸ L` label

Fix `L ≤ H` with `L ◁ H`.  In each `H`-orbit choose a base point `b`; write
each point as `h • b` with `h ∈ H`.  Where `H_b ≤ L`, the coset `hL` is well
defined and `H`-equivariant; elsewhere the label is `1`. -/

variable (H : Subgroup G)

/-- A chosen base point of the `H`-orbit of `ω`. -/
noncomputable def orbitBase (ω : Ω) : Ω :=
  (Quotient.mk (orbitRel H Ω) ω).out

lemma orbitBase_mem (ω : Ω) : orbitBase H ω ∈ orbit H ω :=
  Quotient.mk_out (s := orbitRel H Ω) ω

lemma orbitBase_smul (x : H) (ω : Ω) : orbitBase H (x • ω) = orbitBase H ω := by
  unfold orbitBase
  congr 1
  exact Quotient.sound (mem_orbit ω x)

lemma exists_smul_orbitBase (ω : Ω) : ∃ h : H, h • orbitBase H ω = ω :=
  mem_orbit_symm.mp (orbitBase_mem H ω)

/-- The element of `H` carrying the base point to `ω`. -/
noncomputable def orbitLift (ω : Ω) : H := (exists_smul_orbitBase H ω).choose

lemma orbitLift_smul (ω : Ω) : orbitLift H ω • orbitBase H ω = ω :=
  (exists_smul_orbitBase H ω).choose_spec

variable (L : Subgroup G) [hN : (L.subgroupOf H).Normal]

open Classical in
/-- The label of a point in `H ⧸ L`. -/
noncomputable def orbitLabel (ω : Ω) : H ⧸ L.subgroupOf H :=
  if H ⊓ stabilizer G (orbitBase H ω) ≤ L then (orbitLift H ω : H ⧸ L.subgroupOf H)
  else 1

variable {H L}

/-- "`H_x ≤ L`" is the same at a point and at its base point. -/
lemma stab_le_iff_base (hLH : L ≤ H) (ω : Ω) :
    H ⊓ stabilizer G ω ≤ L ↔ H ⊓ stabilizer G (orbitBase H ω) ≤ L := by
  set b := orbitBase H ω
  set y := orbitLift H ω
  have hyb : (y : G) • b = ω := orbitLift_smul H ω
  constructor
  · intro h
    refine le_of_conj_le hLH hN y.2 fun s hs ↦ h (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact H.mul_mem (H.mul_mem y.2 (Subgroup.mem_inf.mp hs).1) (H.inv_mem y.2)
    · have hsb : s • b = b := mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hs).2
      rw [mem_stabilizer_iff, mul_smul, mul_smul, ← hyb, inv_smul_smul, hsb]
  · intro h
    refine le_of_conj_le hLH hN (H.inv_mem y.2) fun s hs ↦ h (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · exact H.mul_mem (H.mul_mem (H.inv_mem y.2) (Subgroup.mem_inf.mp hs).1)
        (H.inv_mem (H.inv_mem y.2))
    · have hsω : s • ω = ω := mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hs).2
      rw [mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, hyb, hsω]
      exact inv_smul_eq_iff.mpr hyb.symm

/-- Where stabilisers lie in `L`, the label is `H`-equivariant. -/
lemma orbitLabel_smul {ω : Ω} (hc : H ⊓ stabilizer G (orbitBase H ω) ≤ L) (x : H) :
    orbitLabel H L (x • ω) = (x : H ⧸ L.subgroupOf H) * orbitLabel H L ω := by
  have hb : orbitBase H (x • ω) = orbitBase H ω := orbitBase_smul H x ω
  have hc' : H ⊓ stabilizer G (orbitBase H (x • ω)) ≤ L := by rwa [hb]
  simp only [orbitLabel, hc, hc', ↓reduceIte]
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
  set b := orbitBase H ω
  set l' := orbitLift H (x • ω) with hl'
  set l := orbitLift H ω with hl
  have h1 : l' • b = x • ω := by
    have := orbitLift_smul H (x • ω)
    rwa [hb] at this
  have h2 : l • b = ω := orbitLift_smul H ω
  have hstab : (l'⁻¹ * (x * l)) • b = b := by
    rw [mul_smul, mul_smul, h2, ← h1, inv_smul_smul]
  have hmem : ((l'⁻¹ * (x * l) : H) : G) ∈ H ⊓ stabilizer G b :=
    Subgroup.mem_inf.mpr ⟨Subtype.property _,
      mem_stabilizer_iff.mpr (by simpa [Subgroup.smul_def] using hstab)⟩
  exact hc hmem

/-- The label is constant along `L`. -/
lemma orbitLabel_smul_of_mem (ω : Ω) (x : H) (hx : (x : G) ∈ L) :
    orbitLabel H L (x • ω) = orbitLabel H L ω := by
  by_cases hc : H ⊓ stabilizer G (orbitBase H ω) ≤ L
  · rw [orbitLabel_smul hc, (QuotientGroup.eq_one_iff x).mpr hx, one_mul]
  · have hc' : ¬ H ⊓ stabilizer G (orbitBase H (x • ω)) ≤ L := by
      rwa [orbitBase_smul]
    simp only [orbitLabel, hc, hc', ↓reduceIte]

end Label

section Step

/-! ### One step of the chain -/

variable {H L : Subgroup G} [hN : (L.subgroupOf H).Normal]

lemma relIndex_eq_of_not_le (hq : (L.relIndex H).Prime) {A : Subgroup G} (hAH : A ≤ H)
    (h : ¬ A ≤ L) : L.relIndex A = L.relIndex H :=
  (relIndex_eq_one_or_of_prime hAH hN hq).resolve_left
    fun h1 ↦ h (Subgroup.relIndex_eq_one.mp h1)

/-- "`K_x ≤ L`" is constant along a `K`-orbit. -/
lemma stab_inf_le_iff_smul (hLH : L ≤ H) {K : Subgroup G} (hKH : K ≤ H) (k : K) (ω : Ω) :
    stabilizer G ((k : G) • ω) ⊓ K ≤ L ↔ stabilizer G ω ⊓ K ≤ L := by
  constructor
  · intro h
    refine le_of_conj_le hLH hN (hKH k.2) fun s hs ↦ h (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have hsω : s • ω = ω := mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hs).1
      rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, hsω]
    · exact K.mul_mem (K.mul_mem k.2 (Subgroup.mem_inf.mp hs).2) (K.inv_mem k.2)
  · intro h
    refine le_of_conj_le hLH hN (H.inv_mem (hKH k.2)) fun s hs ↦
      h (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have hsω : s • ((k : G) • ω) = (k : G) • ω :=
        mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hs).1
      rw [mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, hsω, inv_smul_smul]
    · exact K.mul_mem (K.mul_mem (K.inv_mem k.2) (Subgroup.mem_inf.mp hs).2)
        (K.inv_mem (K.inv_mem k.2))

/-- The `(K ⊓ L)`-orbits inside one `K`-orbit all have the same size. -/
lemma ncard_orbit_inf_smul (hLH : L ≤ H) (hq : (L.relIndex H).Prime) {K : Subgroup G}
    (hKH : K ≤ H) (k : K) (ω : Ω) :
    (orbit (K ⊓ L : Subgroup G) ((k : G) • ω)).ncard =
      (orbit (K ⊓ L : Subgroup G) ω).ncard := by
  have e1 := card_orbit_inf_mul_relIndex K L ((k : G) • ω)
  have e2 := card_orbit_inf_mul_relIndex K L ω
  have hO : orbit K ((k : G) • ω) = orbit K ω := by
    rw [← Subgroup.smul_def]
    exact orbit_smul k ω
  have hr : L.relIndex (stabilizer G ((k : G) • ω) ⊓ K) =
      L.relIndex (stabilizer G ω ⊓ K) := by
    have key := stab_inf_le_iff_smul hLH hKH k ω
    by_cases hB : stabilizer G ω ⊓ K ≤ L
    · rw [Subgroup.relIndex_eq_one.mpr hB, Subgroup.relIndex_eq_one.mpr (key.mpr hB)]
    · rw [relIndex_eq_of_not_le hq (inf_le_right.trans hKH) hB,
        relIndex_eq_of_not_le hq (inf_le_right.trans hKH) fun h ↦ hB (key.mp h)]
  rw [hO, hr] at e1
  have hK0 : 0 < L.relIndex K := by
    rcases relIndex_eq_one_or_of_prime hKH hN hq with h | h <;> rw [h]
    · exact one_pos
    · exact hq.pos
  exact Nat.eq_of_mul_eq_mul_right hK0 (e1.trans e2.symm)

/-- Coprimality turns `q ∣ |O|` into `H_x ≤ L`. -/
lemma stab_le_of_dvd (hq : (L.relIndex H).Prime) (x : Ω) {n : ℕ}
    (hcop : Nat.Coprime n (Nat.card (H ⊓ stabilizer G x : Subgroup G)))
    (hdvd : L.relIndex H ∣ n) : H ⊓ stabilizer G x ≤ L := by
  by_contra h
  have h1 := relIndex_eq_of_not_le hq (inf_le_left : H ⊓ stabilizer G x ≤ H) h
  have h2 : L.relIndex H ∣ Nat.card (H ⊓ stabilizer G x : Subgroup G) :=
    h1 ▸ Subgroup.relIndex_dvd_card (H := L) (K := H ⊓ stabilizer G x)
  exact hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hdvd h2)

/-- **Same label, same piece.**  Two points of one `K`-orbit with the same label
lie in one `(K ⊓ L)`-orbit, provided `|O_K|` is coprime to `|H_x|`. -/
lemma mem_orbit_inf_of_label [Finite Ω] (hLH : L ≤ H) (hq : (L.relIndex H).Prime)
    {K : Subgroup G} (hKH : K ≤ H) {x y : Ω} (hy : y ∈ orbit K x)
    (hcop : Nat.Coprime (orbit K x).ncard (Nat.card (H ⊓ stabilizer G x : Subgroup G)))
    (hlab : orbitLabel H L y = orbitLabel H L x) : y ∈ orbit (K ⊓ L : Subgroup G) x := by
  obtain ⟨k, rfl⟩ := hy
  dsimp only at hlab ⊢
  by_cases hKL : K ≤ L
  · exact ⟨⟨k, Subgroup.mem_inf.mpr ⟨k.2, hKL k.2⟩⟩, by simp [Subgroup.smul_def]⟩
  have hrK := relIndex_eq_of_not_le hq hKH hKL
  have e := card_orbit_inf_mul_relIndex K L x
  by_cases hs : stabilizer G x ⊓ K ≤ L
  · rw [hrK, Subgroup.relIndex_eq_one.mpr hs, one_mul] at e
    have hc := stab_le_of_dvd hq x hcop (Dvd.intro_left _ e)
    have hcb := (stab_le_iff_base hLH x).mp hc
    have hk : (⟨k, hKH k.2⟩ : H) • x = k • x := by simp [Subgroup.smul_def]
    rw [← hk, orbitLabel_smul hcb] at hlab
    have h1 : ((⟨k, hKH k.2⟩ : H) : H ⧸ L.subgroupOf H) = 1 := mul_eq_right.mp hlab
    have hkL : (k : G) ∈ L :=
      (QuotientGroup.eq_one_iff (N := L.subgroupOf H) (⟨k, hKH k.2⟩ : H)).mp h1
    exact ⟨⟨k, Subgroup.mem_inf.mpr ⟨k.2, hkL⟩⟩, by simp [Subgroup.smul_def]⟩
  · rw [hrK, relIndex_eq_of_not_le hq (inf_le_right.trans hKH) hs] at e
    have hcard : (orbit (K ⊓ L : Subgroup G) x).ncard = (orbit K x).ncard :=
      Nat.eq_of_mul_eq_mul_right hq.pos (e.trans (mul_comm _ _))
    have hsub : orbit (K ⊓ L : Subgroup G) x ⊆ orbit K x := by
      rintro _ ⟨n, rfl⟩
      exact ⟨⟨n, (Subgroup.mem_inf.mp n.2).1⟩, by simp [Subgroup.smul_def]⟩
    have heq : orbit (K ⊓ L : Subgroup G) x = orbit K x :=
      Set.eq_of_subset_of_ncard_le hsub hcard.ge (Set.toFinite _)
    rw [heq]
    exact mem_orbit x k

end Step

/-- Counting a finite set through the fibres of a labelling. -/
lemma ncard_eq_sum_ncard_label {γ : Type*} [Fintype γ] [Finite Ω]
    (S : Set Ω) (f : Ω → γ) : S.ncard = ∑ c : γ, (S ∩ {x | f x = c}).ncard := by
  classical
  have : Fintype Ω := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card' S,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun x _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext x
  simp

/-- **Lemma O (orbit union bound)**, along a prime-normal chain.  If `G` acts on
the finite set `Ω`, `Kᵢ ≤ H`, and each `|Oᵢ| = |Kᵢ • ωᵢ|` is coprime to
`|H ⊓ G_x|` for every `x ∈ Oᵢ`, then the divisor mass of the `|Oᵢ|` is at most
`|⋃ Oᵢ|`. -/
theorem mass_le_ncard_iUnion_orbit [Finite G] [Finite Ω] {H : Subgroup G}
    (c : Subgroup.PrimeNormalChain H) :
    ∀ (κ : Type w) [Fintype κ] (ω : κ → Ω) (K : κ → Subgroup G), (∀ i, K i ≤ H) →
      (∀ i, ∀ x ∈ orbit (K i) (ω i), Nat.Coprime (orbit (K i) (ω i)).ncard
        (Nat.card (H ⊓ stabilizer G x : Subgroup G))) →
      mass (univ.biUnion fun i ↦ ((orbit (K i) (ω i)).ncard).divisors) ≤
        (⋃ i, orbit (K i) (ω i)).ncard := by
  induction c with
  | bot =>
    intro κ _ ω K hK _
    have hsing : ∀ i, orbit (K i) (ω i) = {ω i} := by
      intro i
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        have hk : (k : G) = 1 := Subgroup.mem_bot.mp (hK i k.2)
        simp [Subgroup.smul_def, hk]
      · rintro rfl
        exact mem_orbit_self _
    simp only [hsing, Set.ncard_singleton, Nat.divisors_one]
    rcases isEmpty_or_nonempty κ with hκ | hne
    · simp [mass]
    · obtain ⟨i⟩ := hne
      have : Nonempty κ := ⟨i⟩
      have hb : (univ.biUnion fun _ : κ ↦ ({1} : Finset ℕ)) = {1} := by
        ext d
        simp
      rw [hb]
      simp only [mass, Finset.sum_singleton, Nat.totient_one]
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨ω i, Set.mem_iUnion.mpr ⟨i, rfl⟩⟩
  | @step H L hLH hN hq tail ih =>
    intro κ _ ω K hK hcop
    classical
    set q := L.relIndex H with hq_def
    have hqpos : 0 < q := hq.pos
    have : Fintype (H ⧸ L.subgroupOf H) := Fintype.ofFinite _
    have hγ : Fintype.card (H ⧸ L.subgroupOf H) = q := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    set W : κ → ℕ := fun i ↦ (orbit (K i) (ω i)).ncard with hW
    set w : κ → ℕ := fun i ↦ (orbit (K i ⊓ L : Subgroup G) (ω i)).ncard with hw
    have hw0 : ∀ i, w i ≠ 0 := fun i ↦
      ((Set.ncard_pos (Set.toFinite _)).mpr ⟨ω i, mem_orbit_self _⟩).ne'
    set cross : Finset κ :=
      univ.filter fun i ↦ ¬ K i ≤ L ∧ stabilizer G (ω i) ⊓ K i ≤ L with hcross
    have hcrossW : ∀ i ∈ cross, W i = q * w i := by
      intro i hi
      obtain ⟨hKL, hs⟩ := (Finset.mem_filter.mp hi).2
      have e := card_orbit_inf_mul_relIndex (K i) L (ω i)
      rw [relIndex_eq_of_not_le hq (hK i) hKL, Subgroup.relIndex_eq_one.mpr hs,
        one_mul] at e
      rw [mul_comm]
      exact e.symm
    have hlocalW : ∀ i ∉ cross, W i = w i := by
      intro i hi
      have e := card_orbit_inf_mul_relIndex (K i) L (ω i)
      by_cases hKL : K i ≤ L
      · rw [Subgroup.relIndex_eq_one.mpr hKL,
          Subgroup.relIndex_eq_one.mpr (inf_le_right.trans hKL), mul_one, one_mul] at e
        exact e.symm
      · have hs : ¬ stabilizer G (ω i) ⊓ K i ≤ L := fun hs ↦
          hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKL, hs⟩)
        rw [relIndex_eq_of_not_le hq (hK i) hKL,
          relIndex_eq_of_not_le hq (inf_le_right.trans (hK i)) hs, mul_comm] at e
        exact (Nat.eq_of_mul_eq_mul_left hqpos e).symm
    set J : (H ⧸ L.subgroupOf H) → Finset κ := fun c ↦
      univ.filter fun i ↦ ∃ x ∈ orbit (K i) (ω i), orbitLabel H L x = c with hJ
    have hallJ : ∀ i, ∃ c, i ∈ J c := fun i ↦
      ⟨orbitLabel H L (ω i),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ω i, mem_orbit_self _, rfl⟩⟩
    have hcrossJ : ∀ i ∈ cross, ∀ c, i ∈ J c := by
      intro i hi c
      obtain ⟨hKL, _⟩ := (Finset.mem_filter.mp hi).2
      have hdvd : q ∣ W i := ⟨w i, hcrossW i hi⟩
      have hc := stab_le_of_dvd hq (ω i) (hcop i (ω i) (mem_orbit_self _)) hdvd
      have hcb := (stab_le_iff_base hLH (ω i)).mp hc
      obtain ⟨k₀, hk₀K, hk₀L⟩ := SetLike.not_le_iff_exists.mp hKL
      have hg₀ : ((⟨k₀, hK i hk₀K⟩ : H) : H ⧸ L.subgroupOf H) ≠ 1 := fun h ↦
        hk₀L ((QuotientGroup.eq_one_iff (N := L.subgroupOf H)
          (⟨k₀, hK i hk₀K⟩ : H)).mp h)
      have : Fact q.Prime := ⟨hq⟩
      have hcard : Nat.card (H ⧸ L.subgroupOf H) = q := by
        rw [Nat.card_eq_fintype_card, hγ]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_of_prime_card hcard hg₀ (g' := c * (orbitLabel H L (ω i))⁻¹))
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((⟨k₀, hk₀K⟩ : K i) ^ m) • ω i, mem_orbit _ _, ?_⟩
      have hsm : ((⟨k₀, hk₀K⟩ : K i) ^ m) • ω i = ((⟨k₀, hK i hk₀K⟩ : H) ^ m) • ω i := by
        simp [Subgroup.smul_def]
      rw [hsm, orbitLabel_smul hcb, QuotientGroup.mk_zpow, hm, inv_mul_cancel_right]
    set U := ⋃ i, orbit (K i) (ω i) with hU
    have hfib : ∀ c, mass ((J c).biUnion fun i ↦ (w i).divisors) ≤
        (U ∩ {x | orbitLabel H L x = c}).ncard := by
      intro c
      rcases (J c).eq_empty_or_nonempty with hJc | _
      · simp [hJc, mass]
      have hx : ∀ i : J c, ∃ x ∈ orbit (K i) (ω i), orbitLabel H L x = c :=
        fun i ↦ (Finset.mem_filter.mp i.2).2
      choose x hxO hxl using hx
      have hOx : ∀ i : J c, orbit (K i) (x i) = orbit (K i) (ω i) := fun i ↦
        orbit_eq_iff.mpr (hxO i)
      have hPc : ∀ i : J c, (orbit (K i ⊓ L : Subgroup G) (x i)).ncard = w i := by
        intro i
        obtain ⟨k, hk⟩ := hxO i
        dsimp only at hk
        rw [← hk, Subgroup.smul_def]
        exact ncard_orbit_inf_smul hLH hq (hK i) k (ω i)
      have hsubO : ∀ i : J c, orbit (K i ⊓ L : Subgroup G) (x i) ⊆ orbit (K i) (ω i) := by
        intro i
        rw [← hOx i]
        rintro _ ⟨n, rfl⟩
        exact ⟨⟨n, (Subgroup.mem_inf.mp n.2).1⟩, by simp [Subgroup.smul_def]⟩
      have hUc : U ∩ {x | orbitLabel H L x = c} =
          ⋃ i : J c, orbit (K i ⊓ L : Subgroup G) (x i) := by
        ext y
        simp only [hU, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨i, hyi⟩, hyl⟩
          have hiJ : i ∈ J c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hyi, hyl⟩
          refine ⟨⟨i, hiJ⟩, ?_⟩
          have hy' : y ∈ orbit (K i) (x ⟨i, hiJ⟩) := (hOx ⟨i, hiJ⟩) ▸ hyi
          refine mem_orbit_inf_of_label hLH hq (hK i) hy' ?_ ?_
          · rw [hOx ⟨i, hiJ⟩]
            exact hcop i _ (hxO ⟨i, hiJ⟩)
          · rw [hyl, hxl]
        · rintro ⟨i, hyi⟩
          refine ⟨⟨i, hsubO i hyi⟩, ?_⟩
          obtain ⟨n, rfl⟩ := hyi
          dsimp only
          have hn : n • x i = (⟨n, hK i (Subgroup.mem_inf.mp n.2).1⟩ : H) • x i := by
            simp [Subgroup.smul_def]
          rw [hn, orbitLabel_smul_of_mem (H := H) (L := L) (x i)
            ⟨n, hK i (Subgroup.mem_inf.mp n.2).1⟩ (Subgroup.mem_inf.mp n.2).2, hxl]
      have hIH := ih (J c) (fun i ↦ x i) (fun i ↦ K i ⊓ L) (fun _ ↦ inf_le_right) (by
        intro i z hz
        rw [hPc i]
        have hwW : w i ∣ W i := by
          by_cases hi : (i : κ) ∈ cross
          · exact ⟨q, by rw [hcrossW i hi, mul_comm]⟩
          · rw [hlocalW i hi]
        have hdc : Nat.card (L ⊓ stabilizer G z : Subgroup G) ∣
            Nat.card (H ⊓ stabilizer G z : Subgroup G) :=
          Subgroup.card_dvd_of_le (inf_le_inf_right _ hLH)
        exact Nat.Coprime.coprime_dvd_right hdc
          (Nat.Coprime.coprime_dvd_left hwW (hcop i z (hsubO i hz))))
      have hmass : ((J c).biUnion fun i ↦ (w i).divisors) =
          univ.biUnion (fun i : J c ↦
            ((orbit (K i ⊓ L : Subgroup G) (x i)).ncard).divisors) := by
        rw [← biUnion_subtype_univ (J c) (fun i ↦ (w i).divisors)]
        exact Finset.biUnion_congr rfl fun i _ ↦ by rw [hPc i]
      rw [hmass, hUc]
      exact hIH
    calc mass (univ.biUnion fun i ↦ ((orbit (K i) (ω i)).ncard).divisors)
        = mass (univ.biUnion fun i ↦ (W i).divisors) := rfl
      _ ≤ ∑ c, mass ((J c).biUnion fun i ↦ (w i).divisors) :=
          mass_biUnion_le_sum_mass_fiber hq.ne_zero hγ w W hw0 J cross hcrossW hlocalW
            hcrossJ hallJ
      _ ≤ ∑ c, (U ∩ {x | orbitLabel H L x = c}).ncard :=
          Finset.sum_le_sum fun c _ ↦ hfib c
      _ = U.ncard := (ncard_eq_sum_ncard_label U _).symm

/-- In `G ⧸ X` every point stabiliser has the order of `X`. -/
lemma card_stabilizer_quotient [Finite G] (X : Subgroup G) (x : G ⧸ X) :
    Nat.card (stabilizer G x) = Nat.card X := by
  have h1 : (stabilizer G x).index = X.index := index_stabilizer_of_transitive G x
  have h2 := (stabilizer G x).card_mul_index
  have h3 := X.card_mul_index
  rw [h1, ← h3] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero X.index_ne_zero_of_finite) h2

/-- **Lemma O, solvable form** (`SOLVABLE_HS_TRACK.md` §9.5).  In a finite
solvable group `G`, orbits `Oᵢ` of subgroups `Kᵢ` on `G ⧸ X` whose sizes are
coprime to `|X|` satisfy `Σ_{d ∣ some |Oᵢ|} φ(d) ≤ |⋃ Oᵢ|`.  With `X = 1` this is
BFF's Lemma IV for solvable groups (Sun 2004, Thm 3.1).  Mathlib's `G ⧸ X` is
left cosets; the track's right-coset form `X∖G` follows by inversion (see the
module docstring). -/
theorem mass_le_ncard_iUnion_orbit_quotient [Finite G] [Group.IsSolvable G]
    (X : Subgroup G) {κ : Type w} [Fintype κ] (ω : κ → G ⧸ X) (K : κ → Subgroup G)
    (hcop : ∀ i, Nat.Coprime (orbit (K i) (ω i)).ncard (Nat.card X)) :
    mass (univ.biUnion fun i ↦ ((orbit (K i) (ω i)).ncard).divisors) ≤
      (⋃ i, orbit (K i) (ω i)).ncard :=
  mass_le_ncard_iUnion_orbit (Subgroup.PrimeNormalChain.of_isSolvable G) κ ω K
    (fun _ ↦ le_top) fun i x _ ↦ by
      rw [top_inf_eq, card_stabilizer_quotient]
      exact hcop i

end Erdos274
