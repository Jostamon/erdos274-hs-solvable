module

public import Erdos274.KnownCases.Solvable


/-!
# Solution: Herzog–Schönheim for solvable groups

Proofs of the three `Erdos274.Palomar` declarations of `Challenge`.  They are the
head theorems of the development (`Erdos274.KnownCases.Solvable`), restated under
the Challenge's names; `Erdos274.Group.ExactCovering` is the same structure as in
the Challenge (`Erdos274/Defs.lean`).
-/

@[expose] public section

open scoped Pointwise Cardinal

namespace Erdos274.Palomar

theorem herzog_schonheim_solvable {G : Type*} [Group G]
    [Group.IsSolvable G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (hι : 1 < Fintype.card ι) (P : Group.ExactCovering G ι) :
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index :=
  Erdos274.herzog_schonheim.variants.solvable hG hι P

theorem erdos_274_solvable {G : Type*} [Group G]
    [Group.IsSolvable G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) :=
  Erdos274.erdos_274.variants.solvable hG P hι

theorem erdos_274_solvable_fintype {G : Type*} [Fintype G] [Group G]
    [Group.IsSolvable G] (hG : 1 < Fintype.card G) {ι : Type*} [Fintype ι]
    (P : Group.ExactCovering G ι) (hι : 1 < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ #(P.parts i) = #(P.parts j) :=
  Erdos274.erdos_274.variants.solvable_fintype hG P hι

end Erdos274.Palomar
