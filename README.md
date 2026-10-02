# Herzog–Schönheim for solvable groups, in Lean 4

A Lean 4/mathlib formalisation of the **Herzog–Schönheim conjecture for every solvable
group**, finite or infinite (and its consequence, the cardinality form of Erdős problem 274). The conjecture for arbitrary groups
remains open.

The theorem: if a solvable group is partitioned into finitely many left cosets of
subgroups, with at least two parts, then two of the subgroups have the same index.
The head file is
[`KnownCases/Solvable.lean`](Erdos274/KnownCases/Solvable.lean):

- `Erdos274.herzog_schonheim.variants.solvable`: equal subgroup indices.
- `Erdos274.erdos_274.variants.solvable`: equal subgroup cardinalities.
- `Erdos274.erdos_274.variants.solvable_fintype`: the finite cardinality variant.

The proof uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
and contains no `sorry`.

## Layout

- `Erdos274/Defs.lean`: the exact-cover type `Erdos274.Group.ExactCovering`.
- `Erdos274/KnownCases/Solvable/`: the finite solvable proof (quotient
  cosets, cyclotomic divisibility of local indices, weighted divisor sets, and a separate
  argument at the prime 7).
- `Erdos274/KnownCases/Solvable.lean`: the finite theorem, then the descent
  of the arbitrary case to the finite quotient by the common core of the covering
  subgroups.
- The remaining directories under `Erdos274/` (`Arithmetic`, `Counting`,
  `ExactCovering`, `FiniteGroup`) hold the supporting lemmas the proof imports.

This repository contains exactly the import closure of the head file; nothing else.

## Build

Lean and mathlib are pinned by `lean-toolchain` and `lakefile.toml`.

```text
lake exe cache get
lake build
```

To check the axioms of the main theorem, add to any file importing the head module:

```lean
#print axioms Erdos274.herzog_schonheim.variants.solvable
```

## Provenance

The code was developed with AI assistance (Claude and OpenAI Codex models); the
`Co-Authored-By` trailers in the commit history record this. The history was filtered to the
files in the proof's import closure, so early commits may not build on their own; the tip does.

Licensed under the Apache License 2.0 (see `LICENSE`).

## Palomar layout

This repository is laid out for the [Palomar](https://palomar-registry.org) registry.

- `Challenge.lean`: the audited statement. It imports Mathlib only and restates the
  exact-covering structure `Erdos274.Group.ExactCovering` verbatim; its theorems
  (`Erdos274.Palomar.herzog_schonheim_solvable` and `erdos_274_solvable`)
  are left as `sorry`.
- `Solution.lean`: proves them from the head theorems in `Erdos274/KnownCases/Solvable.lean`.
- `comparator.json`: the Comparator configuration pairing the two.
- `formalization.yaml`: provenance, sources, authorship, AI involvement and limitations.

Every Lean file uses the module system. The proof assumes `[Group.IsSolvable G]` throughout;
the conjecture for arbitrary groups is **not** claimed. Literature status: a search on
2026-09-24 found no prior proof of the solvable case (the only claim, Burkhart,
arXiv:1901.10131, was withdrawn). Novelty is unconfirmed by a specialist or MathSciNet,
and no human expert has reviewed the proof; the Lean development is machine-checked.

## Literature and status

The Herzog–Schönheim conjecture (1974) is open for arbitrary groups.
What was known before this development, as far as the maintainer has checked:

- It reduces to finite groups (B. H. Neumann 1954; Korec–Znám 1977).
- It holds for finite nilpotent groups (Berger–Felzenbaum–Fraenkel, Canad. Math. Bull. 29, 1986)
  and for pyramidal groups, which include supersolvable groups (Berger–Felzenbaum–Fraenkel,
  Fund. Math. 128, 1987); for groups with a normal top Sylow subgroup and via a union bound
  on cosets (Sun, J. Algebra 273, 2004); under prime-factor conditions (Ginosar–Schnabel 2011);
  for all groups of order below 1440 (Margolis–Schnabel, arXiv:1803.03569); and for simple and
  symmetric groups (Garonzi–Margolis, arXiv:2509.25118).
- The only claim for all solvable groups that the maintainer found, Burkhart
  (arXiv:1901.10131), was withdrawn in 2019 because of a gap in its Lemma 1.

The theorem proved here, for every solvable group, finite or infinite, is not a consequence of
those results. A search on 2026-09-24 (arXiv, zbMATH, erdosproblems.com, the web) found no prior
proof. MathSciNet has not been searched and no specialist has reviewed the result, so novelty is
**unconfirmed**. The reduction to finite quotients and Sun's union bound are used; the rest of the
argument, a least-counterexample analysis at the largest prime divisor of the order with a
separate argument at the prime 7, is the content of this development. The Lean proof is
machine-checked; the informal paper is not part of this repository.

The statements match the formal-conjectures file
[`FormalConjectures/ErdosProblems/274.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/274.lean),
whose `Group.ExactCovering` structure is copied field for field. The index-form theorem is the
upstream `herzog_schonheim` with `[Group.IsSolvable G]` added; the cardinality-form theorem has the
conclusion of upstream `erdos_274` (Erdős problem 274, which asks for equal cardinality and follows
from equal index) and of `erdos_274.variants.abelian`, with
`[Group.IsSolvable G]` added.
