# Herzog–Schönheim for solvable groups, in Lean 4

A Lean 4/mathlib formalisation of the **Herzog–Schönheim conjecture for every solvable
group**, finite or infinite (Erdős problem 274). The conjecture for arbitrary groups
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
