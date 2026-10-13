# HolomorphicAnosov

Lean 4 formalization of Jiesong Zhang, *Codimension-one holomorphic Anosov diffeomorphisms* [arXiv:2609.37695](https://arxiv.org/abs/2609.37695): Theorem A and Theorems 1.1, 1.2, 1.3, including the parts of Ghys's 1995 classification of holomorphic Anosov systems that the paper relies on:

- É. Ghys, *Holomorphic Anosov systems*, Invent. Math. **119** (1995), no. 3, 585–614.

Built over Mathlib with the [SHEAF](https://github.com/frenzymath/SHEAF) (Scalable Hierarchical Engine for Autonomous Formalization) pipeline.

## Layout

- `Comparator/` — `Challenge.lean` imports only Mathlib and contains all definitions and the four theorem statements; `Solution.lean` contains proofs of the same statements. Checked by the [Lean comparator](https://github.com/leanprover/comparator).
- `HolomorphicAnosov/` — the library with the proofs.

## Status

Complete. The four theorems modulo one input (see below) are proved with no `sorry`; their proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

One assumption is a hypothesis of the statements, not proved: Theorems A, 1.1 and 1.3 take `(HS : HomotopyTorusRigidity)`, the assertion that for `n ≥ 5` every closed smooth `n`-manifold homotopy equivalent to the torus `T^n` is homeomorphic to it. This is the Borel conjecture for tori, proved by W.-C. Hsiang and C. T. C. Wall in 1969 (*On homotopy tori II*, Bull. London Math. Soc. **1** (1969), 341–342); it is a classical result, not specific to the paper. It is a `Prop` defined in the challenge file, not a Lean axiom. Theorem 1.2 does not use it.

Lean comparator accepts `Comparator/Solution.lean` against `Comparator/Challenge.lean` ("Your solution is okay!").

Lean/Mathlib version: `leanprover/lean4:v4.35.0-rc1`.

## Checking

```
lake exe cache get        # Mathlib cache
lake build                # the library and the two comparator files
lake env comparator Comparator/config.json
```

The last command needs `comparator`, `lean4export` (built with the toolchain in `lean-toolchain`) and `landrun` on the `PATH`.