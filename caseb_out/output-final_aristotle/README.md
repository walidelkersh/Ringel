This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Ringel's Conjecture in Lean 4

<p align="center">
  <a href="https://github.com/Doublew08/Ringel/actions/workflows/lean_action_ci.yml"><img src="https://github.com/Doublew08/Ringel/actions/workflows/lean_action_ci.yml/badge.svg" alt="CI"></a>
  <a href="https://walidelkersh.github.io/Ringel/blueprint/"><img src="https://img.shields.io/badge/Blueprint-WIP-blue" alt="Blueprint"></a>
  <a href="https://walidelkersh.github.io/Ringel/"><img src="https://img.shields.io/badge/Website-ready-green" alt="Website"></a>
  <img src="https://img.shields.io/badge/Lean-4.30.0-blue" alt="Lean Version">
  <img src="https://img.shields.io/badge/Mathlib-v4.30.0-purple" alt="Mathlib Version">
</p>

A Lean 4 formalization of the Montgomery–Pokrovskiy–Sudakov proof of Ringel's conjecture
for sufficiently large $n$ ([arXiv:2001.02665](https://arxiv.org/abs/2001.02665)).

Ringel conjectured in 1963 that every tree $T$ with $n$ edges decomposes the complete graph
$K_{2n+1}$ into $2n+1$ edge-disjoint copies. Montgomery, Pokrovskiy, and Sudakov proved this
for all sufficiently large $n$. The formalized statement:

```lean
theorem ringel_conjecture_large :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
        Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
        ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1)))
```

The statements live in [`Ringel/Statement.lean`](Ringel/Statement.lean). The all-$n$ form
is open in general and not a target of this project.

## Current state

The project compiles with zero errors. The deterministic combinatorial backbone of the
proof is fully formalized and axiom-clean: the ND-colouring and its 2-factorization,
the split lemma with all supporting tree/forest counting infrastructure (~956 lines),
the case division, the walk-sum tree embedding for Case A, the greedy core embedding for
Case C, and the Kotzig cyclic-shift decomposition that turns a single rainbow copy into a
full edge-decomposition of $K_{2n+1}$.

Four `sorry` sites remain, all probabilistic or extremal: Littlewood–Offord
anticoncentration (`CaseA.lean`), absorption matching (`CaseA.lean`), the full bare-path
embedding (`CaseB.lean`), and leaf extension (`CaseC.lean`). These require machinery
Mathlib does not yet provide.

See the [blueprint](https://walidelkersh.github.io/Ringel/blueprint/) for the proof
architecture and dependency graph.

## Build

```bash
git clone https://github.com/Doublew08/Ringel.git && cd Ringel
lake exe cache get
lake build
```

Requires [elan](https://leanprover.github.io/lean4/doc/setup.html). The toolchain is pinned
by `lean-toolchain`.

## References

R. Montgomery, A. Pokrovskiy, B. Sudakov.
[*A proof of Ringel's Conjecture*](https://arxiv.org/abs/2001.02665).
Geom. Funct. Anal. **31** (2021), 663–720.

License: Apache 2.0.
