# Ringel's Conjecture in Lean 4

<p align="center">
  <a href="https://github.com/walidelkersh/Ringel/actions/workflows/lean_action_ci.yml"><img src="https://github.com/walidelkersh/Ringel/actions/workflows/lean_action_ci.yml/badge.svg" alt="CI"></a>
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

The current top-level theorem surface routes through the source package
`CaseABSourceStatement` in [`Ringel/CaseSource.lean`](Ringel/CaseSource.lean), which packages
the Case A and Case B source statements used by the main theorem. The older explicit-input
wrappers remain only in legacy helper files.

## Current state

Lean formalizes the deterministic combinatorial backbone: the ND-colouring and its
2-factorization, the split lemma and its tree/forest counting infrastructure, the case division,
the Case A walk-sum embedding, the Case C greedy core embedding, the Case AB source package,
and the Kotzig cyclic-shift construction that extends one rainbow copy to an edge-decomposition
of $K_{2n+1}$.

The §6 development defines a finite joint probability space for the near-embedding argument.
`SmallTreeEmbeddingOutcome` stores the rainbow embedding, available vertex and colour reservoirs,
independent leftovers, and their avoidance properties. Separate lemmas prove the local greedy
extension, transfer repletion across complements and retained edges, and extract a successful
finite outcome from a positive probability bound.

Tracked Lean source contains no `sorry`, `admit`, `axiom`, or `sorryAx` declarations. The global
theorem now depends on the source package rather than the older explicit inputs
`CaseAEmbeddingInput` and `CaseBEmbeddingInput`. Those names still appear in legacy helper files,
but they no longer sit on the main theorem path. GitHub Actions provides the authoritative build
check.

See the [blueprint](https://walidelkersh.github.io/Ringel/blueprint/) for the proof
architecture and dependency graph.

## Build

```bash
git clone https://github.com/walidelkersh/Ringel.git && cd Ringel
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
