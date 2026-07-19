# Ringel's Conjecture in Lean 4

<p align="center">
  <a href="https://github.com/walidelkersh/Ringel/actions/workflows/lean_action_ci.yml"><img src="https://github.com/walidelkersh/Ringel/actions/workflows/lean_action_ci.yml/badge.svg" alt="CI"></a>
  <a href="https://walidelkersh.github.io/Ringel/blueprint/"><img src="https://img.shields.io/badge/Blueprint-WIP-blue" alt="Blueprint"></a>
  <a href="https://walidelkersh.github.io/Ringel/"><img src="https://img.shields.io/badge/Website-ready-green" alt="Website"></a>
  <img src="https://img.shields.io/badge/Lean-4.30.0-blue" alt="Lean Version">
  <img src="https://img.shields.io/badge/Mathlib-v4.30.0-purple" alt="Mathlib Version">
</p>

A Lean 4 formalization of the Montgomery–Pokrovskiy–Sudakov proof of Ringel's conjecture
for sufficiently large \(n\) ([arXiv:2001.02665](https://arxiv.org/abs/2001.02665)).

Ringel conjectured in 1963 that every tree \(T\) with \(n\) edges decomposes the complete graph
\(K_{2n+1}\) into \(2n+1\) edge-disjoint copies. The formalization separates the deterministic
graph theory from the source-level Case A and Case B results.

## Formal statement

The public theorem is in Ringel/Statement.lean:

```lean
universe u

theorem ringel_conjecture_large :
    CaseABSourceStatement.{u} →
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type u} [Finite V] (T : SimpleGraph V),
        T.IsTree → T.edgeSet.ncard = n →
        ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
          Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
          ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1)))
```

CaseABSourceStatement in Ringel/CaseSource.lean is the single source-level package used by
the public theorem. It records the Case A and Case B statements at the level required by the
paper. The current repository does not claim that this package has been derived unconditionally
from the MPS probability and absorption arguments.

The all-\(n\) conjecture remains open and is not a target of this repository.

## Current formalized scope

The verified Lean development includes:

- the near-difference colouring of \(K_{2n+1}\) and its 2-factorization;
- tree splitting, case division, and the associated counting lemmas;
- the deterministic embedding and leaf-extension infrastructure for Case A;
- the Case C core and leaf-packing constructions;
- finite probability spaces and reservoir bookkeeping for the near-embedding layer;
- the Kotzig cyclic-shift argument that turns one rainbow copy into a decomposition;
- the source-package interface and its assembly into the public theorem.

The remaining research boundary lies in the unconditional Case A and Case B source results:
the MPS random near-embedding, concentration and repletion estimates, exact-colour matching,
path absorption, and the associated asymptotic parameter hierarchy. These results are represented
by explicit source statements rather than hidden placeholders.

A repository-wide Lean-source audit found no sorry, sorryAx, admit, axiom, opaque, or
implemented_by declarations. GitHub Actions is the authoritative build check.

## Documentation

- [Proof blueprint](https://walidelkersh.github.io/Ringel/blueprint/)
- [MPS source-to-Lean map](PAPER_MAPPING.md)
- [Case A colour-cover audit](docs/CASE_A_COLOURCOVER_AUDIT.md)
- [Near-embedding audit](docs/NEAR_EMBEDDING_AUDIT.md)
- [Reservoir-law audit](docs/NEAR_EMBEDDING_RESERVOIR_AUDIT.md)
- [GitHub Pages site](https://walidelkersh.github.io/Ringel/)

The blueprint describes the dependency structure. The mapping and audit documents record the
formal boundary between proved Lean infrastructure and source-level mathematics still to encode.

## Build

```bash
git clone https://github.com/walidelkersh/Ringel.git
cd Ringel
lake exe cache get
lake build
```

Requires [elan](https://leanprover.github.io/lean4/doc/setup.html). The toolchain is pinned
by lean-toolchain.

## Reference

R. Montgomery, A. Pokrovskiy, B. Sudakov.
[*A proof of Ringel's Conjecture*](https://arxiv.org/abs/2001.02665).
Geom. Funct. Anal. **31** (2021), 663–720.

License: Apache 2.0.
