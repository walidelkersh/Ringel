# Ringel's Conjecture in Lean 4

<p align="center">
  <a href="https://github.com/walidelkersh/Ringel/actions/workflows/lean_action_ci.yml"><img src="https://github.com/walidelkersh/Ringel/actions/workflows/lean_action_ci.yml/badge.svg" alt="CI"></a>
  <a href="https://walidelkersh.github.io/Ringel/blueprint/"><img src="https://img.shields.io/badge/Blueprint-WIP-blue" alt="Blueprint"></a>
  <a href="https://github.com/walidelkersh/Ringel/blob/main/lean-toolchain"><img src="https://img.shields.io/badge/Lean-4.30.0-blue" alt="Lean version"></a>
  <a href="https://github.com/walidelkersh/Ringel/blob/main/LICENSE"><img src="https://img.shields.io/badge/license-Apache--2.0-blue" alt="Apache 2.0 license"></a>
</p>

This project formalizes the Montgomery–Pokrovskiy–Sudakov proof of Ringel's conjecture in Lean 4.

Ringel's conjecture asks whether every tree with \(n\) edges decomposes the complete graph
\(K_{2n+1}\) into \(2n+1\) edge-disjoint copies of the tree. The 2020 MPS proof establishes
this for all sufficiently large \(n\). This repository translates its graph-theoretic and
probabilistic components into machine-checked mathematics.

## The proof strategy

The formalization follows the structure of the paper:

1. Colour the edges of \(K_{2n+1}\) with the near-difference colouring.
2. Find one rainbow copy of the tree in that colouring.
3. Split the tree into Cases A, B, and C according to its leaf and bare-path structure.
4. Handle the three cases with embeddings, matchings, path absorption, and leaf packing.
5. Apply the cyclic-shift construction to turn one rainbow copy into a decomposition of \(K_{2n+1}\).

The formal entry point is ringel_conjecture_large in
[Ringel/Statement.lean](Ringel/Statement.lean).

## Project status

The deterministic graph theory, the case division, the proof assembly, and the Case C construction
are formalized. The project also contains the finite probability and reservoir infrastructure
needed for the remaining parts of the MPS argument.

The unconditional Case A and Case B source arguments are still under development. They contain
the main probabilistic near-embedding, exact-colour matching, and path-absorption work from the
paper. The current Lean interface makes that boundary explicit, so the public theorem records
which source results still need to be completed. The repository does not present those remaining
arguments as finished.

GitHub Actions checks every pushed revision. The tracked Lean source contains no placeholder proof
declarations.

## Repository layout

| Path | Role |
|---|---|
| Ringel/Primitives.lean | Near-difference colouring and basic graph primitives |
| Ringel/TreeStructure.lean | Tree splitting and counting infrastructure |
| Ringel/CaseDivision.lean | Case A/B/C classification |
| Ringel/CaseA.lean | Leaf-rich trees and signed walk-sum embeddings |
| Ringel/CaseB.lean | Bare-path structure and absorption interfaces |
| Ringel/CaseC.lean | Small-core embeddings and Case C assembly |
| Ringel/Prob*.lean | Finite probability and probabilistic matching infrastructure |
| Ringel/NearEmbedding*.lean | Near-embedding and reservoir constructions |
| Ringel/Spine.lean | Rainbow-copy assembly and cyclic shifts |
| Ringel/Statement.lean | Public theorem statements |
| blueprint/ | Generated proof architecture and dependency graph |
| PAPER_MAPPING.md | Paper-to-Lean declaration map |
| docs/ | Focused audits and the project website |

## Build

Install [Lean 4](https://lean-lang.org/lean4/doc/setup.html) through
[elan](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/walidelkersh/Ringel.git
cd Ringel
lake exe cache get
lake build
```

The project pins Lean and Mathlib versions in lean-toolchain and lakefile.toml.

## Documentation

- [Proof blueprint](https://walidelkersh.github.io/Ringel/blueprint/)
- [MPS source-to-Lean map](PAPER_MAPPING.md)
- [Case A colour-cover audit](docs/CASE_A_COLOURCOVER_AUDIT.md)
- [Near-embedding audit](docs/NEAR_EMBEDDING_AUDIT.md)
- [Reservoir-law audit](docs/NEAR_EMBEDDING_RESERVOIR_AUDIT.md)
- [GitHub Pages site](https://walidelkersh.github.io/Ringel/)

## Reference

R. Montgomery, A. Pokrovskiy, and B. Sudakov,
[*A proof of Ringel's Conjecture*](https://arxiv.org/abs/2001.02665),
Geom. Funct. Anal. 31 (2021), 663–720.

## License

[Apache License 2.0](LICENSE)
