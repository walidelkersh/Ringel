# Audit: MPS §4 `colourcover`

## Scope

The focused module `Ringel/CaseAColourCover.lean` formalizes `section4.tex`, lines 96–111. No changes were made to `Ringel/CaseA.lean`, `Ringel/CaseB.lean`, or `Ringel/Statement.lean`.

## Formal statement

`Ringel.colourcover` is parameterized by:

- the finite vertex set `Fin (2*n+1)` and colour set `Fin n`;
- an arbitrary colouring satisfying the existing `IsTwoFactorization` primitive;
- disjoint finite vertex sets `X,V`;
- allowed and prescribed colour sets `C,C'`;
- an explicit repletion integer `repletion`.

The theorem constructs a `PerfectRainbowMatching colour X V D` for some used-colour set `D`, with
`C' ⊆ D ⊆ C' ∪ C`. Thus it is perfect on `X`, has pairwise distinct targets in `V`, is rainbow,
uses every prescribed colour, and uses no colour outside the prescribed or allowed sets.

`Ringel.ndColourcover` specializes this result to the existing ND-colouring and discharges the
factorization hypothesis with `ndColouring_isTwoFactorization`.

## Exact replacement for asymptotics

The proof uses precisely these finite inequalities:

1. `4 * C'.card ≤ repletion` for the prescribed-colour phase. Each earlier chosen edge can rule
   out at most four ordered `X × V` edges of the next colour (at most two through either endpoint).
2. `3 * X.card ≤ allowedColourDegree colour C V x` for every vertex `x`. During completion, each
   earlier choice rules out at most one target and at most two edges of its colour.

These are direct finite forms of the two greedy estimates in the paper. The paper's assumptions
`|C'| ≤ νn`, `10νn`-repletion, `|X| ≤ λn`, and allowed-colour degree at least `3λn` imply these
bounds (with ample slack, subject to the paper's integral interpretation).

The project primitive `IsReplete` is a minimum vertex-neighbour condition, while the paper defines
pair repletion colour-by-colour. To state the cited lemma faithfully without altering existing
primitives, the focused module introduces `ColourPairReplete`, counting ordered `X × V` edges of
each colour.

## Proof decomposition

The checked construction consists of:

- a generic finite greedy conflict-choice lemma;
- the prescribed-colour matching, using colour-pair repletion and local degree two;
- deletion estimates for prescribed endpoints and colours;
- greedy completion with fresh targets and fresh allowed colours;
- explicit assembly into the existing `PerfectRainbowMatching` structure.

## Lean 4.30 compatibility repair

Lean 4.30 parses applications such as `Sym2.mk p` and `Sym2.mk (p.1, p.2)` as partially applied
constructor functions, rather than as symmetric pairs. Every such edge expression in the module
was replaced by the project's established notation `s(p.1, p.2)`. In particular, the occurrences
inside `completion_conflict_card_le_three` now denote exactly the same unordered edge as the
lemma's conclusion. This is a representation-only correction: no theorem statement, hypothesis,
cardinality bound, or mathematical argument was changed.

Once those malformed terms elaborated, Lean 4.30 also exposed a brittle `grind` assembly in
`prescribed_colour_matching`. Its bad relation was reduced to the two same-side endpoint conflicts
actually required by the conclusion. The existing four-conflict bound still proves the needed
bound by monotonicity, so this is proof-preserving and does not alter the theorem statement.

## Verification

Targeted command under the repository toolchain and Mathlib v4.30.0:

```text
lake build Ringel.CaseAColourCover
```

Result: successful. A source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, `implemented_by`,
or `exact?` in the module.
