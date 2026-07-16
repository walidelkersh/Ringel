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

## Verification

Targeted command:

```text
elan run leanprover/lean4:v4.28.0 lake build Ringel.CaseAColourCover
```

Result: successful. A source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, `implemented_by`,
or `exact?` in the module. Kernel axiom inspection of the two exported theorems is recorded by the
final verification run; only standard permitted logical axioms are accepted.
