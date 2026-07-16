# MPS §6 disjoint-reservoir law audit

## Owned artifact

`Ringel/NearEmbeddingReservoir.lean` imports the existing near-embedding concentration and
small-tree construction modules. It supplies the explicit finite probability space needed for the
reservoir allocations in MPS §6. No Case A, Case B, statement, root import, or existing proof body
is changed.

For finite ground type `α` and reservoir-label type `ι`, the sample space is

```lean
ReservoirSample α ι = α → Option ι
```

An outcome independently assigns each ground element either one label (`some i`) or the unused
label (`none`). Given requested masses `q : ι → ℝ`, with all masses nonnegative and total mass at
most one, the per-element mass is `q i` for `some i` and `1 - ∑ i, q i` for `none`. The outcome mass
is the product over ground elements. `categoricalSplitLaw` proves that this is a normalized,
nonnegative `FiniteProbabilityLaw`; its construction has no probabilistic premise.

## Exact laws proved

* `categoricalSplit_atom`: complete product mass of every total assignment.
* `categoricalSplit_cylinder`: product law on every finite coordinate cylinder.
* `categoricalSplit_restriction`: product law for arbitrary coordinatewise allowed labels.
* `categoricalSplit_projected_qRandom`: every labelled projection is exactly an `IsQRandomSet`
  with parameter `q i`, hence has the full product-Bernoulli law required by
  `NearEmbeddingConclusion` and `SmallTreeEmbeddingConclusion`.
* `categoricalSplit_disjoint`: projections with distinct labels are pointwise disjoint in every
  outcome.
* `categoricalSplit_union_qRandom`: the union of all labelled pieces is product-Bernoulli with
  parameter `∑ i, q i`. This realizes the paper's random partition of a larger random reservoir.
* `categoricalSplit_conditional_partition`: the exact division-free joint atom formula for labels
  conditional on a fixed union atom. For a union `B` and label assignment `f`, its joint mass is
  `∏ a∈B q(f a)` times the unused mass for every element outside `B`. When the union event has
  positive mass, division gives the usual independent conditional label probabilities
  `q i / ∑ j, q j`; the division-free statement also remains valid on zero-mass atoms.
* `FiniteProbabilityLaw.product` and its rectangle/marginal lemmas: an explicit product of two
  finite laws.
* `product_map_independent` and `jointReservoir_vertex_colour_independent`: independently sampled
  vertex and colour splits are genuinely independent, including all projected reservoir pairs.

## Independence/disjointness conflict

The phrase “choose disjoint, independent random sets” cannot mean mutual independence of the
labelled sets on one ground type, except in degenerate cases. For distinct labels `i ≠ j` and one
ground element `a`, disjointness forces

```text
P(a ∈ Rᵢ ∧ a ∈ Rⱼ) = 0,
```

whereas independence would force this probability to be `q i * q j`. Thus both assertions are
compatible only when at least one of those two masses is zero. The strongest paper-faithful law is
the categorical product law formalized here: choices are mutually independent **between ground
elements**, pieces are exactly disjoint **within an outcome**, each piece has the requested
product-Bernoulli marginal, and its conditional allocation given the union is explicit. Separate
vertex and colour categorical splits are genuinely independent via the product law.

This is the joint law actually needed by the §6 reservoir splitting steps and moves toward
`NearEmbeddingSourceGoal` by constructing, rather than assuming, the random reservoir layer.

## Verification

The owned module was explicitly built with:

```text
lake build Ringel.NearEmbeddingReservoir
Build completed successfully (8479 jobs).
```

A source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or `implemented_by` in the owned
module. Kernel axiom checks report only standard permitted logical axioms in the principal
construction/law theorems.
