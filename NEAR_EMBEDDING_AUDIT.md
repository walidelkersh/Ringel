# `nearembedagain` formalization audit

## Scope completed

`Ringel/NearEmbedding.lean` adds a self-contained, proof-backed first layer for the joint random
near-embedding theorem in `section2.tex`, lines 211–228, and the extension language introduced in
`section6.tex`, lines 2–24.

The central finite conclusion is `NearEmbeddingConclusion`.  Unlike the old Case A/B assumptions,
it contains one finite probability space and one **joint** outcome carrying the embedded graph,
its vertex support, the image `W` of `U`, and all four leftovers `V,V₀,C,C₀`.  Its clauses state:

* deterministic disjointness from the embedded vertices/colours and pairwise disjointness of
  `V,V₀` and `C,C₀`;
* the A1 high-probability event: an injective copy of `T'`, rainbow in the ND colouring, with `W`
  the image of `U` and `(W,V₀)` `⌊ξn⌋`-replete **in every colour**;
* exact product-Bernoulli (`q`-random) laws for `V₀,C₀`, together with independence of these two
  random variables;
* the exact marginal product-Bernoulli laws `(p+ε)/6` for `V` and `(1-η)ε` for `C`, without adding
  the false requirement that these marginals be independent.

`NearEmbeddingInstance` records the forest size, size of `U`, and the paper's definition of `p` by
removing leaves at vertices with at least `k` leaf-neighbours.  `NearEmbeddingSourceGoal` records
the asymptotic hierarchy and the second relation `ξ ≪ 1/k ≪ 1/log n`; “with high probability” is
represented by an arbitrary failure tolerance followed by sufficiently large `n`.

The deterministic/probability infrastructure proved in this slice includes finite probability
monotonicity/nonnegativity, positive probability implies an outcome, symmetry of independence,
the same-space extension definition and transitivity, and extraction of an actual rainbow core
from the joint theorem.  `Ringel/NearEmbeddingBridge.lean` specializes that extraction to induced
cores and to the bare-path-interior-deleted core shape.  This replaces the concrete Phase-1/core
portion of both old inputs; it does not pretend to prove the finishing portions.

No statement of `ringel_conjecture_large` was changed.  No axiom, `sorry`, `admit`, or `sorryAx` was
added.

## Small-tree construction slice

`Ringel/NearEmbeddingSmallTree.lean` now owns **“Small trees with a replete subset”**
(`section6.tex`, lines 106–128, label `Lemma_embedding_small_tree`) at finite parameters.  Its
`SmallTreeEmbeddingOutcome` keeps, in one outcome, the injective copy of `T`, the q-random
available vertex/colour reservoirs, the two leftovers, reservoir containment, rainbow correctness,
and avoidance of the image and used colours.  It forgets coherently to the existing
`RandomizedRainbowEmbedding` interface.  `SmallTreeEmbeddingConclusion` gives the exact joint
finite law: both available reservoirs are q-random, both leftovers are q/2-random, the leftovers
are independent, and repletion has probability at least `1-failure`.

The deterministic portion is complete and proof-backed:

* `greedy_extend_one` proves the local greedy rainbow insertion step (fresh vertex plus fresh
  colour preserves injectivity and colour freshness);
* `exists_smallTreeEmbeddingOutcome_of_greedy` packages the completed greedy construction into
  the joint outcome;
* `colourPairReplete_compl_of_bad_bound` proves the paper's transfer from a globally replete pair
  and a bound on bad edges into the occupied reservoirs to repletion against their complement;
* `colourPairReplete_of_retained` proves the final random-thinning transfer once every colour has
  retained enough crossing edges;
* `SmallTreeEmbeddingConclusion.exists_replete` is the finite probabilistic-method extraction.

No source assumption has been added.

## Bounded concentration slice

`Ringel/NearEmbeddingConcentration.lean` proves the previously displayed finite theorem
`qRandomSet_lower_tail` exactly as stated, with the multiplicative bound
`exp (-(δ² q |A|)/2)`.  The proof is a finite exponential-moment argument over the powerset of
`A`; no measure-theoretic or asymptotic assumption is inserted.

The definition audit found **no independence obstruction** in `IsQRandomSet`.  Its defining
formula gives the probability of every atom `X = B` as
`q^|B| (1-q)^(|univ \\ B|)`.  Thus it is the complete product-Bernoulli distribution and encodes
mutual independence of all membership bits, not merely their one-point marginals.  This matches
MPS §3's definition of a p-random subset as selecting every element independently.  The new module
makes the consequences explicit:

* `qRandomSet_intersection_atom` gives the exact product law of `A ∩ X` for every `B ⊆ A`;
* `qRandomSet_mem_prob` gives each one-point marginal `P(a ∈ X) = q`;
* `qRandomSet_intersection_expect` gives the exact expectation
  `E |A ∩ X| = q |A|`;
* `qRandomSet_intersection_card_lt_prob` identifies every cardinality lower event with its finite
  binomial powerset sum;
* `powerset_chernoff_lower_tail` proves the finite product-weight estimate used by
  `qRandomSet_lower_tail`.

Consequently the proposed theorem did follow from the actual definition and was not reformulated.
Had `IsQRandomSet` specified only `qRandomSet_mem_prob`, the expectation identity would still
follow by linearity, but the Chernoff conclusion would be false in general (perfectly correlated
membership bits have the same marginals).  That hypothetical obstruction does not apply here.

The next construction needed by §6 is not an added independence hypothesis: it is an explicit
finite product law for the **joint disjoint reservoir split** used in the randomized embedding,
with proofs that its projected reservoirs have the required q-random laws and the required joint
independence/conditional laws.  Together with an upper-tail/Azuma analogue, that construction must
prove the simultaneous
concentration event: (i) every
partially embedded vertex has enough available neighbours in the appropriate vertex/colour
reservoir; (ii) every colour has at most `U.ncard / 10` edges from the designated U-reservoir into
the occupied embedding reservoirs; and (iii) independent q/2 thinning retains at least `r`
crossing edges of every colour, with total failure probability at most `failure`.  The deterministic
lemmas above turn those three estimates directly into the displayed conclusion.

After the four §6 extension lemmas are available, the exact unproved assembly goal already present
in Lean is:

```lean
Ringel.NearEmbeddingSourceGoal
```

whose body requires, in the nested hierarchy
`1/n ≪ ξ ≪ μ ≪ η ≪ ε ≪ 1` and `ξ ≪ 1/k ≪ 1/log n`, that every
`NearEmbeddingInstance n k epsCount pCount T' U` yields

```lean
NearEmbeddingConclusion n hn T' U ξ μ η τ epsCount pCount
```

for every positive failure tolerance `τ`, eventually in `n`.

After that theorem, the next missing goals needed to eliminate the complete old inputs are exactly
the finishing lemmas: `lem:finishA` (`section4.tex`) and `lem:finishB` (`section5.tex`).

## Build audit

The owned concentration module was explicitly built with the repository toolchain:

```text
lake build Ringel.NearEmbeddingConcentration
Build completed successfully (8478 jobs).
```

A source scan of `Ringel/NearEmbeddingConcentration.lean` found no `sorry`, `admit`, `axiom`,
`sorryAx`, `implemented_by`, or unproved source-level assumption.

A default full-project build was also started but did not complete within the audit window.  No
claim of a successful default build is made; the owned module and all of its imports were built by
the explicit command above.
