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

## Exact next source lemma and unproved Lean goal

The next construction lemma is **“Small trees with a replete subset”**
(`section6.tex`, lines 106–128, label `Lemma_embedding_small_tree`).  It initializes the §6 chain
and produces the independent `V₀,C₀` and repletion clause.  Its formalization should prove a
constructor for `RandomizedRainbowEmbedding` and then establish the corresponding
`NearEmbeddingConclusion` fields for the first stage.

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

The new modules were explicitly built together:

```text
lake build Ringel.NearEmbedding Ringel.NearEmbeddingBridge
Build completed successfully (8477 jobs).
```

A full default `lake build` was also run.  It reaches the new module but fails in the separately
owned existing `Ringel/CaseA.lean` CI repair, at lines 221, 236, and 241.  This slice did not edit
that file, per task ownership.  Thus this audit does **not** claim a successful full-project build.
