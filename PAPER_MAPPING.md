# MPS source-to-Lean map

The archive `ringel_2001.02665.tar.gz` was extracted to `paper-source/`.  SHA-256 comparison shows
that its `main.tex` and `section2.tex`–`section6.tex` are byte-for-byte identical to the copies at
the repository root.  The TeX source, rather than the earlier Lean comments, was used for this map.

## Main theorem and proof organization

| Paper source | Paper declaration/content | Existing Lean |
|---|---|---|
| `main.tex`, `main` | Ringel's conjecture for all sufficiently large trees | `Ringel/Statement.lean`: `ringel_conjecture_large` |
| `section2.tex`, `Theorem_Ringel_proof` | rainbow copy in the ND-colouring | `HasRainbowCopy`, `rainbow_copy_exists`, and the case split in `Ringel/Spine.lean` |
| `section3.tex`, `Lemma_case_division` | Cases A/B/C | `IsCaseA`, `IsCaseB`, `IsCaseC`; `Ringel/CaseDivision.lean` and `Ringel/TreeStructure.lean` |
| `section3.tex`, `split`, `littletree`, `dividetree`, `Lemma_decomp`, `Lemma_tree_splitting` | tree decomposition infrastructure | chiefly `Ringel/TreeStructure.lean` and `Ringel/SmallTree.lean` |

## Cases A and B

| Paper source | Required mathematical object | Current Lean representation/status |
|---|---|---|
| `section2.tex`, `nearembedagain`; proof in `section6.tex` | a **joint random object** consisting of a rainbow forest embedding and four disjoint leftover random sets, with repletion, independence, and marginal-randomness properties | Not yet represented faithfully. `valid_caseA_embedding` and `valid_caseB_core` retain only the final embedding/rainbow consequences. The predicates `CaseAEmbeddingInput` and `CaseBEmbeddingInput` are conditional replacements and are not proofs of this theorem. |
| `section2.tex`, `lem:finishA`; proof in `section4.tex` | exact-colour perfect rainbow matching from the leaf anchors into leftover vertices | `PerfectRainbowMatching` in `Ringel/PaperFinishing.lean` now records the matching, target containment, vertex injectivity, rainbow property, and **equality** of the used-colour set. Its restriction, disjoint-union, and cardinality lemmas are proved. The probabilistic existence theorem is not yet formalized. |
| `section4.tex`, `absorbA`, `absorbAmacro` | local matching colour switchers and robust distributive absorption | No faithful probabilistic statement yet. `hall_implies_matching` in `Ringel/ProbabilisticMatching.lean` supplies only the elementary Hall step. |
| `section4.tex`, `colourcover`, `Lemma_saturating_matching_lemma` | cover prescribed colours and almost-cover remaining colours | Not yet formalized. |
| `section2.tex`, `lem:finishB`; proof in `section5.tex` | vertex-disjoint fixed-endpoint paths whose interior lies in leftover sets and whose collective colour set is exactly `D` | `valid_caseB_absorption` records only the final assembled injection/rainbow condition, not the path family or exact colour-set statement. The paper lemma is not yet formalized. |
| `section5.tex`, `lem-switchpath`, `lem-absorbpath`, `lem-randabsorbpath` | deterministic ND colour switchers followed by random-set availability | Not yet formalized. |
| `section5.tex`, `absorbBmacro`, `colourcoverB`, `finishingB` | distributive path absorption, prescribed-colour cover, and reduction of non-random colours | Not yet formalized. |
| `section6.tex`, `Lemma_extending_with_large_stars`, `Lemma_extending_with_connecting_paths`, `Lemma_extending_with_matchings`, `Lemma_embedding_small_tree` | extension stages used to prove `nearembedagain` | Some deterministic graph/tree primitives exist, but these paper statements and their random-distribution conclusions are not formalized. |

## Corrections to the earlier formalization

1. The paper's near-embedding theorem is **not** merely positive probability for an arbitrary
   uniformly random function or embedding.  It constructs a specially distributed joint random
   embedding and leftover sets.  Thus `CaseAEmbeddingInput` and `CaseBEmbeddingInput` are not
   paper-faithful formulations of `nearembedagain`.
2. The finishing lemmas assume large-`n` parameter hierarchies and precise random-set hypotheses.
   Unconditional versions quantified over every `n`, arbitrary leaf/path choices, or empty path
   families are stronger than the source and can be false.  The obstruction theorems already in
   `Ringel/CaseAObstruction.lean` and `Ringel/CaseBObstruction.lean` document concrete malformed
   earlier statements.
3. Case A requires a matching using **exactly** the unused colours; ordinary Hall matching or mere
   colour injectivity is insufficient. `PerfectRainbowMatching.colours_eq` now captures this.
4. Case B requires actual fixed-endpoint, fixed-length, internally vertex-disjoint paths and exact
   collective use of `D`; a global injective map alone suppresses essential hypotheses needed by
   the finishing proof.

## Precise remaining work

A complete unconditional Lean proof still requires formalizing the asymptotic probability layer:
random subsets and their independence, “with high probability”, parameter hierarchies
`1/n ≪ …`, Chernoff/Azuma estimates, pseudorandom/repletion inheritance, randomized near-perfect
rainbow matchings, robustly matchable bipartite graphs, and the randomized forest embedding of
`section6.tex`.  On top of that, the concrete switcher and distributive-absorption constructions of
`section4.tex` and `section5.tex` must be encoded and proved.  Until those are present,
`ringel_conjecture_large` remains conditional on `CaseAEmbeddingInput` and `CaseBEmbeddingInput`;
those hypotheses have not been presented as a completed proof.
