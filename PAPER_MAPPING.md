# MPS source-to-Lean map

This file records which parts of the Montgomery–Pokrovskiy–Sudakov proof have Lean
representations and where the current formal boundary lies. The paper source is the copy in
RingelPaper; the principal source files are mapped below.

## Main theorem and assembly

| Paper source | Lean representation | Status |
|---|---|---|
| main.tex | Ringel/Statement.lean: ringel_conjecture_large | Public large-\(n\) theorem, conditional on CaseABSourceStatement |
| section2.tex, Theorem_Ringel_proof | HasRainbowCopy and Ringel/Spine.lean | Rainbow-copy assembly |
| section2.tex, Lemma_decomp | Ringel/Spine.lean: decomp_of_rainbow_copy | Proved cyclic-shift decomposition |
| section3.tex, case division | Ringel/TreeStructure.lean and Ringel/CaseDivision.lean | Formalized case split |

The all-\(n\) conjecture is stated separately and remains open.

## Case A

| Paper object | Lean representation | Status |
|---|---|---|
| walk-sum core embedding | walkSum, tree_embed, and the Case A modules | Deterministic infrastructure |
| near-embedding output | valid_caseA_embedding and CaseAJointOutput | Finite output interface |
| leaf finishing | PerfectRainbowMatching and CaseAJointOutput.valid_embedding | Matching and assembly lemmas |
| eventual source theorem | CaseASourceStatement | Explicit source-level statement |
| MPS random construction and exact-colour finishing | CaseASource, ProbBounds, NearEmbedding, NearEmbeddingReservoir | Not yet derived unconditionally from the paper |

Case A requires a matching whose used colours equal the prescribed unused-colour set. Ordinary
injectivity or a generic Hall matching does not express that requirement.

## Case B

| Paper object | Lean representation | Status |
|---|---|---|
| bare-path core | CaseBCore and the Case B structural modules | Structural infrastructure |
| path finishing | valid_caseB_absorption and related assembly lemmas | Final-condition interface |
| eventual source theorem | CaseBSourceStatement | Explicit source-level statement |
| fixed-endpoint path family, random availability, and exact collective colour use | CaseB and the probability modules | Not yet derived unconditionally from the paper |

The source theorem must retain fixed endpoints, fixed path lengths, internal vertex-disjointness,
and exact collective colour use. A global injection alone is too weak.

## Case C

| Paper object | Lean representation | Status |
|---|---|---|
| small-core embedding | CaseC.lean: caseC_embedding_exists | Formalized for the stated large-\(n\) range |
| many-high-degree leaf packing | CaseCManyVertex.lean and CaseCLeafPacking.lean | Formalized |
| Case C rainbow copy | CaseC.lean: caseC_rainbow | Formalized |

## Probability and reservoirs

NearEmbedding.lean, NearEmbeddingConcentration.lean, NearEmbeddingReservoir.lean,
ProbabilisticMatching.lean, and ProbBounds.lean provide finite probability spaces, reservoir
bookkeeping, concentration statements, and positive-probability extraction. These modules expose
the infrastructure needed by the paper's random construction. They do not imply the full Case A
or Case B source statements by themselves.

## Formalization boundary

The remaining mathematical work is the unconditional MPS source layer:

- the joint random near-embedding and its distributional properties;
- asymptotic parameter hierarchies and concentration estimates;
- repletion and robust matching arguments;
- Case A exact-colour absorption;
- Case B fixed-endpoint path absorption.

The public theorem makes this boundary explicit through CaseABSourceStatement. No placeholder
or replacement axiom is used to conceal it.
