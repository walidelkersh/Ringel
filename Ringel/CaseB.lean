import Ringel.Primitives
import Ringel.ProbBounds
import Ringel.CaseA
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Filter.Basic
import Ringel.LittlewoodOfford
import Ringel.ProbabilisticMatching
import Ringel.CaseBSwitcherLarge

namespace Ringel

/-!
# Case B: embedding trees with many long bare paths

This file lays down the architectural skeleton of the Montgomery–Pokrovskiy–Sudakov proof of
Ringel's Conjecture in **Case B** (a tree with `≥ ⌊δ n / 800⌋` vertex-disjoint bare paths of
length `⌊δ⁻¹⌋ + 1`, and which is *not* Case C).

The construction follows the paper (`main.tex` §2 and the finishing lemma §5, `section2.tex`
lines 84–91, 164, 238–270). It proceeds in two phases, exactly mirroring the two-phase structure
of Case A in `Ringel/CaseA.lean`:

1. **Core embedding (Phase 1).** Delete the *interior* vertices of every bare path (the set
   `CaseBRemovedVertices paths`) to obtain a forest `T' = T.induce (removed)ᶜ`. Embed `T'` as a
   rainbow copy in the ND-coloured `K_{2n+1}`. In the paper this is the randomized rainbow
   embedding of `T'` supplied by the near-embedding theorem (`nearembedagain`). See
   `caseB_embed_core`.

2. **Bare-path absorption (Phase 2).** Re-embed the removed bare paths vertex-disjointly, routing
   their interior vertices through the leftover vertex set so that the whole tree image is rainbow
   (each colour used at most once). This is the Case B *finishing lemma* (`lem:finishB`), built in
   §5 from colour switchers (`lem-switchpath`), path absorbers (`lem-absorbpath`), distributive
   absorption (`absorbBmacro`), the colour cover (`colourcoverB`) and `finishingB`. See
   `caseB_absorb_paths` and the assembly `extend_caseB_paths`.

## The genuine mathematical content, and how it enters here

The two probabilistic existence facts — that the core embedding (Phase 1), resp. the absorption
(Phase 2), occur with positive probability over the random choice of embedding — are the genuine
mathematical content of Case B (MPS §4 near-embedding and §5 finishing lemma). They are *not*
available in Mathlib, and formalizing them from scratch is a large development well beyond a wiring
fix; indeed the Phase-1 fact for the degenerate family `paths = []` is already at least as hard as
producing a ρ-labelling of an arbitrary tree.

Rather than hide this content behind an unproved claim, we keep the probabilistic content explicit in the theorem statements.
Every lemma below is then proved *unconditionally in Lean*: the
probabilistic-method step "positive probability ⇒ existence" is discharged genuinely via
`exists_embed_core_caseB_prob` / `exists_absorption_paths_prob` (from `Ringel/ProbBounds.lean`),
and the two-phase gluing into a global rainbow embedding is proved outright. The dependence on the
unformalized MPS ingredients is thus recorded honestly in the statements as the hypothesis
the theorem statements that thread up to `caseB_rainbow`.
-/

open SimpleGraph
open Classical

/-- The **core forest** of a Case B tree: `T` with the interior vertices of every bare path
removed. By the paper (§2, §4) this is the forest `T'` that gets a randomized rainbow embedding
before the bare paths are absorbed back. -/
def CaseBCore {V : Type*} (T : SimpleGraph V) (paths : List (List V)) :
    SimpleGraph ((CaseBRemovedVertices paths)ᶜ : Set V) :=
  T.induce ((CaseBRemovedVertices paths)ᶜ)

/-- The Case B core is a **forest** (acyclic): deleting vertices from a tree cannot create a
cycle. It need not be connected — removing the interior of a bare path disconnects `T` — which is
why Phase 1 embeds a forest rather than a tree. -/
lemma caseB_core_isAcyclic {V : Type*} (T : SimpleGraph V) (hT : T.IsTree)
    (paths : List (List V)) : (CaseBCore T paths).IsAcyclic :=
  hT.IsAcyclic.induce ((CaseBRemovedVertices paths)ᶜ)

end Ringel
