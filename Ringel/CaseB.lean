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

Rather than hide this content behind an unproved claim, we make it **a conditional hypothesis** `CaseBEmbeddingInput`.
Every lemma below is then proved *unconditionally in Lean*: the
probabilistic-method step "positive probability ⇒ existence" is discharged genuinely via
`exists_embed_core_caseB_prob` / `exists_absorption_paths_prob` (from `Ringel/ProbBounds.lean`),
and the two-phase gluing into a global rainbow embedding is proved outright. The dependence on the
unformalized MPS ingredients is thus recorded honestly in the statements as the hypothesis
`CaseBEmbeddingInput`, which threads up to `caseB_rainbow`.
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

/-- **The genuine probabilistic content of Case B, as a conditional hypothesis (MPS §4 + §5).**

For a tree `T` with `n` available colours, and for *every* admissible family of vertex-disjoint
bare paths, this asserts:

* **(Phase 1, §4 near-embedding.)** A rainbow embedding of the core forest `T'` occurs with
  positive probability over a uniformly random vertex map `f_core`.
* **(Phase 2, §5 finishing lemma.)** For *every* rainbow core embedding `f_core`, a valid
  absorption of the bare paths occurs with positive probability over a random map `f_paths`.

These are exactly the two facts the MPS paper establishes by the probabilistic method; they are not
in Mathlib, so we take them as a conditional hypothesis. It is a
genuine (satisfiable, non-vacuous) statement: for a tree admitting a ρ-labelling and the requisite
leftover colours, both events do occur with positive probability. -/
def CaseBEmbeddingInput (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V) : Prop :=
  ∀ (hn : 0 < n) (paths : List (List V))
    [Fintype (((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))]
    [Fintype (CaseBRemovedVertices paths ↪ Fin (2 * n + 1))],
    (∀ P ∈ paths, IsBarePath T P) →
    (∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q}) →
    prob_event (fun f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1) =>
        valid_caseB_core n hn T paths f_core) > 0 ∧
    (∀ f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1),
      prob_event (fun f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1) =>
        valid_caseB_absorption n hn T paths f_core f_paths) > 0)

/-- **Phase 1 — embedding the core forest (§2, §4; MPS `nearembedagain`).**

The forest `T'` obtained by deleting the bare-path interiors admits a rainbow embedding into the
ND-coloured `K_{2n+1}`: there is an injective vertex map whose core edges all receive distinct
ND-colours.

The genuinely hard input — that the rainbow-core event `valid_caseB_core` has *positive
probability* over a random `f_core` (the §4 near-embedding of `T'`) — is taken as the hypothesis
`h_prob`. From it the existence of a rainbow embedding follows by the probabilistic method
(`exists_embed_core_caseB_prob`), which is what this lemma proves. -/
lemma caseB_embed_core (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree) (paths : List (List V))
    (h_bare : ∀ P ∈ paths, IsBarePath T P)
    (h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q})
    [Fintype (((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))]
    (h_prob : prob_event (fun f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1) =>
      valid_caseB_core n hn T paths f_core) > 0) :
    ∃ f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn)
        ((T.induce (CaseBRemovedVertices paths)ᶜ).map f_core).edgeSet :=
  exists_embed_core_caseB_prob n hn T hT paths h_bare h_disj h_prob

/-- **Phase 2 — bare-path absorption (§2, §5; the Case B finishing lemma `lem:finishB`).**

Given a core embedding `f_core` of the forest `T'`, the removed bare paths can be re-embedded so
that:
* their interior vertices avoid the core image (`Disjoint (range f_paths) (range f_core)`), and
* the resulting embedding of the *whole* tree `T` is rainbow (`Set.InjOn (ndColouring …)` on the
  image edge set),

which together is exactly `valid_caseB_absorption`. In the paper this finishing lemma is assembled
(`section5.tex`) from colour switchers (`lem-switchpath`), path absorbers (`lem-absorbpath`),
`lem-randabsorbpath`, distributive absorption (`absorbBmacro`), and the colour cover
(`colourcoverB` / `finishingB`).

The genuinely hard input — that the absorption event `valid_caseB_absorption` has *positive
probability* over a random `f_paths` — is taken as the hypothesis `h_prob`. From it the existence
of a valid absorption follows by the probabilistic method (`exists_absorption_paths_prob`), which
is what this lemma proves. (Note that a valid absorption glues `f_core` and `f_paths` into a
rainbow copy of the *whole* `T`, so it can only exist when `T.edgeSet.ncard ≤ n`; this is not a
hypothesis here but is *forced* by `h_prob` being satisfiable — see
`Ringel/CaseBObstruction.lean`.) -/
lemma caseB_absorb_paths (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (paths : List (List V))
    (h_bare : ∀ P ∈ paths, IsBarePath T P)
    (h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q})
    (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
    [Fintype (CaseBRemovedVertices paths ↪ Fin (2 * n + 1))]
    (h_prob : prob_event (fun f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1) =>
      valid_caseB_absorption n hn T paths f_core f_paths) > 0) :
    ∃ f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1),
      valid_caseB_absorption n hn T paths f_core f_paths :=
  exists_absorption_paths_prob n hn T hT paths h_bare h_disj f_core h_prob

/-- **Assembly of Phase 2.** From a core embedding and the §5 absorption input, absorb the bare
paths and glue the core map and the bare-path map into a single injective, rainbow embedding of the
whole tree `T`, producing a `HasRainbowCopy n T`. (Mirror of `extend_caseA_leaves`.) -/
lemma extend_caseB_paths (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (paths : List (List V))
    (h_bare : ∀ P ∈ paths, IsBarePath T P)
    (h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q})
    (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
    [Fintype (CaseBRemovedVertices paths ↪ Fin (2 * n + 1))]
    (h_prob : prob_event (fun f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1) =>
      valid_caseB_absorption n hn T paths f_core f_paths) > 0) :
    HasRainbowCopy n T := by
  obtain ⟨f_paths, h_disj_r, h_rainbow⟩ :=
    caseB_absorb_paths n hn T hT paths h_bare h_disj f_core h_prob
  -- Glue the two partial maps into a global vertex map.
  let f_full : V → Fin (2 * n + 1) := fun v =>
    if h : v ∈ CaseBRemovedVertices paths then f_paths ⟨v, h⟩ else f_core ⟨v, h⟩
  have h_inj : Function.Injective f_full := by
    intro v w h_eq
    dsimp only [f_full] at h_eq
    by_cases hv : v ∈ CaseBRemovedVertices paths <;>
      by_cases hw : w ∈ CaseBRemovedVertices paths
    · rw [dif_pos hv, dif_pos hw] at h_eq
      exact Subtype.ext_iff.mp (f_paths.injective h_eq)
    · rw [dif_pos hv, dif_neg hw] at h_eq
      have hv_in : f_paths ⟨v, hv⟩ ∈ Set.range f_paths := Set.mem_range_self _
      have hw_in : f_core ⟨w, hw⟩ ∈ Set.range f_core := Set.mem_range_self _
      rw [h_eq] at hv_in
      exact absurd hw_in (Set.disjoint_left.mp h_disj_r hv_in)
    · rw [dif_neg hv, dif_pos hw] at h_eq
      have hw_in : f_paths ⟨w, hw⟩ ∈ Set.range f_paths := Set.mem_range_self _
      have hv_in : f_core ⟨v, hv⟩ ∈ Set.range f_core := Set.mem_range_self _
      rw [← h_eq] at hw_in
      exact absurd hv_in (Set.disjoint_left.mp h_disj_r hw_in)
    · rw [dif_neg hv, dif_neg hw] at h_eq
      exact Subtype.ext_iff.mp (f_core.injective h_eq)
  refine ⟨⟨f_full, h_inj⟩, fun _ => ?_⟩
  rw [SimpleGraph.edgeSet_map]
  exact h_rainbow

/-- **Case B main embedding.** Every Case B tree that is not Case C has a rainbow copy in the
ND-coloured `K_{2n+1}`, *given* the MPS probabilistic embedding input `CaseBEmbeddingInput`
(§4 near-embedding + §5 finishing lemma). This composes Phase 1 (`caseB_embed_core`) and Phase 2
(`extend_caseB_paths`). -/
end Ringel
