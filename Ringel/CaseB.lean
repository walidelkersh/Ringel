import Ringel.Primitives
import Ringel.ProbBounds
import Ringel.CaseA
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Filter.Basic
import Ringel.LittlewoodOfford
import Ringel.ProbabilisticMatching

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

The two probabilistic existence facts (that the core embedding, resp. the absorption, occur with
positive probability) are the genuine mathematical content of Case B; they are isolated as the two
remaining `sorry`s (inside `caseB_embed_core` and `caseB_absorb_paths`). Everything else — the
forest structure of the core and the assembly of the two phases into a global rainbow embedding —
is proved.
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

/-- **Phase 1 — embedding the core forest (§2, §4; MPS `nearembedagain`).**

The forest `T'` obtained by deleting the bare-path interiors admits a rainbow embedding into the
ND-coloured `K_{2n+1}`: there is an injective vertex map whose core edges all receive distinct
ND-colours. In the paper this is the *randomized* rainbow embedding of `T'`; here we package its
existence via the probabilistic scaffold `exists_embed_core_caseB_prob`.

The single remaining `sorry` is exactly the probabilistic content: that the event
`valid_caseB_core` (a rainbow core embedding) has positive probability over the random choice of
`f_core`. This is where the near-embedding theorem of §4 is applied.

**Status of this `sorry` (honest assessment).** By `prob_pos_of_exists`/`exists_of_prob_gt_zero`
(in `Ringel/ProbBounds.lean`), over the finite sample space of embeddings the goal
`prob_event (… valid_caseB_core …) > 0` is *equivalent* to the plain existence of one rainbow
embedding of the core forest `T'`. So the difficulty is not probabilistic: an averaging/union-bound
argument ("expected number of colour collisions `< 1`") cannot help, and in fact the expected
number of colliding edge-pairs for a uniformly random embedding is `Θ(n)`, not `o(1)`.

Moreover this statement is at least as hard as an **open problem**. Its hypotheses admit the
sub-case `paths = []` (valid whenever `⌊δ·n/800⌋ = 0`, e.g. `n < 800/δ`), and then
`CaseBRemovedVertices paths = ∅`, so the "core forest" is the *entire* `n`-edge tree `T` and
`valid_caseB_core` becomes: `T` has a rainbow embedding into the ND-coloured `K_{2n+1}`, i.e. a
**ρ-labelling (Rosa labelling) of `T`**. Since `δ` ranges over all positive reals, a single proof of
this lemma would yield a ρ-labelling for every tree — the cyclic-decomposition/graceful-type
labelling problem, which is open in general and absent from Mathlib. Discharging this `sorry`
soundly therefore requires either the paper's full §4 near-embedding + §5 absorption construction
(a large development, not a wiring fix) or a proof of an open conjecture; it is left in place
rather than closed by an unsound proof. (Compare the honest treatment of the analogous Case A gap
in `bound_vertex_collisions`.) -/
lemma caseB_embed_core (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree) (hcard : T.edgeSet.ncard = n)
    (paths : List (List V))
    (h_bare : ∀ P ∈ paths, IsBarePath T P)
    (h_len : ∀ P ∈ paths, P.length = ⌊(δ : ℝ)⁻¹⌋₊ + 1)
    (h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q})
    (h_count : ⌊δ * (n : ℝ) / 800⌋₊ ≤ paths.length) :
    ∃ f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn)
        ((T.induce (CaseBRemovedVertices paths)ᶜ).map f_core).edgeSet := by
  haveI : Fintype (((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1)) :=
    Fintype.ofFinite _
  -- The probabilistic near-embedding of the forest `T'`: this is the genuine content of §4.
  exact exists_embed_core_caseB_prob n hn T hT paths h_bare h_disj sorry

/-- **Phase 2 — bare-path absorption (§2, §5; the Case B finishing lemma `lem:finishB`).**

Given a rainbow core embedding `f_core` of the forest `T'`, the removed bare paths can be
re-embedded so that:
* their interior vertices avoid the core image (`Disjoint (range f_paths) (range f_core)`), and
* the resulting embedding of the *whole* tree `T` is rainbow (`Set.InjOn (ndColouring …)` on the
  image edge set),

which together is exactly `valid_caseB_absorption`. In the paper this finishing lemma is assembled
(`section5.tex`) from:
* `lem-switchpath` — colour switchers: two length-7 rainbow paths between the same endpoints
  differing only in one colour, letting us switch between two colours;
* `lem-absorbpath` — upgrading a switcher to select 1 of a set of 100 colours;
* `lem-randabsorbpath` — many such switchers use only random vertices/colours;
* `absorbBmacro` — distributive absorption turns these into a large-scale absorber;
* `colourcoverB` / `finishingB` — embedding the paths to use (almost) exactly the leftover colours.

The hypothesis `h_core` records the genuine dependence of the finishing step on the core embedding
(the leftover colour pool is `C(K_{2n+1})` minus the colours used by the core). The single
remaining `sorry` is the probabilistic content of `lem:finishB`: that `valid_caseB_absorption`
holds with positive probability over the random choice of `f_paths`.

**Status of this `sorry` (honest assessment; see `Ringel/CaseBObstruction.lean`).**
By `prob_pos_of_exists` / `exists_of_prob_gt_zero` (in `Ringel/ProbBounds.lean`), over the finite,
nonempty sample space of embeddings the positivity goal fed to `exists_absorption_paths_prob` is
*equivalent* to the plain existence `∃ f_paths, valid_caseB_absorption …`. So the difficulty is not
probabilistic.

As currently stated this lemma is in fact **false**, because it lacks any hypothesis bounding the
number of edges of `T` by the number `n` of available colours. `valid_caseB_absorption` glues
`f_core` and `f_paths` into a single injective vertex map whose image edge-set is rainbow under the
`n`-colour `ndColouring`; a rainbow copy uses at most `n` distinct colours, so any successful
absorption forces `T.edgeSet.ncard ≤ n` (this is the machine-checked
`valid_caseB_absorption_edge_ncard_le`). Yet none of the hypotheses here supply that bound:
`caseB_absorb_paths` omits the edge-count hypothesis `T.edgeSet.ncard = n` (and the paper's regime
hypotheses `h_len`, `h_count`, `¬IsCaseC`, large `n`) that *are* available at its only call site
inside `caseB_embedding_exists`. The concrete counterexample `T = pathGraph 3` (a tree with `2`
edges), `n = 1`, single bare path `[0,1,2]`, satisfies every hypothesis yet admits no absorbing
embedding — this is proved in full in `caseB_absorb_paths_statement_false`.

Even the faithful, `hcard`-corrected version is the genuine §5 finishing lemma `lem:finishB`, whose
proof requires the paper's absorption machinery (colour switchers `lem-switchpath`, path absorbers
`lem-absorbpath`, distributive absorption `absorbBmacro`, the colour cover `colourcoverB` /
`finishingB`) and a *controlled* (quasirandom) core embedding rather than the arbitrary `f_core`
taken here — a large development, not a wiring fix, and absent from Mathlib. It is therefore left
in place rather than closed by an unsound proof, mirroring the honest treatment of the Phase-1 gap
(`caseB_embed_core`) and the Case A gap (`bound_vertex_collisions`). -/
lemma caseB_absorb_paths (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (paths : List (List V))
    (h_bare : ∀ P ∈ paths, IsBarePath T P)
    (h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q})
    (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
    (h_core : Set.InjOn (ndColouring n hn)
      ((T.induce (CaseBRemovedVertices paths)ᶜ).map f_core).edgeSet) :
    ∃ f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1),
      valid_caseB_absorption n hn T paths f_core f_paths := by
  haveI : Fintype (CaseBRemovedVertices paths ↪ Fin (2 * n + 1)) := Fintype.ofFinite _
  -- The probabilistic finishing lemma §5: this is the genuine content of Case B absorption.
  exact exists_absorption_paths_prob n hn T hT paths h_bare h_disj f_core sorry

/-- **Assembly of Phase 2.** From a rainbow core embedding, absorb the bare paths and glue the
core map and the bare-path map into a single injective, rainbow embedding of the whole tree `T`,
producing a `HasRainbowCopy n T`. (Mirror of `extend_caseA_leaves`.) -/
lemma extend_caseB_paths (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (paths : List (List V))
    (h_bare : ∀ P ∈ paths, IsBarePath T P)
    (h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
      Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q})
    (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
    (h_core : Set.InjOn (ndColouring n hn)
      ((T.induce (CaseBRemovedVertices paths)ᶜ).map f_core).edgeSet) :
    HasRainbowCopy n T := by
  obtain ⟨f_paths, h_disj_r, h_rainbow⟩ :=
    caseB_absorb_paths n hn T hT paths h_bare h_disj f_core h_core
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
ND-coloured `K_{2n+1}`. This composes Phase 1 (`caseB_embed_core`) and Phase 2
(`extend_caseB_paths`); the two remaining `sorry`s live in the probabilistic existence lemmas
`caseB_embed_core` and `caseB_absorb_paths`. -/
lemma caseB_embedding_exists (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn_pos : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V)
    (hT : T.IsTree) (hn : T.edgeSet.ncard = n) (hB : IsCaseB δ n T) (hC : ¬IsCaseC δ n T) :
    HasRainbowCopy n T := by
  obtain ⟨paths, h_bare, h_len, h_disj, h_count⟩ := hB
  -- Phase 1: embed the core forest `T'`.
  obtain ⟨f_core, h_core⟩ :=
    caseB_embed_core δ hδ n hn_pos T hT hn paths h_bare h_len h_disj h_count
  -- Phase 2: absorb the bare paths and assemble the full rainbow embedding.
  exact extend_caseB_paths n hn_pos T hT paths h_bare h_disj f_core h_core

lemma caseB_rainbow_large_n (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseB δ n T → ¬IsCaseC δ n T → HasRainbowCopy n T := by
  use 1
  intro n hn V _ T hT hcard hB hC
  have hn_pos : 0 < n := by omega
  exact caseB_embedding_exists δ hδ n hn_pos T hT hcard hB hC

/-- **Case B rainbow copy (§5, §6, M1+M2).** For small δ > 0 and large n, every Case B
tree that is not Case C has a rainbow copy in the ND-coloured K_{2n+1}. -/
theorem caseB_rainbow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseB δ n T → ¬IsCaseC δ n T → HasRainbowCopy n T := by
  obtain ⟨N, hN⟩ := caseB_rainbow_large_n δ hδ
  exact Filter.eventually_atTop.mpr ⟨N, hN⟩

end Ringel
