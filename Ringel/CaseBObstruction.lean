import Ringel.CaseB

/-!
# Case B, Phase 2 — the absorption obstruction (analytical infrastructure)

This file documents, with fully machine-checked lemmas, *why* the Phase-2 lemma
`caseB_absorb_paths` (in `Ringel/CaseB.lean`) cannot be discharged soundly **as currently
stated**, and isolates the genuine mathematical content that a faithful version would require.

The `sorry` in `caseB_absorb_paths` sits behind `exists_absorption_paths_prob`, whose only real
hypothesis is `prob_event (fun f_paths => valid_caseB_absorption n hn T paths f_core f_paths) > 0`.
By `prob_pos_of_exists` / `exists_of_prob_gt_zero` (in `Ringel/ProbBounds.lean`), over the finite,
nonempty sample space of embeddings this positivity is **equivalent** to the plain existence
`∃ f_paths, valid_caseB_absorption …`. So the difficulty is not probabilistic — it is the bare
existence of an absorbing embedding.

The key structural fact proved here is `valid_caseB_absorption_edge_ncard_le`: **any** successful
absorption forces `T.edgeSet.ncard ≤ n`. Indeed a valid absorption glues `f_core` and `f_paths`
into a single injective vertex map whose image edge-set is rainbow under the `n`-colour
`ndColouring`, and a rainbow copy can use at most `n` distinct colours
(`rainbow_map_edge_ncard_le`), hence at most `n` edges.

Consequently the *conclusion* of `caseB_absorb_paths` entails `T.edgeSet.ncard ≤ n`, yet **none of
its hypotheses supply this bound**: `caseB_absorb_paths` omits the edge-count hypothesis
`T.edgeSet.ncard = n` (and the paper's regime hypotheses `h_len`, `h_count`, `¬IsCaseC`, large `n`)
that are available at its only call site inside `caseB_embedding_exists`. Because a tree may have
arbitrarily many edges while `n` stays fixed, the statement is **false** as written. This is made
fully explicit and machine-checked in `caseB_absorb_paths_statement_false` below, using the
concrete instance `T = pathGraph 3` (`2` edges) with `n = 1` (one available colour): every
hypothesis of `caseB_absorb_paths` holds, yet no absorbing embedding exists.

This mirrors the honest treatment of the analogous Phase-1 gap (`caseB_embed_core`) and the Case A
gap (`bound_vertex_collisions`): rather than fabricate an unsound proof, we pin the obstruction down
with verified lemmas and document exactly what a faithful, provable version would need.
-/

open SimpleGraph

namespace Ringel

/-- **Rainbow copies use at most `n` colours, hence at most `n` edges.**

If an injective vertex map `f : V ↪ Fin (2n+1)` embeds `T` so that the image edges all receive
distinct `ndColouring` values (`Set.InjOn`), then `T` has at most `n` edges. The `ndColouring`
takes only `n` values (`Fin n`), so an injective colouring of the image edge-set bounds its size by
`n`; and an injective vertex map preserves the number of edges.
-/
lemma rainbow_map_edge_ncard_le {V : Type*} (n : ℕ) (hn : 0 < n) (T : SimpleGraph V)
    (f : V ↪ Fin (2 * n + 1))
    (h : Set.InjOn (ndColouring n hn) (T.map f).edgeSet) :
    T.edgeSet.ncard ≤ n := by
  -- An injective vertex map preserves the number of edges.
  have hmap : (T.map f).edgeSet.ncard = T.edgeSet.ncard := by
    rw [SimpleGraph.edgeSet_map,
      Set.ncard_image_of_injective _ f.sym2Map.injective]
  -- The colouring is injective on the image edge-set, so it has at most `n = |Fin n|` elements.
  have hle : (T.map f).edgeSet.ncard ≤ n := by
    have h' := Set.ncard_le_ncard_of_injOn (ndColouring n hn)
      (fun e _ => Set.mem_univ (ndColouring n hn e)) h Set.finite_univ
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h'
  rw [← hmap]
  exact hle

/-- A `HasRainbowCopy n T` witness forces `T.edgeSet.ncard ≤ n`. -/
lemma hasRainbowCopy_edge_ncard_le {V : Type*} (n : ℕ) (hn : 0 < n) (T : SimpleGraph V)
    (h : HasRainbowCopy n T) : T.edgeSet.ncard ≤ n := by
  obtain ⟨f, hf⟩ := h
  exact rainbow_map_edge_ncard_le n hn T f (hf hn)

/-- Gluing a core embedding `f_core` and an (interior) path embedding `f_paths` witnessing
`valid_caseB_absorption` produces a genuine rainbow copy of the whole tree `T`. (This is the
gluing step of `extend_caseB_paths`, isolated so it can be fed an *explicit* `f_paths` rather than
one produced by the still-`sorry`ed `caseB_absorb_paths`.) -/
lemma hasRainbowCopy_of_absorption {V : Type*} [Finite V] (n : ℕ) (hn : 0 < n)
    (T : SimpleGraph V) (paths : List (List V))
    (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
    (f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1))
    (h : valid_caseB_absorption n hn T paths f_core f_paths) :
    HasRainbowCopy n T := by
  classical
  obtain ⟨h_disj_r, h_rainbow⟩ := h
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
  convert h_rainbow using 2

/-- **The absorption obstruction (machine-checked).** Any valid Case B absorption forces the tree
to have at most `n` edges. Since `caseB_absorb_paths` has no hypothesis bounding `T.edgeSet.ncard`,
its conclusion cannot hold in general. -/
lemma valid_caseB_absorption_edge_ncard_le {V : Type*} [Finite V] (n : ℕ) (hn : 0 < n)
    (T : SimpleGraph V) (paths : List (List V))
    (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
    (f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1))
    (h : valid_caseB_absorption n hn T paths f_core f_paths) :
    T.edgeSet.ncard ≤ n :=
  hasRainbowCopy_edge_ncard_le n hn T
    (hasRainbowCopy_of_absorption n hn T paths f_core f_paths h)

/-- **`caseB_absorb_paths` is false as currently stated.**

The universally-quantified statement of `caseB_absorb_paths` (all hypotheses ⇒ an absorbing
embedding exists) does not hold: it lacks any hypothesis bounding the number of edges of `T` by the
number `n` of available colours. The witness is the path `pathGraph 3` (a tree with `2` edges) with
`n = 1` (one colour). It has a single bare path `[0,1,2]` (interior `{1}`), whose core `{0,2}`
carries no edges, so a core embedding `f_core` and the rainbow-core hypothesis `h_core` are
trivial; yet `2 > 1`, so by `valid_caseB_absorption_edge_ncard_le` no absorbing embedding exists. -/
theorem caseB_absorb_paths_statement_false :
    ¬ ∀ (n : ℕ) (hn : 0 < n) (V : Type) [Finite V] (T : SimpleGraph V)
        (_hT : T.IsTree) (paths : List (List V))
        (_h_bare : ∀ P ∈ paths, IsBarePath T P)
        (_h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q →
          Disjoint ({v : V | v ∈ P} : Set V) {v : V | v ∈ Q})
        (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
        (_h_core : Set.InjOn (ndColouring n hn)
          ((T.induce (CaseBRemovedVertices paths)ᶜ).map f_core).edgeSet),
        ∃ f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1),
          valid_caseB_absorption n hn T paths f_core f_paths := by
  intro H
  -- The concrete witness: `T = pathGraph 3`, a tree with two edges, and `n = 1`.
  -- Edge set of `pathGraph 3`.
  have hES : (pathGraph 3).edgeSet = {s(0, 1), s(1, 2)} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeSet, pathGraph_adj, Set.mem_insert_iff, Set.mem_singleton_iff,
        Sym2.eq_iff]
      constructor
      · rintro (h | h) <;> (revert a b; decide)
      · rintro (h | h) <;> (revert a b; decide)
  have hES2 : (pathGraph 3).edgeSet.ncard = 2 := by
    rw [hES, Set.ncard_pair (by decide)]
  -- `pathGraph 3` is a tree.
  have hT : (pathGraph 3).IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨pathGraph_connected 2, ?_⟩
    rw [Nat.card_coe_set_eq, hES2, Nat.card_eq_fintype_card, Fintype.card_fin]
  -- The removed-vertex set for the single bare path `[0,1,2]` is `{1}`.
  have hrem : CaseBRemovedVertices ([[0, 1, 2]] : List (List (Fin 3))) = {1} := by
    ext v
    simp only [CaseBRemovedVertices, List.mem_singleton, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨P, rfl, hv⟩
      have : ([0, 1, 2] : List (Fin 3)).tail.dropLast = [1] := rfl
      rw [this, List.mem_singleton] at hv
      exact hv
    · rintro rfl
      exact ⟨[0, 1, 2], rfl, by decide⟩
  -- `[0,1,2]` is a bare path of `pathGraph 3`.
  have hbare : ∀ P ∈ ([[0, 1, 2]] : List (List (Fin 3))), IsBarePath (pathGraph 3) P := by
    intro P hP
    rw [List.mem_singleton] at hP
    subst hP
    refine ⟨?_, by decide, ?_⟩
    · rw [List.isChain_cons, List.isChain_cons]
      refine ⟨?_, ?_, List.isChain_singleton _⟩ <;>
        (intro y hy;
         simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy;
         subst hy; rw [pathGraph_adj]; decide)
    · intro v hv
      have hv1 : v = 1 := by
        have : ([0, 1, 2] : List (Fin 3)).tail.dropLast = [1] := rfl
        rw [this, List.mem_singleton] at hv; exact hv
      subst hv1
      have hnb : (pathGraph 3).neighborSet 1 = {0, 2} := by
        ext w
        simp only [mem_neighborSet, pathGraph_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
        revert w; decide
      rw [hnb, Set.ncard_pair (by decide)]
  -- Vacuous disjointness: there is only one path.
  have hdisj : ∀ P ∈ ([[0, 1, 2]] : List (List (Fin 3))),
      ∀ Q ∈ ([[0, 1, 2]] : List (List (Fin 3))),
      P ≠ Q → Disjoint ({v : Fin 3 | v ∈ P} : Set (Fin 3)) {v : Fin 3 | v ∈ Q} := by
    intro P hP Q hQ hPQ
    rw [List.mem_singleton] at hP hQ
    exact absurd (hP.trans hQ.symm) hPQ
  -- The trivial core embedding (inclusion of the complement subtype).
  set f_core :
      ((CaseBRemovedVertices ([[0, 1, 2]] : List (List (Fin 3))))ᶜ : Set (Fin 3)) ↪ Fin 3 :=
    Function.Embedding.subtype _ with hfc
  -- The core carries no edges, so the rainbow-core hypothesis is trivial.
  have hcore : Set.InjOn (ndColouring 1 Nat.one_pos)
      (((pathGraph 3).induce (CaseBRemovedVertices ([[0, 1, 2]] : List (List (Fin 3))))ᶜ).map
        f_core).edgeSet := by
    have hind : ((pathGraph 3).induce
        (CaseBRemovedVertices ([[0, 1, 2]] : List (List (Fin 3))))ᶜ).edgeSet = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro e he
      induction e using Sym2.ind with
      | _ a b =>
        rw [mem_edgeSet] at he
        have hadj : (pathGraph 3).Adj (a : Fin 3) (b : Fin 3) := he
        have ha : (a : Fin 3) ≠ 1 := by
          intro h
          exact absurd
            ((Set.ext_iff.mp hrem (a : Fin 3)).mpr (Set.mem_singleton_iff.mpr h)) a.2
        have hb : (b : Fin 3) ≠ 1 := by
          intro h
          exact absurd
            ((Set.ext_iff.mp hrem (b : Fin 3)).mpr (Set.mem_singleton_iff.mpr h)) b.2
        rw [pathGraph_adj] at hadj
        revert hadj ha hb
        generalize (a : Fin 3) = x
        generalize (b : Fin 3) = y
        revert x y; decide
    have hmap : (((pathGraph 3).induce
        (CaseBRemovedVertices ([[0, 1, 2]] : List (List (Fin 3))))ᶜ).map
          f_core).edgeSet = ∅ := by
      rw [SimpleGraph.edgeSet_map, hind, Set.image_empty]
    rw [hmap]
    exact Set.injOn_empty _
  -- Apply the (assumed) universal statement to obtain an absorbing embedding …
  obtain ⟨f_paths, hvalid⟩ :=
    H 1 Nat.one_pos (Fin 3) (pathGraph 3) hT [[0, 1, 2]] hbare hdisj f_core hcore
  -- … which forces `(pathGraph 3).edgeSet.ncard ≤ 1`, contradicting `= 2`.
  have hle := valid_caseB_absorption_edge_ncard_le 1 Nat.one_pos (pathGraph 3)
    [[0, 1, 2]] f_core f_paths hvalid
  rw [hES2] at hle
  omega

end Ringel
