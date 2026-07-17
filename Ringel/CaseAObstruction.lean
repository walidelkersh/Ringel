import Ringel.CaseA
import Ringel.CaseBObstruction

/-!
# Case A, Phase 2 — the absorption-matching obstruction (analytical infrastructure)

This file documents, with fully machine-checked lemmas, *why* the Phase-2 lemma
`exists_absorption_matching` (in `Ringel/CaseA.lean`) cannot be discharged soundly **as currently
stated**, and isolates the genuine mathematical content that a faithful version would require.

The open proof in `exists_absorption_matching` sits behind `exists_absorption_matching_prob`, whose
only real hypothesis is
`prob_event (fun f_leaves => valid_absorption n hn T S f_core f_leaves) > 0`.
By `prob_pos_of_exists` / `exists_of_prob_gt_zero` (in `Ringel/ProbBounds.lean`), over the finite,
nonempty sample space of embeddings this positivity is **equivalent** to the plain existence
`∃ f_leaves, …`. So the difficulty is not probabilistic — it is the bare existence of an absorbing
leaf embedding.

The key structural fact proved here is `valid_caseA_absorption_edge_ncard_le`: **any** successful
leaf absorption forces `T.edgeSet.ncard ≤ n`. Indeed a valid absorption glues `f_core` and
`f_leaves` into a single injective vertex map (`extend_map`) whose image edge-set is rainbow under
the `n`-colour `ndColouring`, and a rainbow copy can use at most `n` distinct colours
(`rainbow_map_edge_ncard_le`, reused from `Ringel/CaseBObstruction.lean`), hence at most `n` edges.

Consequently the *conclusion* of `exists_absorption_matching` entails `T.edgeSet.ncard ≤ n`, yet
**none of its hypotheses supply this bound**: `exists_absorption_matching` omits the edge-count
hypothesis `T.edgeSet.ncard = n` (and the paper's regime hypotheses) that are available at its only
call site inside `extend_caseA_leaves`. Because a tree may have arbitrarily many edges while `n`
stays fixed, the statement is **false** as written. This is made fully explicit and machine-checked
in `exists_absorption_matching_statement_false` below, using the concrete instance
`T = pathGraph 3` (`2` edges) with `n = 1` (one available colour): every hypothesis of
`exists_absorption_matching` holds, yet no absorbing leaf embedding exists.

This mirrors the honest treatment of the analogous Case B Phase-2 gap (`caseB_absorb_paths`,
documented in `Ringel/CaseBObstruction.lean`) and the Case A Phase-1 gap
(`bound_vertex_collisions`): rather than fabricate an unsound proof, we pin the obstruction down
with verified lemmas and document exactly what a faithful, provable version would need.
-/

open SimpleGraph

namespace Ringel

/-- Gluing an injective core embedding `f_core` with an injective leaf embedding `f_leaves` whose
range is disjoint from the core's range (`UsedVertices`) yields an injective vertex map on all of
`V`. This is the `extend_map` used in the Case A absorption conclusion. -/
lemma extend_map_injective {V : Type*} (S : Set V) (n : ℕ)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1)) (f_leaves : S ↪ Fin (2 * n + 1))
    (h_disj : Disjoint (Set.range f_leaves) (UsedVertices S f_core)) :
    Function.Injective (extend_map S n f_core f_leaves) := by
  classical
  intro v w h_eq
  dsimp only [extend_map] at h_eq
  by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
  · rw [dif_pos hv, dif_pos hw] at h_eq
    exact Subtype.ext_iff.mp (f_leaves.injective h_eq)
  · rw [dif_pos hv, dif_neg hw] at h_eq
    have hv_in : f_leaves ⟨v, hv⟩ ∈ Set.range f_leaves := Set.mem_range_self _
    have hw_in : f_core ⟨w, hw⟩ ∈ UsedVertices S f_core := Set.mem_range_self _
    rw [h_eq] at hv_in
    exact absurd hw_in (Set.disjoint_left.mp h_disj hv_in)
  · rw [dif_neg hv, dif_pos hw] at h_eq
    have hw_in : f_leaves ⟨w, hw⟩ ∈ Set.range f_leaves := Set.mem_range_self _
    have hv_in : f_core ⟨v, hv⟩ ∈ UsedVertices S f_core := Set.mem_range_self _
    rw [← h_eq] at hw_in
    exact absurd hv_in (Set.disjoint_left.mp h_disj hw_in)
  · rw [dif_neg hv, dif_neg hw] at h_eq
    exact Subtype.ext_iff.mp (f_core.injective h_eq)

/-- **The absorption-matching obstruction (machine-checked).** Any valid Case A leaf absorption
forces the tree to have at most `n` edges. Since `exists_absorption_matching` has no hypothesis
bounding `T.edgeSet.ncard`, its conclusion cannot hold in general. -/
lemma valid_caseA_absorption_edge_ncard_le {V : Type*} [Finite V] (n : ℕ) (hn : 0 < n)
    (T : SimpleGraph V) (S : Set V)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1)) (f_leaves : S ↪ Fin (2 * n + 1))
    (h_disj : Disjoint (Set.range f_leaves) (UsedVertices S f_core))
    (h_rainbow : Set.InjOn (ndColouring n hn)
      (Sym2.map (extend_map S n f_core f_leaves) '' T.edgeSet)) :
    T.edgeSet.ncard ≤ n := by
  -- Package the glued vertex map as an embedding and reuse `rainbow_map_edge_ncard_le`.
  refine rainbow_map_edge_ncard_le n hn T
    ⟨extend_map S n f_core f_leaves, extend_map_injective S n f_core f_leaves h_disj⟩ ?_
  rw [SimpleGraph.edgeSet_map]
  exact h_rainbow

/-- **`exists_absorption_matching` is false as currently stated.**

The universally-quantified statement of `exists_absorption_matching` (all hypotheses ⇒ an absorbing
leaf embedding exists) does not hold: it lacks any hypothesis bounding the number of edges of `T` by
the number `n` of available colours. The witness is the path `pathGraph 3` (a tree with `2` edges)
with `n = 1` (one colour). Its two leaves `{0, 2}` are pairwise non-adjacent (an independent set of
leaves), so all hypotheses hold for any core embedding `f_core`; yet `2 > 1`, so by
`valid_caseA_absorption_edge_ncard_le` no absorbing leaf embedding exists. -/
theorem exists_absorption_matching_statement_false :
    ¬ ∀ (n : ℕ) (hn : 0 < n) (V : Type) [Finite V] (T : SimpleGraph V)
        (_hT : T.IsTree) (S : Set V) (_hS_leaves : ∀ v ∈ S, IsLeaf T v)
        (_hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
        (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1)),
        ∃ f_leaves : S ↪ Fin (2 * n + 1),
          (Disjoint (Set.range f_leaves) (UsedVertices S f_core)) ∧
          Set.InjOn (ndColouring n hn)
            (Sym2.map (extend_map S n f_core f_leaves) '' T.edgeSet) := by
  intro H
  -- The concrete witness: `T = pathGraph 3`, a tree with two edges, and `n = 1`.
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
  -- The two endpoints `{0, 2}` are leaves of `pathGraph 3`.
  set S : Set (Fin 3) := {0, 2} with hSdef
  have hS_leaves : ∀ v ∈ S, IsLeaf (pathGraph 3) v := by
    intro v hv
    rw [hSdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · refine ⟨1, by simp only [pathGraph_adj]; decide, ?_⟩
      intro w hw; rw [pathGraph_adj] at hw
      fin_cases w <;> first | rfl | (exfalso; revert hw; decide)
    · refine ⟨1, by simp only [pathGraph_adj]; decide, ?_⟩
      intro w hw; rw [pathGraph_adj] at hw
      fin_cases w <;> first | rfl | (exfalso; revert hw; decide)
  -- The leaves are pairwise non-adjacent (an independent set).
  have hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬(pathGraph 3).Adj v w := by
    intro v hv w hw hvw
    rw [hSdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hv hw
    rw [pathGraph_adj]
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
      first
        | exact absurd rfl hvw
        | decide
  -- The trivial core embedding (inclusion of the complement subtype).
  set f_core : (Sᶜ : Set (Fin 3)) ↪ Fin 3 := Function.Embedding.subtype _ with hfc
  -- Apply the (assumed) universal statement to obtain an absorbing embedding …
  obtain ⟨f_leaves, h_disj, h_rainbow⟩ :=
    H 1 Nat.one_pos (Fin 3) (pathGraph 3) hT S hS_leaves hS_indep f_core
  -- … which forces `(pathGraph 3).edgeSet.ncard ≤ 1`, contradicting `= 2`.
  have hle := valid_caseA_absorption_edge_ncard_le 1 Nat.one_pos (pathGraph 3) S
    f_core f_leaves h_disj h_rainbow
  rw [hES2] at hle
  omega

end Ringel
