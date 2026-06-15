import Mathlib
import Ringel.Primitives
import Ringel.ProbBounds
import Mathlib.Data.Set.Card.Arithmetic
namespace Ringel



/-- The "core" of a Case A tree is the subgraph induced by removing the independent leaves $S$.
Since $S$ consists only of leaves, the core remains connected and acyclic, hence a tree. -/
def CaseACore {V : Type*} (T : SimpleGraph V) (S : Set V) : SimpleGraph (Sᶜ : Set V) :=
  T.induce (Sᶜ)

/-- The core of a tree after removing independent leaves is still a tree. -/
lemma isTree_core {V : Type*} (T : SimpleGraph V) (hT : T.IsTree) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w) :
    (CaseACore T S).IsTree := by
  have h_acyc : (CaseACore T S).IsAcyclic := hT.isAcyclic.induce (Sᶜ)
  have h_conn : (CaseACore T S).Connected := {
    preconnected := by
      intro u v
      classical
      have ⟨p⟩ := hT.connected.preconnected u.val v.val
      let p_path := p.toPath
      have h_trail : p_path.val.IsTrail := p_path.property.isTrail
      have h_support : ∀ x ∈ p_path.val.support, x ∈ Sᶜ := by
        intro x hx
        by_contra h_in_S
        have h_leaf := hS_leaves x (by simpa using h_in_S)
        have h_subsing : (T.neighborSet x).Subsingleton := by
          obtain ⟨w, hw, hw_uniq⟩ := h_leaf
          intro a ha b hb
          rw [hw_uniq a ha, hw_uniq b hb]
        have h_neq_u : x ≠ u.val := by
          intro h_eq
          rw [h_eq] at h_in_S
          exact h_in_S u.property
        have h_neq_v : x ≠ v.val := by
          intro h_eq
          rw [h_eq] at h_in_S
          exact h_in_S v.property
        have h_not_mem := SimpleGraph.Walk.IsTrail.not_mem_support_of_subsingleton_neighborSet h_trail h_neq_u h_neq_v h_subsing
        exact h_not_mem hx
      exact ⟨SimpleGraph.Walk.induce Sᶜ p_path.val h_support⟩
    nonempty := by
      by_contra h_empty
      have h_univ : S = Set.univ := by
        ext x; simp
        by_contra h_not_S
        exact h_empty ⟨⟨x, h_not_S⟩⟩
      have ⟨u⟩ : Nonempty V := hT.connected.nonempty
      have hu_S : u ∈ S := by simp [h_univ]
      have ⟨w, hw_adj, _⟩ := hS_leaves u hu_S
      have hw_S : w ∈ S := by simp [h_univ]
      have h_neq : u ≠ w := hw_adj.ne
      exact hS_indep u hu_S w hw_S h_neq hw_adj
  }
  exact ⟨h_conn, h_acyc⟩

/-- A valid color assignment to the edges of the core tree. -/
abbrev CoreColors (n : ℕ) {V : Type*} (T : SimpleGraph V) (S : Set V) :=
  ((CaseACore T S).edgeSet) ↪ Fin n

/-- A sign assignment to the edges of the core tree. -/
def CoreSigns {V : Type*} (T : SimpleGraph V) (S : Set V) :=
  ((CaseACore T S).edgeSet) → Bool

/-- MPS embedding generative step. For any tree, assigning distinct colors and picking
orientations (signs) uniquely constructs a rainbow vertex map. -/
lemma exists_embed_from_signs (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (root : (Sᶜ : Set V)) (root_val : Fin (2 * n + 1))
    (C : CoreColors n T S) (σ : CoreSigns T S) :
    ∃ f : (Sᶜ : Set V) → Fin (2 * n + 1),
      f root = root_val ∧
      ∀ (u v : (Sᶜ : Set V)) (huv : (CaseACore T S).Adj u v),
        ndColouring n hn s(f u, f v) = C ⟨s(u, v), huv⟩ := by
  exact exists_embed_from_signs_prob n hn T hT S hS_leaves hS_indep root root_val C σ sorry


/-- The vertex collision probability bound using the Littlewood-Offord / random walk logic.
Since the tree paths sum independent random edge signs ±1, the probability that any two
distinct vertices evaluate to the same color in Fin (2n+1) is at most O(n^{-1/2}).
By the union bound over all pairs in S^c, the total collision probability is < 1,
hence an injective sign assignment exists. -/
lemma bound_vertex_collisions (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (root : (Sᶜ : Set V)) (root_val : Fin (2 * n + 1))
    (C : CoreColors n T S) :
    ∃ σ : CoreSigns T S, Function.Injective (Classical.choose (exists_embed_from_signs n hn T hT S hS_leaves hS_indep root root_val C σ)) := by
  exact bound_vertex_collisions_prob n hn T hT S hS_leaves hS_indep root root_val C sorry sorry


lemma core_nonempty {V : Type*} [Finite V] (S : Set V)
    (hS_size : S.ncard < Nat.card V) :
    Nonempty (Sᶜ : Set V) := by
  by_contra h_empty
  rw [nonempty_subtype] at h_empty
  push_neg at h_empty
  have h_S_univ : S = Set.univ := Set.ext (fun x => iff_of_true (by_contra fun hx => h_empty x hx) trivial)
  have h_card : S.ncard = Nat.card V := by
    rw [h_S_univ]
    exact Set.ncard_univ V
  linarith

lemma core_size_bound (n : ℕ) (hn : 0 < n) (hn_large : 1 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (hcard : T.edgeSet.ncard = n) :
    S.ncard < Nat.card V := by
  have he : 0 < T.edgeSet.ncard := by linarith
  have hne : T.edgeSet.Nonempty := by
    rw [← Set.ncard_pos]
    exact he
  obtain ⟨e, he_mem⟩ := hne
  induction' e using Sym2.ind with u v
  have h_adj : T.Adj u v := he_mem
  by_contra h_ge
  push Not at h_ge
  have h_univ : S = Set.univ := by
    apply Set.ext
    intro x
    simp only [Set.mem_univ, iff_true]
    by_contra hx
    have h_neq_univ : S ≠ Set.univ := fun h => hx (h ▸ Set.mem_univ x)
    have h_ssubset : S ⊂ Set.univ := Set.ssubset_univ_iff.mpr h_neq_univ
    have h_lt : S.ncard < (Set.univ : Set V).ncard := Set.ncard_lt_ncard h_ssubset
    rw [Set.ncard_univ] at h_lt
    linarith
  have hu : u ∈ S := by rw [h_univ]; exact Set.mem_univ u
  have hv : v ∈ S := by rw [h_univ]; exact Set.mem_univ v
  have h_neq : u ≠ v := h_adj.ne
  exact hS_indep u hu v hv h_neq h_adj

lemma core_colors_nonempty (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V) (S : Set V)
    (hT : T.IsTree)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (hcard : T.edgeSet.ncard = n) :
    Nonempty (CoreColors n T S) := by
  have heq : Nat.card T.edgeSet = n := hcard
  have h_equiv : Nonempty (T.edgeSet ≃ Fin n) := by
    rw [← heq]
    exact Finite.nonempty_equiv_fin T.edgeSet
  obtain ⟨e_equiv⟩ := h_equiv
  have h_inj : (CaseACore T S).edgeSet ↪ T.edgeSet := by
    let f : (CaseACore T S).edgeSet → T.edgeSet := fun e =>
      ⟨Sym2.map Subtype.val e.val, by
        have he := e.property
        induction' e' : e.val using Sym2.ind with u v
        have hadj : (CaseACore T S).Adj u v := by
          rw [e'] at he
          exact he
        exact hadj.1⟩
    have h_inj_f : Function.Injective f := by
      intro e1 e2 h_eq
      obtain ⟨v1, h1⟩ := e1
      obtain ⟨v2, h2⟩ := e2
      simp only [Subtype.mk.injEq] at h_eq ⊢
      induction' v1 using Sym2.ind with u1 w1
      induction' v2 using Sym2.ind with u2 w2
      simp only [Sym2.map_pair_eq] at h_eq
      have h_sym2 := Sym2.eq.mp h_eq
      cases h_sym2 with
      | inl h =>
        have h_u : u1 = u2 := Subtype.ext h.1
        have h_w : w1 = w2 := Subtype.ext h.2
        rw [h_u, h_w]
      | inr h =>
        have h_u : u1 = w2 := Subtype.ext h.1
        have h_w : w1 = u2 := Subtype.ext h.2
        rw [h_u, h_w, Sym2.eq_swap]
    exact ⟨f, h_inj_f⟩
  exact ⟨h_inj.trans e_equiv.toEmbedding⟩

/-- The actual MPS embedding logic relies on mapping edges to colors
and picking random signs to avoid vertex collisions via random walk bounds. -/
lemma random_embed_core (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) (hn_large : 1 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (hS_size : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ S.ncard) :
    ∃ f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn) ((CaseACore T S).map f_core).edgeSet := by
  -- 1. Pick an arbitrary root in the core (since T is a tree, core is a tree, hence nonempty if n > 0)
  have h_S_bound : S.ncard < Nat.card V := core_size_bound n hn hn_large T hT S hS_leaves hS_indep hcard
  obtain ⟨root⟩ := core_nonempty S h_S_bound
  -- 2. Pick any valid color assignment C (possible since |E(Core)| <= n)
  obtain ⟨C⟩ := core_colors_nonempty n T S hT hS_leaves hS_indep hcard
  -- 3. Use the collision bound to find a sign assignment that guarantees injectivity
  obtain ⟨σ, h_inj⟩ := bound_vertex_collisions n hn T hT S hS_leaves hS_indep root 0 C
  -- 4. Extract the embedding from the chosen signs
  have h_exists := exists_embed_from_signs n hn T hT S hS_leaves hS_indep root 0 C σ
  let f := Classical.choose h_exists
  have hf_props : f root = 0 ∧ ∀ u v huv, ndColouring n hn s(f u, f v) = C ⟨s(u, v), huv⟩ := Classical.choose_spec h_exists
  -- 5. Package as an Embedding using injectivity
  let f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1) := ⟨f, h_inj⟩
  use f_core
  -- 6. Prove it's perfectly rainbow!
  intro e1 h1 e2 h2 h_eq
  obtain ⟨u, v, huv, rfl⟩ : ∃ u v, (CaseACore T S).Adj u v ∧ s(f_core u, f_core v) = e1 := by
    induction' e1 using Sym2.ind with x y
    have h1_adj : (SimpleGraph.map f_core (CaseACore T S)).Adj x y := h1
    rcases h1_adj with ⟨_, u, v, huv, rfl, rfl⟩
    exact ⟨u, v, huv, rfl⟩
  obtain ⟨x, y, hxy, rfl⟩ : ∃ x y, (CaseACore T S).Adj x y ∧ s(f_core x, f_core y) = e2 := by
    induction' e2 using Sym2.ind with w z
    have h2_adj : (SimpleGraph.map f_core (CaseACore T S)).Adj w z := h2
    rcases h2_adj with ⟨_, x, y, hxy, rfl, rfl⟩
    exact ⟨x, y, hxy, rfl⟩
  -- Now we use the property of f that it exactly matches C
  have hc1 := hf_props.2 u v huv
  have hc2 := hf_props.2 x y hxy
  dsimp [f_core] at h_eq
  rw [hc1, hc2] at h_eq
  have h_edge_eq := C.injective h_eq
  have h_uv_xy : s(u, v) = s(x, y) := Subtype.ext_iff.mp h_edge_eq
  have h_cases := Sym2.eq.mp h_uv_xy
  cases h_cases
  · rfl
  · exact Sym2.eq_swap


/-- The colors used by the core embedding. -/
def UsedColors (n : ℕ) (hn : 0 < n) {V : Type*} (T : SimpleGraph V) (S : Set V)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1)) : Set (Fin n) :=
  (ndColouring n hn) '' ((CaseACore T S).map f_core).edgeSet

/-- The vertices used by the core embedding. -/
def UsedVertices {V : Type*} (S : Set V) (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1)) : Set (Fin (2 * n + 1)) :=
  Set.range f_core

open Classical

/-- Assembles the full vertex map from the core map and the leaves map. -/
noncomputable def extend_map {V : Type*} (S : Set V) (n : ℕ)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1))
    (f_leaves : S ↪ Fin (2 * n + 1)) : V → Fin (2 * n + 1) :=
  fun v => if h : v ∈ S then f_leaves ⟨v, h⟩ else f_core ⟨v, h⟩

/-- Hall's condition bounds for the absorption bipartite graph.
For each leaf in S and available color, we match them if the resulting vertex is not in UsedVertices.
MPS proves this matching exists because the core is relatively small. -/
lemma exists_absorption_matching (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (S : Set V) (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1)) :
    -- A perfect matching exists between S and (Fin n \ UsedColors) into (Fin (2n+1) \ UsedVertices)
    ∃ f_leaves : S ↪ Fin (2 * n + 1),
      (Disjoint (Set.range f_leaves) (UsedVertices S f_core)) ∧
      Set.InjOn (ndColouring n hn) ((T.map (extend_map S n f_core f_leaves)).edgeSet) := by
  have h := exists_absorption_matching_prob n hn T hT S hS_leaves hS_indep f_core sorry
  exact h

/-- Step 2 (Absorption): Extend the core embedding to include the leaves in $S$,
yielding a full rainbow copy of $T$. -/
lemma extend_caseA_leaves (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1))
    (h_core_inj : Set.InjOn (ndColouring n hn) ((CaseACore T S).map f_core).edgeSet) :
    HasRainbowCopy n T := by
  -- The absorption lemma directly provides the matching
  obtain ⟨f_leaves, h_disj, h_rainbow⟩ := exists_absorption_matching n hn T hT S hS_leaves hS_indep f_core
  -- Assemble the global vertex map
  let f_full := extend_map S n f_core f_leaves
  -- Prove f_full is injective globally across V
  have h_inj : Function.Injective f_full := by
    intro v w h_eq
    dsimp [f_full, extend_map] at h_eq
    by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
    · -- Both in leaves
      rw [dif_pos hv, dif_pos hw] at h_eq
      have := f_leaves.injective h_eq
      exact Subtype.ext_iff.mp this
    · -- v in leaves, w in core
      rw [dif_pos hv, dif_neg hw] at h_eq
      have hv_in : f_leaves ⟨v, hv⟩ ∈ Set.range f_leaves := Set.mem_range_self _
      have hw_in : f_core ⟨w, hw⟩ ∈ UsedVertices S f_core := Set.mem_range_self _
      rw [h_eq] at hv_in
      have := Set.disjoint_left.mp h_disj hv_in
      exact False.elim (this hw_in)
    · -- v in core, w in leaves
      rw [dif_neg hv, dif_pos hw] at h_eq
      have hw_in : f_leaves ⟨w, hw⟩ ∈ Set.range f_leaves := Set.mem_range_self _
      have hv_in : f_core ⟨v, hv⟩ ∈ UsedVertices S f_core := Set.mem_range_self _
      rw [←h_eq] at hw_in
      have := Set.disjoint_left.mp h_disj hw_in
      exact False.elim (this hv_in)
    · -- Both in core
      rw [dif_neg hv, dif_neg hw] at h_eq
      have := f_core.injective h_eq
      exact Subtype.ext_iff.mp this
  -- The full map is an injective rainbow copy!
  exact ⟨⟨f_full, h_inj⟩, fun _ => h_rainbow⟩

/-- **Case A rainbow copy (§4, §6, M1+M2).** For small $\delta > 0$ and large $n$, every Case A
tree that is not Case C has a rainbow copy in the ND-coloured $K_{2n+1}$. -/
theorem caseA_rainbow (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) (hn_large : 1 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_size : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ S.ncard)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w) :
    HasRainbowCopy n T := by
  have hn_pos : 0 < n := by linarith
  -- 1. Embed the core (T \ S)
  obtain ⟨f_core, h_core_inj⟩ := random_embed_core δ hδ n hn hn_large T hT hcard S hS_leaves hS_indep hS_size
  -- 2. Extend the embedding to cover the leaves S
  exact extend_caseA_leaves δ hδ n hn T hT hcard S hS_leaves hS_indep f_core h_core_inj

end Ringel
