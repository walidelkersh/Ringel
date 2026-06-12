import Ringel.Statement
import Ringel.Primitives
import Mathlib.Data.Set.Card.Arithmetic

namespace Ringel



/-- The "core" of a Case A tree is the subgraph induced by removing the independent leaves `S`.
Since `S` consists only of leaves, the core remains connected and acyclic, hence a tree. -/
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
    (root : (Sᶜ : Set V)) (root_val : Fin (2 * n + 1))
    (C : CoreColors n T S) (σ : CoreSigns T S) :
    ∃ f : (Sᶜ : Set V) → Fin (2 * n + 1),
      f root = root_val ∧
      ∀ (u v : (Sᶜ : Set V)) (huv : (CaseACore T S).Adj u v),
        ndColouring n hn s(f u, f v) = C ⟨s(u, v), huv⟩ := by
  sorry

/-- The vertex collision probability bound using the Littlewood-Offord / random walk logic. -/
lemma bound_vertex_collisions (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree) (S : Set V)
    (root : (Sᶜ : Set V)) (root_val : Fin (2 * n + 1))
    (C : CoreColors n T S) :
    -- There exists a sign assignment that avoids vertex collisions (injectivity)
    ∃ σ : CoreSigns T S, Function.Injective (Classical.choose (exists_embed_from_signs n hn T hT S root root_val C σ)) := by
  sorry

/-- The actual MPS embedding logic relies on mapping edges to colors
and picking random signs to avoid vertex collisions via random walk bounds. -/
lemma random_embed_core (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_size : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ S.ncard) :
    ∃ f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn) ((CaseACore T S).map f_core).edgeSet := by
  -- 1. Pick an arbitrary root in the core (since T is a tree, core is a tree, hence nonempty if n > 0)
  have h_core_nonempty : Nonempty (Sᶜ : Set V) := sorry
  obtain ⟨root⟩ := h_core_nonempty
  -- 2. Pick any valid color assignment C (possible since |E(Core)| <= n)
  have h_colors : Nonempty (CoreColors n T S) := sorry
  obtain ⟨C⟩ := h_colors
  -- 3. Use the collision bound to find a sign assignment that guarantees injectivity
  obtain ⟨σ, h_inj⟩ := bound_vertex_collisions n hn T hT S root 0 C
  -- 4. Extract the embedding from the chosen signs
  have h_exists := exists_embed_from_signs n hn T hT S root 0 C σ
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

/-- Step 1 (M1+M2 equivalent): Embed the core of the tree into `K_{2n+1}`. -/
lemma embed_caseA_core (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (hS_size : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ S.ncard) :
    ∃ f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn) ((CaseACore T S).map f_core).edgeSet := by
  exact random_embed_core δ hδ n hn T hT hcard S hS_leaves hS_size

/-- Step 2 (Absorption): Extend the core embedding to include the leaves in `S`,
yielding a full rainbow copy of `T`. -/
lemma extend_caseA_leaves (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1))
    (h_core_inj : Set.InjOn (ndColouring n hn) ((CaseACore T S).map f_core).edgeSet) :
    HasRainbowCopy n T := by
  sorry

/-- **Case A rainbow copy (§4, §6, M1+M2).** For small `δ > 0` and large `n`, every Case A
tree that is not Case C has a rainbow copy in the ND-coloured `K_{2n+1}`. -/
theorem caseA_rainbow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseA δ n T → ¬IsCaseC δ n T → HasRainbowCopy n T := by
  filter_upwards [Filter.Ioi_mem_atTop 0] with n hn
  intro V inst T hT hcard hA hNotC
  obtain ⟨S, hS_leaves, hS_indep, hS_size⟩ := hA
  -- From Step 1, embed the core
  have ⟨f_core, h_core_inj⟩ := embed_caseA_core δ hδ n hn T hT hcard S hS_leaves hS_indep hS_size
  -- From Step 2, extend to the leaves to get the final rainbow copy
  exact extend_caseA_leaves δ hδ n hn T hT hcard S hS_leaves hS_indep f_core h_core_inj

end Ringel
