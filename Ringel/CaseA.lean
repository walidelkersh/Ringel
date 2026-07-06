import Mathlib
import Ringel.Primitives
import Ringel.ProbBounds
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Ringel.LittlewoodOfford
import Ringel.ProbabilisticMatching

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


/-- Signed sum of edge increments `δ` along a walk, valued in `Fin M`. -/
def walkSum {α : Type*} {G : SimpleGraph α} {M : ℕ} [NeZero M]
    (δ : ∀ a b, G.Adj a b → Fin M) :
    ∀ {a b : α}, G.Walk a b → Fin M
  | _, _, SimpleGraph.Walk.nil => 0
  | _, _, SimpleGraph.Walk.cons h p => δ _ _ h + walkSum δ p

lemma walkSum_nil {α : Type*} {G : SimpleGraph α} {M : ℕ} [NeZero M]
    (δ : ∀ a b, G.Adj a b → Fin M) (a : α) :
    walkSum δ (SimpleGraph.Walk.nil : G.Walk a a) = 0 := rfl

lemma walkSum_cons {α : Type*} {G : SimpleGraph α} {M : ℕ} [NeZero M]
    (δ : ∀ a b, G.Adj a b → Fin M) {a b c : α} (h : G.Adj a b) (p : G.Walk b c) :
    walkSum δ (SimpleGraph.Walk.cons h p) = δ a b h + walkSum δ p := rfl

lemma walkSum_append {α : Type*} {G : SimpleGraph α} {M : ℕ} [NeZero M]
    (δ : ∀ a b, G.Adj a b → Fin M) {a b c : α} (p : G.Walk a b) (q : G.Walk b c) :
    walkSum δ (p.append q) = walkSum δ p + walkSum δ q := by
  induction p with
  | nil => rw [SimpleGraph.Walk.nil_append, walkSum_nil, zero_add]
  | cons h p ih =>
    rw [SimpleGraph.Walk.cons_append, walkSum_cons, walkSum_cons, ih, add_assoc]

lemma walkSum_concat {α : Type*} {G : SimpleGraph α} {M : ℕ} [NeZero M]
    (δ : ∀ a b, G.Adj a b → Fin M) {a b c : α} (p : G.Walk a b) (h : G.Adj b c) :
    walkSum δ (p.concat h) = walkSum δ p + δ b c h := by
  rw [SimpleGraph.Walk.concat_eq_append, walkSum_append, walkSum_cons, walkSum_nil, add_zero]

/-- **Tree embedding.** Given a tree `G` on a linearly ordered vertex type, a root with target
value `root_val`, an injective edge colouring `C` and an orientation `σ`, there is a vertex map `f`
with `f root = root_val` such that every edge `s(u,v)` receives ND-colour `C ⟨s(u,v), huv⟩`.
Concretely `f v = root_val + Σ` of signed increments `±(C(e)+1)` along the unique root-to-`v` path;
the sign of each edge is fixed by comparing its endpoints in the linear order against `σ`. Each
tree edge then realizes a `±(C(e)+1)` step, which `ndColouring_step` shows has ND-colour `C(e)`. -/
lemma tree_embed {α : Type*} (n : ℕ) (hn : 0 < n) (G : SimpleGraph α) (hG : G.IsTree)
    [LinearOrder α] (root : α) (root_val : Fin (2 * n + 1))
    (C : G.edgeSet ↪ Fin n) (σ : G.edgeSet → Bool) :
    ∃ f : α → Fin (2 * n + 1), f root = root_val ∧
      ∀ (u v : α) (huv : G.Adj u v),
        ndColouring n hn s(f u, f v) = C ⟨s(u, v), huv⟩ := by
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  classical
  let edge : ∀ a b, G.Adj a b → G.edgeSet := fun a b h => ⟨s(a, b), h⟩
  let δ : ∀ a b, G.Adj a b → Fin (2 * n + 1) := fun a b h =>
    let m : Fin (2 * n + 1) :=
      ⟨(C (edge a b h)).val + 1, by have := (C (edge a b h)).isLt; omega⟩
    if decide (a < b) = σ (edge a b h) then m else -m
  have hedge_swap : ∀ a b (h : G.Adj a b), edge b a h.symm = edge a b h := by
    intro a b h; apply Subtype.ext; exact Sym2.eq_swap
  have hanti : ∀ a b (h : G.Adj a b), δ b a h.symm = - δ a b h := by
    intro a b h
    have hne : a ≠ b := h.ne
    change (let m : Fin (2 * n + 1) := ⟨(C (edge b a h.symm)).val + 1, _⟩;
          if decide (b < a) = σ (edge b a h.symm) then m else -m) = - _
    simp only [hedge_swap a b h]
    have hflip : decide (b < a) = !(decide (a < b)) := by
      rcases lt_trichotomy a b with hlt | heq | hgt
      · simp [hlt, asymm hlt]
      · exact absurd heq hne
      · simp [hgt, asymm hgt]
    rw [hflip]
    cases hab : decide (a < b) <;> cases hs : σ (edge a b h) <;> simp [δ, hab, hs]
  let P : ∀ w, G.Walk root w := fun w => (hG.existsUnique_path root w).choose
  have hPpath : ∀ w, (P w).IsPath := fun w => (hG.existsUnique_path root w).choose_spec.1
  have hPuniq : ∀ w (q : G.Walk root w), q.IsPath → q = P w :=
    fun w q hq => (hG.existsUnique_path root w).choose_spec.2 q hq
  refine ⟨fun v => root_val + walkSum δ (P v), ?_, ?_⟩
  · have hr : P root = SimpleGraph.Walk.nil := (hPuniq root _ SimpleGraph.Walk.IsPath.nil).symm
    change root_val + walkSum δ (P root) = root_val
    rw [hr, walkSum_nil, add_zero]
  · intro u v huv
    have hfv : root_val + walkSum δ (P v)
        = (root_val + walkSum δ (P u)) + δ u v huv := by
      by_cases hu : u ∈ (P v).support
      · have htk : ((P v).takeUntil u hu).IsPath := (hPpath v).takeUntil hu
        have htk_eq : (P v).takeUntil u hu = P u := hPuniq u _ htk
        have hdr : ((P v).dropUntil u hu).IsPath := (hPpath v).dropUntil hu
        have hdr_eq : (P v).dropUntil u hu = huv.toWalk :=
          (hG.existsUnique_path u v).unique hdr (SimpleGraph.Walk.IsPath.of_adj huv)
        have hspec := SimpleGraph.Walk.take_spec (P v) hu
        have hPv : P v = (P u).append huv.toWalk := by
          rw [← htk_eq, ← hdr_eq]; exact hspec.symm
        rw [hPv, walkSum_append]
        have hw : walkSum δ huv.toWalk = δ u v huv := by
          change walkSum δ (SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil) = δ u v huv
          rw [walkSum_cons, walkSum_nil, add_zero]
        rw [hw]; abel
      · have hcc : ((P v).concat huv.symm).IsPath := (hPpath v).concat hu huv.symm
        have hPu : (P v).concat huv.symm = P u := hPuniq u _ hcc
        have hws : walkSum δ (P u) = walkSum δ (P v) + δ v u huv.symm := by
          rw [← hPu]; exact walkSum_concat δ (P v) huv.symm
        have hsym : δ v u huv.symm = - δ u v huv := hanti u v huv
        rw [hws, hsym]; abel
    change ndColouring n hn s(root_val + walkSum δ (P u), root_val + walkSum δ (P v))
        = C ⟨s(u, v), huv⟩
    rw [hfv]
    have hδval : (δ u v huv).val = (C ⟨s(u, v), huv⟩).val + 1 ∨
        (δ u v huv).val = 2 * n + 1 - ((C ⟨s(u, v), huv⟩).val + 1) := by
      set m : Fin (2 * n + 1) := ⟨(C ⟨s(u, v), huv⟩).val + 1,
        by have := (C ⟨s(u, v), huv⟩).isLt; omega⟩ with hm_def
      have hmval : m.val = (C ⟨s(u, v), huv⟩).val + 1 := rfl
      have hm0 : m ≠ 0 := by
        intro h; have hz : m.val = 0 := by rw [h]; rfl
        rw [hmval] at hz; omega
      have hδ_def : δ u v huv = if decide (u < v) = σ ⟨s(u, v), huv⟩ then m else -m := rfl
      rw [hδ_def]
      by_cases hcond : decide (u < v) = σ ⟨s(u, v), huv⟩
      · rw [if_pos hcond]; left; exact hmval
      · rw [if_neg hcond]; right
        rw [Fin.val_neg, hmval, if_neg hm0]
    exact ndColouring_step n hn (root_val + walkSum δ (P u)) (δ u v huv)
      (C ⟨s(u, v), huv⟩) hδval

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
  haveI : Fintype ((Sᶜ : Set V)) := Fintype.ofFinite _
  haveI : LinearOrder ((Sᶜ : Set V)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  exact tree_embed n hn (CaseACore T S) (isTree_core T hT S hS_leaves hS_indep)
    root root_val C σ


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
  haveI : Fintype (CoreSigns T S) := by unfold CoreSigns; exact Fintype.ofFinite _
  -- `h_exists` is discharged constructively by `exists_embed_from_signs` (proven via `tree_embed`);
  -- the remaining `sorry` is the genuine Littlewood–Offord anticoncentration bound (`h_prob`).
  exact bound_vertex_collisions_prob n hn T hT S hS_leaves hS_indep root root_val C
    (fun σ => exists_embed_from_signs n hn T hT S hS_leaves hS_indep root root_val C σ) sorry


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
    haveI : Fintype T.edgeSet := Fintype.ofFinite _
    exact ⟨Fintype.equivFinOfCardEq (by rwa [Nat.card_eq_fintype_card] at heq)⟩
  obtain ⟨e_equiv⟩ := h_equiv
  have h_inj : (CaseACore T S).edgeSet ↪ T.edgeSet := by
    let f : (CaseACore T S).edgeSet → T.edgeSet := fun e =>
      ⟨Sym2.map Subtype.val e.val, by
        have he := e.property
        induction' e' : e.val using Sym2.ind with u v
        have hadj : (CaseACore T S).Adj u v := by
          rw [e'] at he
          exact he
        rw [Sym2.map_pair_eq, SimpleGraph.mem_edgeSet]
        exact hadj⟩
    have h_inj_f : Function.Injective f :=
      fun e1 e2 h_eq =>
        Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h_eq))
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
  haveI : Fintype (S ↪ Fin (2 * n + 1)) := Fintype.ofFinite _
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

/-- `∀ᶠ` wrapper around `caseA_rainbow`, suitable for `filter_upwards` in the spine. -/
theorem caseA_rainbow_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n → IsCaseA δ n T → ¬IsCaseC δ n T → HasRainbowCopy n T := by
  apply Filter.eventually_atTop.mpr
  exact ⟨2, fun n hn V _ T hT hcard ⟨S, hS_leaves, hS_indep, hS_size⟩ _ =>
    caseA_rainbow δ hδ n (by omega) (by omega) T hT hcard S hS_leaves hS_size hS_indep⟩

end Ringel
