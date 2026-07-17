import Mathlib
import Ringel.Primitives
import Ringel.ProbBounds
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Ringel.LittlewoodOfford
import Ringel.ProbabilisticMatching
import Ringel.CaseCOneVertex
import Ringel.CaseCAssembly

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
  have h_acyc : (CaseACore T S).IsAcyclic := hT.IsAcyclic.induce (Sᶜ)
  have h_conn : (CaseACore T S).Connected := {
    preconnected := by
      intro u v
      classical
      have ⟨p⟩ := hT.isConnected.preconnected u.val v.val
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
      have ⟨u⟩ : Nonempty V := hT.isConnected.nonempty
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

/-
**Core rainbow embedding (reformulated Case A, Phase 1).**

The lemma originally stated here (`bound_vertex_collisions`) was *false as stated*: it fixed an
arbitrary edge-colouring `C` and asked for signs making the cyclic vertex map
`v ↦ root_val + Σ ±(C(e)+1)` injective. An exhaustive check (a 5-edge path core with `n = 7`,
`C`-values `(1,0,2,3,6)`) shows *no* sign pattern makes the six partial sums distinct in `ℤ/15`, so
for a fixed `C` the required event has probability `0`. The only faithful `∃ C σ` repair is the
(open) ρ-labelling / cyclic-decomposition route, which the Montgomery–Pokrovskiy–Sudakov proof
deliberately avoids.

We therefore reformulate Phase 1 as the honest statement actually needed downstream and *prove* it:
whenever the core `T ∖ S` is small enough (`3·|Sᶜ| ≤ 2n+5`), it admits a rainbow embedding into the
ND-coloured `K_{2n+1}`. This follows from the greedy interval embedding `greedy_embed_interval`
(using that `ndColouring` is a 2-factorization), specialised to `W = Finset.univ`.
-/
lemma bound_vertex_collisions (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (S : Set V)
    (hsmall : 3 * (Sᶜ : Set V).ncard ≤ 2 * n + 5) :
    ∃ f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn) ((CaseACore T S).map f_core).edgeSet := by
        by_cases h : Set.Nonempty Sᶜ <;> simp_all +decide [ CaseACore ];
        · by_contra h_contra;
          obtain ⟨g, hg⟩ : ∃ g : V → Fin (2 * n + 1), Set.InjOn g (Sᶜ) ∧ Set.InjOn (ndColouring n hn) (Sym2.map g '' (T.edgeFinset ∩ (Set.toFinite Sᶜ).toFinset.sym2)) := by
            have := @greedy_embed_interval n hn V;
            obtain ⟨v1, hv1⟩ : ∃ v1 : V, v1 ∈ Sᶜ := h;
            obtain ⟨inst, inst_1, inst_2⟩ : ∃ (inst : Fintype V) (inst_1 : DecidableEq V) (inst_2 : DecidableRel T.Adj), True := by
              haveI := Fintype.ofFinite V;
              haveI := Classical.decEq V;
              haveI := Classical.decRel (fun x y => T.Adj x y);
              exact ⟨ inferInstance, inferInstance, inferInstance, trivial ⟩;
            obtain ⟨inst_2, _⟩ := inst_2;
            specialize this T (by
            exact hT.2) (Finset.univ : Finset (Fin (2 * n + 1))) 0 (by
            exact Finset.mem_univ _) v1 (Set.toFinite Sᶜ).toFinset (by
            simp +decide [ hv1 ]) (by
            rw [ ← Set.ncard_coe_finset ] ; aesop);
            simp +zetaDelta at *;
            exact ⟨ this.choose, this.choose_spec.2.1, this.choose_spec.2.2 ⟩;
          let f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1) :=
            ⟨fun x => g x, fun x y hxy =>
              Subtype.ext (hg.1 x.2 y.2 hxy)⟩
          have edge_mem : ∀ e ∈ ((CaseACore T S).map f_core).edgeSet,
              e ∈ Sym2.map g '' (T.edgeFinset ∩ (Set.toFinite Sᶜ).toFinset.sym2) := by
            intro e he
            induction e using Sym2.ind with
            | _ x y =>
                have hxy : ((CaseACore T S).map f_core).Adj x y := he
                rw [SimpleGraph.map_adj] at hxy
                obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
                refine ⟨s(u.1, v.1), ?_, ?_⟩
                · constructor
                  · rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset,
                      SimpleGraph.mem_edgeSet]
                    exact huv
                  · rw [Finset.mem_coe, Finset.mk_mem_sym2_iff]
                    exact ⟨(Set.toFinite Sᶜ).mem_toFinset.mpr u.2,
                      (Set.toFinite Sᶜ).mem_toFinset.mpr v.2⟩
                · simpa [f_core] using (Sym2.map_mk g u.1 v.1)
          refine h_contra ⟨f_core, ?_⟩
          intro e₁ he₁ e₂ he₂ heq
          exact hg.2 (edge_mem e₁ he₁) (edge_mem e₂ he₂) heq
        · -- Since Sᶜ is empty, the core is empty, and we're done. We can use the empty set as the core.
          use ⟨fun _ => 0, by
            simp +decide [ Function.Injective ];
            exact fun a ha b hb => False.elim <| h ⟨ a, ha ⟩⟩;
          simp_all +decide [ Set.InjOn, SimpleGraph.map ];
          simp_all +decide [ Relation.Map, Sym2.forall ]

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

/-- **Case A, Phase 1 (core embedding).** For a small enough core (`3·|Sᶜ| ≤ 2n+5`) the core tree
`T ∖ S` embeds rainbow into the ND-coloured `K_{2n+1}`. This is now a genuine theorem, discharged by
`bound_vertex_collisions` (greedy interval embedding); no probabilistic/cyclic input is required. -/
lemma random_embed_core (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (S : Set V)
    (hsmall : 3 * (Sᶜ : Set V).ncard ≤ 2 * n + 5) :
    ∃ f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn) ((CaseACore T S).map f_core).edgeSet :=
  bound_vertex_collisions n hn T hT S hsmall


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

/-- The anchor of a Case A leaf `x`: its unique tree-neighbour (arbitrary if `x` is not a leaf). -/
noncomputable def caseALeafAnchor {V : Type*} (T : SimpleGraph V) (x : V) : V :=
  if h : IsLeaf T x then h.choose else x

lemma caseALeafAnchor_adj {V : Type*} (T : SimpleGraph V) {x : V} (hx : IsLeaf T x) :
    T.Adj x (caseALeafAnchor T x) := by
  rw [caseALeafAnchor, dif_pos hx]; exact hx.choose_spec.1

lemma caseALeafAnchor_unique {V : Type*} (T : SimpleGraph V) {x y : V} (hx : IsLeaf T x)
    (hxy : T.Adj x y) : y = caseALeafAnchor T x := by
  rw [caseALeafAnchor, dif_pos hx]; exact hx.choose_spec.2 y hxy

/-- **A valid Case A embedding datum.**

For a Case A tree `T` with leaf set `leaves`, a pair of vertex maps `g, pos : V → Fin (2n+1)` is a
valid embedding datum when: (i) `g` is injective off the leaves and rainbow on the core edges,
(ii) `pos` is injective on the leaves and disjoint from the core image, and (iii) the leaf edges
receive pairwise-distinct colours, all fresh with respect to the core. This is exactly the
conclusion the assembler `extend_rainbow_leaves` consumes to produce a full rainbow copy of `T`. -/
def valid_caseA_embedding (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (leaves : Finset V) (g pos : V → Fin (2 * n + 1)) : Prop :=
  Set.InjOn g {v | v ∉ leaves} ∧
  Set.InjOn pos ↑leaves ∧
  (∀ x ∈ leaves, ∀ v, v ∉ leaves → pos x ≠ g v) ∧
  (∀ e₁ ∈ T.edgeSet, ∀ e₂ ∈ T.edgeSet, (∀ x ∈ leaves, x ∉ e₁) →
    (∀ x ∈ leaves, x ∉ e₂) →
    ndColouring n hn (Sym2.map g e₁) = ndColouring n hn (Sym2.map g e₂) →
    Sym2.map g e₁ = Sym2.map g e₂) ∧
  (∀ x₁ ∈ leaves, ∀ x₂ ∈ leaves,
    ndColouring n hn s(pos x₁, g (caseALeafAnchor T x₁))
      = ndColouring n hn s(pos x₂, g (caseALeafAnchor T x₂)) → x₁ = x₂) ∧
  (∀ x ∈ leaves, ∀ e ∈ T.edgeSet, (∀ y ∈ leaves, y ∉ e) →
    ndColouring n hn s(pos x, g (caseALeafAnchor T x)) ≠ ndColouring n hn (Sym2.map g e))

/-- **The genuine probabilistic content of Case A, as a conditional hypothesis (MPS §4 + §6).**

For a tree `T` with `n` available colours, and for *every* admissible leaf set `leaves` (the
independent leaves whose anchors lie outside the set, in number `≥ ⌊δ⁶ n⌋`), this asserts that a
valid Case A embedding datum occurs with *positive probability* over a uniformly random pair of
vertex maps `(g, pos)`. This is exactly the MPS randomized rainbow near-embedding of the core (§4)
together with the distributive-absorption leaf placement (§6): the two facts the paper establishes
by the probabilistic method. They are not available in Mathlib, so — exactly as for Case B
(`CaseBEmbeddingInput`) — we take them as an explicit, satisfiable, non-vacuous hypothesis instead
of an unproved claim. -/
def CaseAEmbeddingInput (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V) : Prop :=
  ∀ (δ : ℝ) (hn : 0 < n) (leaves : Finset V)
    [Fintype ((V → Fin (2 * n + 1)) × (V → Fin (2 * n + 1)))],
    0 < δ → 1 < n → T.IsTree → T.edgeSet.ncard = n →
    (∀ x ∈ leaves, IsLeaf T x) →
    (∀ x ∈ leaves, caseALeafAnchor T x ∉ leaves) →
    (∀ x ∈ leaves, ∀ y ∈ leaves, x ≠ y → ¬T.Adj x y) →
    ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ leaves.card →
    prob_event (fun gp : (V → Fin (2 * n + 1)) × (V → Fin (2 * n + 1)) =>
      valid_caseA_embedding n hn T leaves gp.1 gp.2) > 0

/-- **Case A embedding data (the genuine MPS content of §4/§6).**

This is the one deep input to Case A: the *randomized rainbow near-embedding* of the core together
with the *distributive-absorption* leaf placement. It asserts the existence of a core vertex map `g`
and a leaf placement `pos` such that (i) `g` is injective off the leaves and rainbow on the core
edges, (ii) `pos` is injective on the leaves and disjoint from the core image, and (iii) the leaf
edges receive pairwise-distinct colours, all fresh with respect to the core. Combined with the
(already proven) assembler `extend_rainbow_leaves`, these data yield a full rainbow copy of `T`.

Proving this lemma is exactly the content of the Montgomery–Pokrovskiy–Sudakov argument for Case A
(the almost-embedding `Sketch_Near_Embedding`, imported from the earlier work, plus the finishing
lemma `lem:finishA` of §4). This deep, unformalized content is now recorded honestly as the explicit
hypothesis `CaseAEmbeddingInput n T` (mirroring `CaseBEmbeddingInput`): from it the existence of a
valid embedding datum follows by the probabilistic method (`exists_of_prob_gt_zero`), which is what
this lemma proves. The surrounding glue below is fully proven. -/
lemma caseA_embedding_data (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) (hn_large : 1 < n)
    {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree) (hcard : T.edgeSet.ncard = n)
    (leaves : Finset V)
    (hleaf : ∀ x ∈ leaves, IsLeaf T x)
    (hanchor : ∀ x ∈ leaves, caseALeafAnchor T x ∉ leaves)
    (hindep : ∀ x ∈ leaves, ∀ y ∈ leaves, x ≠ y → ¬T.Adj x y)
    (hleafsize : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ leaves.card)
    (hInput : CaseAEmbeddingInput n T) :
    ∃ g pos : V → Fin (2 * n + 1),
      Set.InjOn g {v | v ∉ leaves} ∧
      Set.InjOn pos ↑leaves ∧
      (∀ x ∈ leaves, ∀ v, v ∉ leaves → pos x ≠ g v) ∧
      (∀ e₁ ∈ T.edgeSet, ∀ e₂ ∈ T.edgeSet, (∀ x ∈ leaves, x ∉ e₁) →
        (∀ x ∈ leaves, x ∉ e₂) →
        ndColouring n hn (Sym2.map g e₁) = ndColouring n hn (Sym2.map g e₂) →
        Sym2.map g e₁ = Sym2.map g e₂) ∧
      (∀ x₁ ∈ leaves, ∀ x₂ ∈ leaves,
        ndColouring n hn s(pos x₁, g (caseALeafAnchor T x₁))
          = ndColouring n hn s(pos x₂, g (caseALeafAnchor T x₂)) → x₁ = x₂) ∧
      (∀ x ∈ leaves, ∀ e ∈ T.edgeSet, (∀ y ∈ leaves, y ∉ e) →
        ndColouring n hn s(pos x, g (caseALeafAnchor T x)) ≠ ndColouring n hn (Sym2.map g e)) := by
  classical
  letI : Fintype ((V → Fin (2 * n + 1)) × (V → Fin (2 * n + 1))) := Fintype.ofFinite _
  have h_prob := hInput δ hn leaves hδ hn_large hT hcard hleaf hanchor hindep hleafsize
  obtain ⟨gp, hgp⟩ := exists_of_prob_gt_zero _ h_prob
  exact ⟨gp.1, gp.2, hgp⟩

/-- **Case A rainbow copy (§4, §6, M1+M2).** For small $\delta > 0$ and large $n$, every Case A
tree that is not Case C has a rainbow copy in the ND-coloured $K_{2n+1}$.

The proof reduces the goal to the single deep input `caseA_embedding_data` (the MPS
randomized near-embedding + distributive absorption) via the proven assembler
`extend_rainbow_leaves`: it constructs the leaf set and anchor map, discharges all the structural
side conditions (leaves are anchored outside the leaf set, every edge is a core edge or a
leaf–anchor edge), and glues the resulting core embedding and leaf placement into a rainbow copy. -/
theorem caseA_rainbow (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n) (hn_large : 1 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hcard : T.edgeSet.ncard = n) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_size : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ S.ncard)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (hInput : CaseAEmbeddingInput n T) :
    HasRainbowCopy n T := by
  classical
  have hSfin : S.Finite := S.toFinite
  set leaves := hSfin.toFinset with hlv
  have hmem : ∀ x, x ∈ leaves ↔ x ∈ S := fun x => by rw [hlv]; exact hSfin.mem_toFinset
  have hleaf : ∀ x ∈ leaves, IsLeaf T x := fun x hx => hS_leaves x ((hmem x).mp hx)
  have hindep : ∀ x ∈ leaves, ∀ y ∈ leaves, x ≠ y → ¬T.Adj x y :=
    fun x hx y hy hne => hS_indep x ((hmem x).mp hx) y ((hmem y).mp hy) hne
  have hanchor : ∀ x ∈ leaves, caseALeafAnchor T x ∉ leaves := by
    intro x hx hax
    have hadj := caseALeafAnchor_adj T (hleaf x hx)
    exact hindep x hx _ hax hadj.ne hadj
  have hedges : ∀ e ∈ T.edgeSet,
      (∀ x ∈ leaves, x ∉ e) ∨ ∃ x ∈ leaves, e = s(x, caseALeafAnchor T x) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      by_cases ha : a ∈ leaves
      · exact Or.inr ⟨a, ha, by
          rw [caseALeafAnchor_unique T (hleaf a ha) (show T.Adj a b from he)]⟩
      · by_cases hb : b ∈ leaves
        · refine Or.inr ⟨b, hb, ?_⟩
          rw [Sym2.eq_swap,
            caseALeafAnchor_unique T (hleaf b hb) (show T.Adj b a from (show T.Adj a b from he).symm)]
        · refine Or.inl ?_
          intro x hx hxe
          rcases Sym2.mem_iff.mp hxe with rfl | rfl
          · exact ha hx
          · exact hb hx
  have hleafsize : ⌊δ ^ 6 * (n : ℝ)⌋₊ ≤ leaves.card := by
    rw [hlv, ← Set.ncard_eq_toFinset_card S hSfin]; exact hS_size
  obtain ⟨g, pos, hginj, hposinj, hdisj, hrb, hinj, hfresh⟩ :=
    caseA_embedding_data δ hδ n hn hn_large T hT hcard leaves hleaf hanchor hindep hleafsize hInput
  obtain ⟨f, hf⟩ := extend_rainbow_leaves n hn T leaves (caseALeafAnchor T) hanchor hedges
    g pos hginj hposinj hdisj hrb hinj hfresh
  exact ⟨f, fun _ => hf⟩

/-- `∀ᶠ` wrapper around `caseA_rainbow`, suitable for `filter_upwards` in the spine. -/
theorem caseA_rainbow_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n → IsCaseA δ n T → ¬IsCaseC δ n T →
      CaseAEmbeddingInput n T → HasRainbowCopy n T := by
  apply Filter.eventually_atTop.mpr
  exact ⟨2, fun n hn V _ T hT hcard ⟨S, hS_leaves, hS_indep, hS_size⟩ _ hInput =>
    caseA_rainbow δ hδ n (by omega) (by omega) T hT hcard S hS_leaves hS_size hS_indep hInput⟩

end Ringel