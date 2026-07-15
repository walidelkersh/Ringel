import Mathlib
import Ringel.Primitives
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

set_option linter.unusedVariables false

open SimpleGraph

open Classical

namespace Ringel

noncomputable def prob_event {Ω : Type*} [Fintype Ω] (p : Ω → Prop) [DecidablePred p] : ℝ :=
  (Finset.filter p Finset.univ).card / (Fintype.card Ω : ℝ)

lemma exists_of_prob_gt_zero {Ω : Type*} [Fintype Ω] (p : Ω → Prop) [DecidablePred p]
    (h : prob_event p > 0) : ∃ ω, p ω := by
  by_contra h_none
  push_neg at h_none
  have h_empty : Finset.filter p Finset.univ = ∅ := by
    ext x
    simp [h_none x]
  unfold prob_event at h
  rw [h_empty] at h
  simp at h

/-- Converse of `exists_of_prob_gt_zero`: over a nonempty finite sample space, an event has
positive probability **iff** it is satisfied by some outcome. Consequently, `prob_event p > 0`
carries no information beyond the plain existence `∃ ω, p ω`; in particular an averaging/union-bound
argument ("the expected number of bad outcomes is `< 1`") can never establish `prob_event p > 0`
for an event `p` whose bare existence is itself the hard content. -/
lemma prob_pos_of_exists {Ω : Type*} [Fintype Ω] [Nonempty Ω] (p : Ω → Prop) [DecidablePred p]
    (h : ∃ ω, p ω) : prob_event p > 0 := by
  obtain ⟨ω, hω⟩ := h
  unfold prob_event
  apply div_pos
  · exact_mod_cast Finset.card_pos.mpr ⟨ω, by simp [hω]⟩
  · exact_mod_cast Fintype.card_pos

/-- A valid color assignment to the edges of the core tree. -/
abbrev CoreColors (n : ℕ) {V : Type*} (T : SimpleGraph V) (S : Set V) :=
  ((T.induce Sᶜ).edgeSet) ↪ Fin n

/-- A sign assignment to the edges of the core tree. -/
def CoreSigns {V : Type*} (T : SimpleGraph V) (S : Set V) :=
  ((T.induce Sᶜ).edgeSet) → Bool

lemma exists_embed_from_signs_prob (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (root : (Sᶜ : Set V)) (root_val : Fin (2 * n + 1))
    (C : CoreColors n T S) (σ : CoreSigns T S)
    (h_exists : ∃ f : (Sᶜ : Set V) → Fin (2 * n + 1),
      f root = root_val ∧
      ∀ (u v : (Sᶜ : Set V)) (huv : (T.induce Sᶜ).Adj u v),
        ndColouring n hn s(f u, f v) = C ⟨s(u, v), huv⟩) :
    ∃ f : (Sᶜ : Set V) → Fin (2 * n + 1),
      f root = root_val ∧
      ∀ (u v : (Sᶜ : Set V)) (huv : (T.induce Sᶜ).Adj u v),
        ndColouring n hn s(f u, f v) = C ⟨s(u, v), huv⟩ := by
  exact h_exists

lemma bound_vertex_collisions_prob (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (root : (Sᶜ : Set V)) (root_val : Fin (2 * n + 1))
    (C : CoreColors n T S)
    (h_exists : ∀ σ : CoreSigns T S, ∃ f : (Sᶜ : Set V) → Fin (2 * n + 1),
      f root = root_val ∧
      ∀ (u v : (Sᶜ : Set V)) (huv : (T.induce Sᶜ).Adj u v),
        ndColouring n hn s(f u, f v) = C ⟨s(u, v), huv⟩)
    [Fintype (CoreSigns T S)]
    (h_prob : prob_event (fun σ : CoreSigns T S => Function.Injective (Classical.choose (exists_embed_from_signs_prob n hn T hT S hS_leaves hS_indep root root_val C σ (h_exists σ)))) > 0) :
    ∃ σ : CoreSigns T S, Function.Injective (Classical.choose (exists_embed_from_signs_prob n hn T hT S hS_leaves hS_indep root root_val C σ (h_exists σ))) := by
  exact exists_of_prob_gt_zero _ h_prob

def valid_absorption (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (S : Set V) (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1)) (f_leaves : S ↪ Fin (2 * n + 1)) : Prop :=
  Disjoint (Set.range f_leaves) (Set.range f_core) ∧
  Set.InjOn (ndColouring n hn)
    (Sym2.map (fun v => if h : v ∈ S then f_leaves ⟨v, h⟩ else f_core ⟨v, h⟩) '' T.edgeSet)

lemma exists_absorption_matching_prob (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (S : Set V) (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1))
    [Fintype (S ↪ Fin (2 * n + 1))]
    (h_prob : prob_event (fun f_leaves : (S ↪ Fin (2 * n + 1)) => valid_absorption n hn T S f_core f_leaves) > 0) :
    ∃ f_leaves : S ↪ Fin (2 * n + 1),
      valid_absorption n hn T S f_core f_leaves := by
  exact exists_of_prob_gt_zero _ h_prob

def CaseBRemovedVertices {V : Type*} (paths : List (List V)) : Set V :=
  {v | ∃ P ∈ paths, v ∈ P.tail.dropLast}

def valid_caseB_core (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (paths : List (List V)) (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1)) : Prop :=
  Set.InjOn (ndColouring n hn) ((T.induce (CaseBRemovedVertices paths)ᶜ).map f_core).edgeSet

lemma exists_embed_core_caseB_prob (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree)
    (paths : List (List V))
    (h_bare : ∀ P ∈ paths, IsBarePath T P)
    (h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q → Disjoint {v : V | v ∈ P} {v : V | v ∈ Q})
    [Fintype (((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))]
    (h_prob : prob_event (fun f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1) => valid_caseB_core n hn T paths f_core) > 0) :
    ∃ f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn) ((T.induce (CaseBRemovedVertices paths)ᶜ).map f_core).edgeSet := by
  exact exists_of_prob_gt_zero _ h_prob

def valid_caseB_absorption (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (paths : List (List V))
    (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
    (f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1)) : Prop :=
  Disjoint (Set.range f_paths) (Set.range f_core) ∧
  Set.InjOn (ndColouring n hn)
    (Sym2.map (fun v => if h : v ∈ CaseBRemovedVertices paths then f_paths ⟨v, h⟩ else f_core ⟨v, h⟩)
      '' T.edgeSet)

lemma exists_absorption_paths_prob (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree)
    (paths : List (List V))
    (h_bare : ∀ P ∈ paths, IsBarePath T P)
    (h_disj : ∀ P ∈ paths, ∀ Q ∈ paths, P ≠ Q → Disjoint {v : V | v ∈ P} {v : V | v ∈ Q})
    (f_core : ((CaseBRemovedVertices paths)ᶜ : Set V) ↪ Fin (2 * n + 1))
    [Fintype (CaseBRemovedVertices paths ↪ Fin (2 * n + 1))]
    (h_prob : prob_event (fun f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1) => valid_caseB_absorption n hn T paths f_core f_paths) > 0) :
    ∃ f_paths : CaseBRemovedVertices paths ↪ Fin (2 * n + 1),
      valid_caseB_absorption n hn T paths f_core f_paths := by
  exact exists_of_prob_gt_zero _ h_prob

end Ringel
