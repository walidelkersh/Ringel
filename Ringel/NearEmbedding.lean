import Mathlib
import Ringel.Primitives

/-!
# The joint random near-embedding object

This file formalizes the first, paper-faithful interface of MPS, `section2.tex`,
Theorem `nearembedagain`, together with the deterministic extension language used in
`section6.tex`.  It deliberately does not identify “random” with positive probability on an
arbitrary function space: a finite probability law and the complete joint random object are part
of the data.
-/

open scoped BigOperators
open SimpleGraph
open Classical

namespace Ringel

/-- A transparent finite probability law.  No full-support assumption is made. -/
structure FiniteProbabilityLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  sum_mass : ∑ ω, mass ω = 1

namespace FiniteProbabilityLaw

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event under a finite law. -/
noncomputable def prob (P : FiniteProbabilityLaw Ω) (A : Set Ω) : ℝ :=
  ∑ ω with ω ∈ A, P.mass ω

@[simp] lemma prob_univ (P : FiniteProbabilityLaw Ω) : P.prob Set.univ = 1 := by
  simp [prob, P.sum_mass]

lemma prob_nonneg (P : FiniteProbabilityLaw Ω) (A : Set Ω) : 0 ≤ P.prob A := by
  exact Finset.sum_nonneg fun i _ => P.mass_nonneg i

lemma prob_mono (P : FiniteProbabilityLaw Ω) {A B : Set Ω} (h : A ⊆ B) :
    P.prob A ≤ P.prob B := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    have hxA : x ∈ A := by simpa using hx
    simpa using h hxA
  · exact fun _ _ _ => P.mass_nonneg _

lemma exists_mem_of_prob_pos (P : FiniteProbabilityLaw Ω) (A : Set Ω)
    (hA : 0 < P.prob A) : ∃ ω, ω ∈ A := by
  by_contra h
  have hn : ∀ ω, ω ∉ A := by simpa only [not_exists] using h
  have hsub : A ⊆ ∅ := fun x hx => (hn x hx).elim
  have : A = ∅ := Set.Subset.antisymm hsub (Set.empty_subset A)
  simp [this, prob] at hA

/-- Two random variables are independent, stated by factorization on all point events.
For finite codomains this is equivalent to the usual event-level definition. -/
def Independent {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteProbabilityLaw Ω) (X : Ω → α) (Y : Ω → β) : Prop :=
  ∀ x y, P.prob {ω | X ω = x ∧ Y ω = y} =
    P.prob {ω | X ω = x} * P.prob {ω | Y ω = y}

lemma Independent.symm {α β : Type*} [Fintype α] [Fintype β]
    (P : FiniteProbabilityLaw Ω) {X : Ω → α} {Y : Ω → β}
    (h : P.Independent X Y) : P.Independent Y X := by
  intro y x
  simpa only [and_comm, mul_comm] using h x y

end FiniteProbabilityLaw

/-- Exact product-Bernoulli law for a random subset of a finite ground type.  This single formula
records both the marginal inclusion probability and mutual independence of all membership bits. -/
def IsQRandomSet {Ω α : Type*} [Fintype Ω] [Fintype α]
    (P : FiniteProbabilityLaw Ω) (q : ℝ) (X : Ω → Set α) : Prop :=
  ∀ A : Set α,
    P.prob {ω | X ω = A} =
      q ^ A.ncard * (1 - q) ^ ((Set.univ : Set α) \ A).ncard

/-- The edges of colour `c` crossing from `X` to `Y`. -/
def colourCrossEdges (n : ℕ) (hn : 0 < n) (X Y : Set (Fin (2 * n + 1))) (c : Fin n) :
    Set (Sym2 (Fin (2 * n + 1))) :=
  {e | ¬e.IsDiag ∧ ndColouring n hn e = c ∧
    ∃ x ∈ X, ∃ y ∈ Y, e = s(x, y)}

/-- Paper-faithful repletion: every colour has at least `r` crossing edges. -/
def ColourPairReplete (n : ℕ) (hn : 0 < n)
    (X Y : Set (Fin (2 * n + 1))) (r : ℕ) : Prop :=
  ∀ c : Fin n, r ≤ (colourCrossEdges n hn X Y c).ncard

/-- Vertices and colours exposed by one randomized rainbow embedding stage (§6). -/
structure RandomizedRainbowEmbedding (Ω : Type*) (n : ℕ) (V : Type*) where
  hn : 0 < n
  sourceGraph : SimpleGraph V
  reservedVertices : Ω → Set (Fin (2 * n + 1))
  reservedColours : Ω → Set (Fin n)
  graph : Ω → SimpleGraph (Fin (2 * n + 1))
  vertexMap : Ω → V → Fin (2 * n + 1)
  graph_eq : ∀ ω, graph ω = sourceGraph.map (vertexMap ω)
  vertices_reserved : ∀ ω, Set.range (vertexMap ω) ⊆ reservedVertices ω
  colours_reserved : ∀ ω,
    ndColouring n hn '' (graph ω).edgeSet ⊆ reservedColours ω

/-- Same-space extension from §6.  New embedded vertices and colours must come from the newly
reserved portions; this is stronger than mere monotonicity of the three fields. -/
def RandomizedRainbowEmbedding.Extends {Ω : Type*} {n : ℕ} {V₁ V₂ : Type*}
    (φ₂ : RandomizedRainbowEmbedding Ω n V₂)
    (φ₁ : RandomizedRainbowEmbedding Ω n V₁) : Prop :=
  ∀ ω,
    (φ₁.graph ω).edgeSet ⊆ (φ₂.graph ω).edgeSet ∧
    φ₁.reservedVertices ω ⊆ φ₂.reservedVertices ω ∧
    φ₁.reservedColours ω ⊆ φ₂.reservedColours ω ∧
    (Set.range (φ₂.vertexMap ω) \ Set.range (φ₁.vertexMap ω) ⊆
      φ₂.reservedVertices ω \ φ₁.reservedVertices ω) ∧
    (ndColouring n φ₂.hn '' ((φ₂.graph ω).edgeSet \ (φ₁.graph ω).edgeSet) ⊆
      φ₂.reservedColours ω \ φ₁.reservedColours ω)

lemma RandomizedRainbowEmbedding.Extends.trans
    {Ω : Type*} {n : ℕ} {V₁ V₂ V₃ : Type*}
    {φ₁ : RandomizedRainbowEmbedding Ω n V₁}
    {φ₂ : RandomizedRainbowEmbedding Ω n V₂}
    {φ₃ : RandomizedRainbowEmbedding Ω n V₃}
    (h₃₂ : φ₃.Extends φ₂) (h₂₁ : φ₂.Extends φ₁) : φ₃.Extends φ₁ := by
  intro ω
  rcases h₃₂ ω with ⟨he32, hv32, hc32, hnv32, hnc32⟩
  rcases h₂₁ ω with ⟨he21, hv21, hc21, hnv21, hnc21⟩
  refine ⟨he21.trans he32, hv21.trans hv32, hc21.trans hc32, ?_, ?_⟩
  · intro x hx
    by_cases hx2 : x ∈ Set.range (φ₂.vertexMap ω)
    · exact ⟨hv32 (hnv21 ⟨hx2, hx.2⟩).1, (hnv21 ⟨hx2, hx.2⟩).2⟩
    · refine ⟨(hnv32 ⟨hx.1, hx2⟩).1, ?_⟩
      intro hx1
      exact (hnv32 ⟨hx.1, hx2⟩).2 (hv21 hx1)
  · rintro c ⟨e, ⟨he3, he1⟩, rfl⟩
    by_cases he2 : e ∈ (φ₂.graph ω).edgeSet
    · have hc := hnc21 ⟨e, ⟨he2, he1⟩, rfl⟩
      exact ⟨hc32 hc.1, hc.2⟩
    · have hc := hnc32 ⟨e, ⟨he3, he2⟩, rfl⟩
      refine ⟨hc.1, ?_⟩
      intro hc1
      exact hc.2 (hc21 hc1)

/-- Leaves removed in the definition of the paper's parameter `p`: leaves adjacent to a vertex
having at least `k` leaf neighbours. -/
def heavyLeafRemoval {V : Type*} (T : SimpleGraph V) (k : ℕ) : Set V :=
  {x | IsLeaf T x ∧ ∃ v, T.Adj v x ∧
    k ≤ {y | T.Adj v y ∧ IsLeaf T y}.ncard}

/-- One outcome of the joint object in `nearembedagain`.  The four leftover sets and the copy of
`U` are retained jointly, rather than replaced by unrelated existential witnesses. -/
structure NearEmbeddingOutcome (n : ℕ) where
  hat : SimpleGraph (Fin (2 * n + 1))
  hatVertices : Set (Fin (2 * n + 1))
  W : Set (Fin (2 * n + 1))
  spareV : Set (Fin (2 * n + 1))
  V0 : Set (Fin (2 * n + 1))
  spareC : Set (Fin n)
  C0 : Set (Fin n)

/-- The deterministic “always” clauses of `nearembedagain`: all four leftover sets are disjoint
from the embedded object, and each pair is disjoint. -/
def NearEmbeddingOutcome.Leftover {n : ℕ} (hn : 0 < n)
    (o : NearEmbeddingOutcome n) : Prop :=
  Disjoint o.spareV o.V0 ∧ Disjoint o.spareC o.C0 ∧
  o.spareV ⊆ o.hatVerticesᶜ ∧ o.V0 ⊆ o.hatVerticesᶜ ∧
  o.spareC ⊆ (ndColouring n hn '' o.hat.edgeSet)ᶜ ∧
  o.C0 ⊆ (ndColouring n hn '' o.hat.edgeSet)ᶜ

/-- The high-probability event A1 in the paper. -/
def NearEmbeddingOutcome.Good {n : ℕ} (hn : 0 < n) {V : Type*}
    (T' : SimpleGraph V) (U : Set V) (ξ : ℝ) (o : NearEmbeddingOutcome n) : Prop :=
  ∃ f : V ↪ Fin (2 * n + 1),
    o.hat = T'.map f ∧ o.hatVertices = Set.range f ∧ o.W = f '' U ∧
    Set.InjOn (ndColouring n hn) o.hat.edgeSet ∧
    ColourPairReplete n hn o.W o.V0 ⌊ξ * n⌋₊

/-- Exact finite-`n` conclusion of `nearembedagain`.  A2 is represented by two exact Bernoulli
laws plus their joint independence; A3 gives the two stated marginal laws and intentionally does
not assert independence between them. -/
def NearEmbeddingConclusion (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V]
    (T' : SimpleGraph V) (U : Set V) (ξ μ η failure : ℝ) (epsCount pCount : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (P : FiniteProbabilityLaw Ω)
      (out : Ω → NearEmbeddingOutcome n),
    (∀ ω, (out ω).Leftover hn) ∧
    IsQRandomSet P μ (fun ω => (out ω).V0) ∧
    IsQRandomSet P μ (fun ω => (out ω).C0) ∧
    P.Independent (fun ω => (out ω).V0) (fun ω => (out ω).C0) ∧
    IsQRandomSet P (((pCount : ℝ) + epsCount) / (6 * n)) (fun ω => (out ω).spareV) ∧
    IsQRandomSet P ((1 - η) * epsCount / n) (fun ω => (out ω).spareC) ∧
    1 - failure ≤ P.prob {ω | (out ω).Good hn T' U ξ}

/-- Complete finite parameter hypotheses from the statement of `nearembedagain`, with integral
counts exposed instead of silently assuming that `εn` and `pn` are integers. -/
def NearEmbeddingInstance (n k epsCount pCount : ℕ) {V : Type*} [Fintype V]
    (T' : SimpleGraph V) (U : Set V) : Prop :=
  T'.IsAcyclic ∧ Fintype.card V = n - epsCount ∧ U.ncard = epsCount ∧
  ((Set.univ : Set V) \ heavyLeafRemoval T' k).ncard = pCount

/-- The exact remaining source theorem, in finite parameter form.  “`≪`” is intentionally not
replaced by arbitrary numerical inequalities: the paper's theorem asserts this conclusion in the
usual nested sufficiently-large/sufficiently-small hierarchy
`1/n ≪ ξ ≪ μ ≪ η ≪ ε ≪ 1` and `ξ ≪ 1/k ≪ 1/log n`.

This definition is a proposition to be proved by formalizing the construction lemmas of §6; it is
not postulated as an axiom and is not used below. -/
def NearEmbeddingSourceGoal : Prop :=
  ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
    ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioo 0 ε),
      ∀ᶠ μ : ℝ in nhdsWithin 0 (Set.Ioo 0 η),
        ∀ᶠ ξ : ℝ in nhdsWithin 0 (Set.Ioo 0 μ),
          ∀ τ : ℝ, 0 < τ →
          ∀ᶠ n : ℕ in Filter.atTop,
            (hn : 0 < n) → ∀ k epsCount pCount : ℕ, ∀ (V : Type) (_ : Fintype V),
              ∀ T' : SimpleGraph V, ∀ U : Set V,
                NearEmbeddingInstance n k epsCount pCount T' U →
                epsCount = ⌊ε * n⌋₊ →
                ξ < (k : ℝ)⁻¹ → (k : ℝ)⁻¹ < (Real.log n)⁻¹ →
                NearEmbeddingConclusion n hn T' U ξ μ η τ epsCount pCount

/-- A proved probabilistic-method consequence of the faithful joint layer. -/
lemma NearEmbeddingConclusion.exists_good
    {n : ℕ} (hn : 0 < n) {V : Type*} [Fintype V]
    {T' : SimpleGraph V} {U : Set V} {ξ μ η failure : ℝ} {epsCount pCount : ℕ}
    (hfailure : failure < 1)
    (h : NearEmbeddingConclusion n hn T' U ξ μ η failure epsCount pCount) :
    ∃ o : NearEmbeddingOutcome n, o.Good hn T' U ξ := by
  rcases h with ⟨Ω, iΩ, P, out, _, _, _, _, _, _, hgood⟩
  letI : Fintype Ω := iΩ
  have hp : 0 < P.prob {ω | (out ω).Good hn T' U ξ} := lt_of_lt_of_le (sub_pos.mpr hfailure) hgood
  obtain ⟨ω, hω⟩ := P.exists_mem_of_prob_pos _ hp
  exact ⟨out ω, hω⟩

/-- Concrete replacement for the *core near-embedding portion* of both old Case A/B inputs:
the joint theorem yields an actual rainbow embedding of `T'`, without placing a positive-
probability assumption on an arbitrary map space.  The finishing/absorption portions remain
separate. -/
lemma NearEmbeddingConclusion.exists_rainbow_core
    {n : ℕ} (hn : 0 < n) {V : Type*} [Fintype V]
    {T' : SimpleGraph V} {U : Set V} {ξ μ η failure : ℝ} {epsCount pCount : ℕ}
    (hfailure : failure < 1)
    (h : NearEmbeddingConclusion n hn T' U ξ μ η failure epsCount pCount) :
    ∃ f : V ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn) (T'.map f).edgeSet := by
  obtain ⟨o, f, hhat, _, _, hrainbow, _⟩ := h.exists_good hn hfailure
  exact ⟨f, by simpa [hhat] using hrainbow⟩

end Ringel
