import Ringel.NearEmbedding

/-!
# Small trees with a replete subset (MPS §6)

This module is the finite, joint-object layer for `Lemma_embedding_small_tree`.  It separates the
finite deterministic construction from the two concentration estimates used in the paper.  In
particular, an outcome retains the embedding, its two available sets, and the independently sampled
leftovers on one probability space.
-/

open scoped BigOperators
open SimpleGraph
open Classical

namespace Ringel

namespace FiniteProbabilityLaw

/-- Complement rule for the transparent finite law. -/
lemma prob_add_prob_compl {Ω : Type*} [Fintype Ω]
    (P : FiniteProbabilityLaw Ω) (A : Set Ω) : P.prob A + P.prob Aᶜ = 1 := by
  rw [prob, prob]
  simp only [Set.mem_compl_iff]
  rw [Finset.sum_filter_add_sum_filter_not]
  exact P.sum_mass

end FiniteProbabilityLaw

/-- One finite outcome of the small-tree construction.  Unlike a bare mapped graph, this records
that the vertex map is an embedding and that its image is rainbow. -/
structure SmallTreeEmbeddingOutcome (n : ℕ) (hn : 0 < n) {V : Type*} (T : SimpleGraph V) where
  f : V ↪ Fin (2 * n + 1)
  availableVertices : Set (Fin (2 * n + 1))
  availableColours : Set (Fin n)
  V0 : Set (Fin (2 * n + 1))
  C0 : Set (Fin n)
  vertices_available : Set.range f ⊆ availableVertices
  colours_available : ndColouring n hn '' ((T.map f).edgeSet) ⊆ availableColours
  rainbow : Set.InjOn (ndColouring n hn) ((T.map f).edgeSet)
  V0_avoids_image : V0 ⊆ (Set.range f)ᶜ
  C0_avoids_colours : C0 ⊆ (ndColouring n hn '' ((T.map f).edgeSet))ᶜ

/-- Forgetting the extra correctness witnesses gives the existing §6 joint embedding interface. -/
noncomputable def SmallTreeEmbeddingOutcome.toRandomizedRainbowEmbedding
    {Ω : Type*} {n : ℕ} {V : Type*} (hn : 0 < n) (T : SimpleGraph V)
    (out : Ω → SmallTreeEmbeddingOutcome n hn T) : RandomizedRainbowEmbedding Ω n V where
  hn := hn
  sourceGraph := T
  reservedVertices := fun ω => (out ω).availableVertices
  reservedColours := fun ω => (out ω).availableColours
  graph := fun ω => T.map (out ω).f
  vertexMap := fun ω => out ω |>.f
  graph_eq := fun _ => rfl
  vertices_reserved := fun ω => (out ω).vertices_available
  colours_reserved := fun ω => (out ω).colours_available

/-- The exact finite conclusion supplied by the small-tree stage.  `failure` is the finite version
of “with high probability”; the two leftovers are kept as joint random variables and are explicitly
independent. -/
def SmallTreeEmbeddingConclusion (n : ℕ) (hn : 0 < n) {V : Type*} [Fintype V]
    (T : SimpleGraph V) (U : Set V) (q failure : ℝ) (r : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (P : FiniteProbabilityLaw Ω)
      (out : Ω → SmallTreeEmbeddingOutcome n hn T),
    IsQRandomSet P q (fun ω => (out ω).availableVertices) ∧
    IsQRandomSet P q (fun ω => (out ω).availableColours) ∧
    IsQRandomSet P (q / 2) (fun ω => (out ω).V0) ∧
    IsQRandomSet P (q / 2) (fun ω => (out ω).C0) ∧
    P.Independent (fun ω => (out ω).V0) (fun ω => (out ω).C0) ∧
    1 - failure ≤ P.prob {ω |
      ColourPairReplete n hn ((out ω).f '' U) (out ω).V0 r}

/-- A finite growth order is the exact combinatorial datum used by the paper's greedy sentence:
every vertex after the root has one earlier neighbour.  Requiring uniqueness makes all mapped
edges appear at their unique insertion step. -/
structure TreeGrowthOrder {V : Type*} [Fintype V] (T : SimpleGraph V) where
  order : List V
  nodup : order.Nodup
  complete : ∀ v, v ∈ order
  root : V
  head_eq : order.head? = some root
  parent : V → V
  parent_earlier : ∀ v, v ≠ root →
    ∃ before after, order = before ++ v :: after ∧ parent v ∈ before ∧ T.Adj (parent v) v
  unique_earlier : ∀ v, v ≠ root → ∀ w before after,
    order = before ++ v :: after → w ∈ before → T.Adj w v → w = parent v

/-- Candidate vertices for one greedy insertion step. -/
def greedyCandidates (n : ℕ) (hn : 0 < n) {V : Type*}
    (availableV : Set (Fin (2 * n + 1))) (availableC : Set (Fin n))
    (f : V → Fin (2 * n + 1)) (parent : V) : Set (Fin (2 * n + 1)) :=
  {x | x ∈ availableV ∧ x ≠ f parent ∧
    ndColouring n hn s(f parent, x) ∈ availableC}

/-- The local greedy extension step.  A candidate outside the used image and whose edge colour is
fresh extends injectivity and rainbow distinctness. -/
lemma greedy_extend_one
    (n : ℕ) (hn : 0 < n) {V : Type*} (parent child : V)
    (f : V → Fin (2 * n + 1)) (S : Set V)
    (hchild : child ∉ S) (hparent : parent ∈ S)
    (hinj : Set.InjOn f S)
    (usedColours : Set (Fin n)) (x : Fin (2 * n + 1))
    (hx : x ∉ f '' S)
    (hcolour : ndColouring n hn s(f parent, x) ∉ usedColours) :
    Set.InjOn (Function.update f child x) (insert child S) ∧
    ndColouring n hn s((Function.update f child x) parent,
      (Function.update f child x) child) ∉ usedColours := by
  have hpc : parent ≠ child := fun h => hchild (h ▸ hparent)
  constructor
  · intro a ha b hb hab
    by_cases hac : a = child
    · subst a
      by_cases hbc : b = child
      · exact hbc.symm
      · have hbS : b ∈ S := hb.resolve_left hbc
        simp only [Function.update_self, Function.update_of_ne hbc] at hab
        exact (hx ⟨b, hbS, hab.symm⟩).elim
    · have haS : a ∈ S := ha.resolve_left hac
      by_cases hbc : b = child
      · subst b
        simp only [Function.update_of_ne hac, Function.update_self] at hab
        exact (hx ⟨a, haS, hab⟩).elim
      · have hbS : b ∈ S := hb.resolve_left hbc
        rw [Function.update_of_ne hac, Function.update_of_ne hbc] at hab
        exact hinj haS hbS hab
  · simpa [Function.update_of_ne hpc, Function.update_self] using hcolour

/-- Repletion survives restriction of the right-hand set whenever each colour retains `r` crossing
edges.  This is the deterministic final transfer used after random thinning. -/
lemma colourPairReplete_of_retained
    {n r : ℕ} (hn : 0 < n) (U B B0 : Set (Fin (2 * n + 1)))
    (hretain : ∀ c : Fin n,
      r ≤ (colourCrossEdges n hn U B c ∩ colourCrossEdges n hn U B0 c).ncard) :
    ColourPairReplete n hn U B0 r := by
  intro c
  apply le_trans (hretain c)
  apply Set.ncard_le_ncard
  · exact Set.inter_subset_right
  · exact Set.toFinite _

/-- Removing an occupied set loses at most the crossing edges entering that set.  This is the
paper's deterministic `0.9 |U|` calculation, stated without asymptotic rounding. -/
lemma colourPairReplete_compl_of_bad_bound
    {n total bad : ℕ} (hn : 0 < n) (U occupied : Set (Fin (2 * n + 1)))
    (htotal : ColourPairReplete n hn U Set.univ total)
    (hbad : ∀ c : Fin n, (colourCrossEdges n hn U occupied c).ncard ≤ bad) :
    ColourPairReplete n hn U occupiedᶜ (total - bad) := by
  intro c
  have hsub : colourCrossEdges n hn U Set.univ c ⊆
      colourCrossEdges n hn U occupied c ∪ colourCrossEdges n hn U occupiedᶜ c := by
    intro e he
    rcases he with ⟨hdiag, hcol, x, hxU, y, hy, rfl⟩
    by_cases hyocc : y ∈ occupied
    · exact Or.inl ⟨hdiag, hcol, x, hxU, y, hyocc, rfl⟩
    · exact Or.inr ⟨hdiag, hcol, x, hxU, y, hyocc, rfl⟩
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hunion := Set.ncard_union_le
      (colourCrossEdges n hn U occupied c) (colourCrossEdges n hn U occupiedᶜ c)
  have ht := htotal c
  have hb := hbad c
  omega

/-- Deterministic assembly of the paper's greedy stage.  Once the successive candidate choices
have produced an injective map whose vertices and edge colours lie in the available reservoirs,
and freshness has established the rainbow clause, all deterministic outcome fields—including
avoidance by the two leftovers—are packaged without any probabilistic assumption. -/
lemma exists_smallTreeEmbeddingOutcome_of_greedy
    {n : ℕ} (hn : 0 < n) {V : Type*} (T : SimpleGraph V)
    (f : V ↪ Fin (2 * n + 1))
    (availableV : Set (Fin (2 * n + 1))) (availableC : Set (Fin n))
    (V0 : Set (Fin (2 * n + 1))) (C0 : Set (Fin n))
    (hvertices : Set.range f ⊆ availableV)
    (hcolours : ndColouring n hn '' (T.map f).edgeSet ⊆ availableC)
    (hrainbow : Set.InjOn (ndColouring n hn) (T.map f).edgeSet)
    (hV0 : V0 ⊆ (Set.range f)ᶜ)
    (hC0 : C0 ⊆ (ndColouring n hn '' (T.map f).edgeSet)ᶜ) :
    ∃ o : SmallTreeEmbeddingOutcome n hn T,
      o.f = f ∧ o.availableVertices = availableV ∧ o.availableColours = availableC ∧
      o.V0 = V0 ∧ o.C0 = C0 := by
  refine ⟨{
    f := f
    availableVertices := availableV
    availableColours := availableC
    V0 := V0
    C0 := C0
    vertices_available := hvertices
    colours_available := hcolours
    rainbow := hrainbow
    V0_avoids_image := hV0
    C0_avoids_colours := hC0 }, rfl, rfl, rfl, rfl, rfl⟩

/-- A positive finite success bound yields one concrete rainbow embedding with the required
repletion. -/
lemma SmallTreeEmbeddingConclusion.exists_replete
    {n : ℕ} (hn : 0 < n) {V : Type*} [Fintype V]
    {T : SimpleGraph V} {U : Set V} {q failure : ℝ} {r : ℕ}
    (hfailure : failure < 1)
    (h : SmallTreeEmbeddingConclusion n hn T U q failure r) :
    ∃ o : SmallTreeEmbeddingOutcome n hn T,
      ColourPairReplete n hn (o.f '' U) o.V0 r := by
  rcases h with ⟨Ω, iΩ, P, out, _, _, _, _, _, hgood⟩
  letI : Fintype Ω := iΩ
  have hp : 0 < P.prob {ω | ColourPairReplete n hn ((out ω).f '' U) (out ω).V0 r} :=
    lt_of_lt_of_le (sub_pos.mpr hfailure) hgood
  obtain ⟨ω, hω⟩ := P.exists_mem_of_prob_pos _ hp
  exact ⟨out ω, hω⟩

end Ringel
