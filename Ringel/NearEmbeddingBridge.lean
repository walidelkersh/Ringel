import Ringel.NearEmbedding

/-!
# Bridges from the joint near-embedding layer to Cases A and B

These generic lemmas replace the core-embedding portions of the old Case A/B inputs without
importing the case files (whose CI repair is owned separately).  Instantiate `removed` with the
leaf set in Case A or with the union of bare-path interiors in Case B.  They do not claim to replace
either finishing/absorption portion.
-/

namespace Ringel

open SimpleGraph

/-- The near-embedding conclusion supplies a rainbow embedding of an induced core. -/
lemma induced_core_from_nearEmbedding
    {n : ℕ} (hn : 0 < n) {V : Type*} [Fintype V]
    (T : SimpleGraph V) (removed : Set V) (U : Set (removedᶜ : Set V))
    [Fintype (removedᶜ : Set V)] {ξ μ η failure : ℝ} {epsCount pCount : ℕ} (hfailure : failure < 1)
    (hnear : NearEmbeddingConclusion n hn (T.induce removedᶜ) U ξ μ η failure epsCount pCount) :
    ∃ f : (removedᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn) ((T.induce removedᶜ).map f).edgeSet :=
  hnear.exists_rainbow_core hn hfailure

/-- In particular, the joint layer proves the old Case B Phase-1 shape once `removed` is chosen as
all bare-path interiors.  The §5 fixed-endpoint path finishing lemma is still the exact missing
Phase 2. -/
lemma path_deleted_core_from_nearEmbedding
    {n : ℕ} (hn : 0 < n) {V : Type*} [Fintype V]
    (T : SimpleGraph V) (paths : List (List V))
    (U : Set ({v | ∃ P ∈ paths, v ∈ P.tail.dropLast}ᶜ : Set V))
    [Fintype ({v | ∃ P ∈ paths, v ∈ P.tail.dropLast}ᶜ : Set V)]
    {ξ μ η failure : ℝ} {epsCount pCount : ℕ} (hfailure : failure < 1)
    (hnear : NearEmbeddingConclusion n hn
      (T.induce {v | ∃ P ∈ paths, v ∈ P.tail.dropLast}ᶜ) U ξ μ η failure epsCount pCount) :
    ∃ f_core : ({v | ∃ P ∈ paths, v ∈ P.tail.dropLast}ᶜ : Set V) ↪ Fin (2 * n + 1),
      Set.InjOn (ndColouring n hn)
        ((T.induce {v | ∃ P ∈ paths, v ∈ P.tail.dropLast}ᶜ).map f_core).edgeSet :=
  hnear.exists_rainbow_core hn hfailure

end Ringel
