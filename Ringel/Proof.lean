import Ringel.CaseSource

namespace Ringel

/--
**Ringel's Conjecture for large $n$ (Montgomery–Pokrovskiy–Sudakov, 2020).**
This wrapper now runs through the source package rather than the older conditional inputs.
-/
theorem ringel_conjecture_large_proof :
    CaseABSourceStatement →
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
        T.IsTree → T.edgeSet.ncard = n →
        ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
          Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
          ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  exact ringel_conjecture_large_via_source

end Ringel
