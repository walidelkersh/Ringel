import Ringel.Statement

/-!
# Challenge surface for Ringel's conjecture

This file isolates the audited main statement behind a stable name.
It imports the formal theorem and re-exports the exact target without
adding hypotheses, helper lemmas, or proof scaffolding.
-/

namespace Ringel

/-- Audit target: the large-`n` form of Ringel's conjecture. -/
theorem challenge_ringel_conjecture_large :
    CaseABSourceStatement →
      ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
        T.IsTree → T.edgeSet.ncard = n →
        ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
          Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
          ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  simpa using ringel_conjecture_large

end Ringel
