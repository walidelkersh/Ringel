import Ringel.Statement
import Ringel.Primitives
import Mathlib.Data.Set.Card.Arithmetic

namespace Ringel

/-- **Lemma `Lemma_case_division` (§2).** For small `δ > 0` and large `n`, every `n`-edge tree
is in Case A, Case B, or Case C (cases need not be disjoint). -/
theorem case_division (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseA δ n T ∨ IsCaseB δ n T ∨ IsCaseC δ n T := by
  sorry

end Ringel
