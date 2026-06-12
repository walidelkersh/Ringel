import Ringel.Statement
import Ringel.Primitives
import Mathlib.Data.Set.Card.Arithmetic

namespace Ringel

/-- **Case B rainbow copy (§5, §6, M1+M2).** For small `δ > 0` and large `n`, every Case B
tree that is not Case C has a rainbow copy in the ND-coloured `K_{2n+1}`. -/
theorem caseB_rainbow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseB δ n T → ¬IsCaseC δ n T → HasRainbowCopy n T := by
  sorry

end Ringel
