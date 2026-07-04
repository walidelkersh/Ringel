import Ringel.Statement
import Ringel.Primitives
import Ringel.ProbBounds
import Ringel.CaseA
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Filter.Basic

namespace Ringel

lemma caseB_embedding_exists (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn_pos : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hn : T.edgeSet.ncard = n) (hB : IsCaseB δ n T) (hC : ¬IsCaseC δ n T) : HasRainbowCopy n T := by
  obtain ⟨paths, h_bare, h_len, h_disj, _⟩ := hB
  sorry

lemma caseB_rainbow_large_n (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseB δ n T → ¬IsCaseC δ n T → HasRainbowCopy n T := by
  use 1
  intro n hn V _ T hT hcard hB hC
  have hn_pos : 0 < n := by omega
  exact caseB_embedding_exists δ hδ n hn_pos T hT hcard hB hC

/-- **Case B rainbow copy (§5, §6, M1+M2).** For small δ > 0 and large n, every Case B
tree that is not Case C has a rainbow copy in the ND-coloured K_{2n+1}. -/
theorem caseB_rainbow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseB δ n T → ¬IsCaseC δ n T → HasRainbowCopy n T := by
  obtain ⟨N, hN⟩ := caseB_rainbow_large_n δ hδ
  exact Filter.eventually_atTop.mpr ⟨N, hN⟩

end Ringel
