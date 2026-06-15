import Mathlib
import Ringel.Primitives

namespace Ringel

/-- **Lemma `Lemma_case_division` (§2).** For small $\delta > 0$ and large $n$, every $n$-edge tree
is in Case A, Case B, or Case C (cases need not be disjoint). -/
lemma tree_split (δ : ℝ) (hδ : 0 < δ) (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V)
  (hTree : T.IsTree) (hn : T.edgeSet.ncard = n) :
  IsCaseA δ n T ∨ IsCaseB δ n T ∨ IsCaseC δ n T := sorry

theorem case_division (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseA δ n T ∨ IsCaseB δ n T ∨ IsCaseC δ n T := by
  filter_upwards
  intro n V _ T hT hn
  exact tree_split δ hδ n T hT hn

end Ringel
