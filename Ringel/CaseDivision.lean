import Mathlib
import Ringel.Primitives
import Ringel.TreeStructure

namespace Ringel

/-- **Lemma `Lemma_case_division` (§2).** For `0 < δ ≤ 1/4` and any `n`, every `n`-edge tree is in
Case A, Case B, or Case C. Proved via the geometric `split` lemma (`TreeStructure.tree_split_via_split`):
applying `split` with `k = ⌊δ⁻¹⌋ ≥ 4`, the leaf branch yields Case A and the bare-path branch yields
Case B. (The small-δ hypothesis is necessary: for large δ the trichotomy is false — a path graph
satisfies none of the three cases.) -/
lemma tree_split (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) (n : ℕ) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hTree : T.IsTree) (hn : T.edgeSet.ncard = n) :
    IsCaseA δ n T ∨ IsCaseB δ n T ∨ IsCaseC δ n T :=
  TreeStructure.tree_split_via_split δ hδ hδ' n T hTree hn

theorem case_division (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseA δ n T ∨ IsCaseB δ n T ∨ IsCaseC δ n T := by
  filter_upwards
  intro n V _ T hT hn
  exact tree_split δ hδ hδ' n T hT hn

end Ringel
