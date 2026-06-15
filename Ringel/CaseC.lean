import Ringel.Statement
import Ringel.Primitives
import Mathlib.Data.Set.Card.Arithmetic

namespace Ringel

lemma caseC_decompose (δ : ℝ) (n : ℕ) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hC : IsCaseC δ n T) :
    ∃ (T_core : SimpleGraph V) (leaves : Set V),
      T_core ≤ T ∧
      (∀ v ∈ leaves, IsLeaf T v) ∧
      (T_core.edgeSet.ncard ≤ n / 100) ∧
      (T_core.edgeSet ∪ {e ∈ T.edgeSet | ∃ v ∈ leaves, v ∈ e}) = T.edgeSet := by
  sorry

lemma caseC_embed_core (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T_core : SimpleGraph V)
    (h_small : T_core.edgeSet.ncard ≤ n / 100) :
    ∃ f_core : V ↪ Fin (2 * n + 1), Set.InjOn (ndColouring n hn) (T_core.map f_core).edgeSet := by
  sorry

lemma caseC_extend_embedding (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V) (T_core : SimpleGraph V) (leaves : Set V)
    (h_decomp1 : T_core ≤ T) (h_decomp2 : ∀ v ∈ leaves, IsLeaf T v)
    (h_decomp3 : T_core.edgeSet ∪ {e ∈ T.edgeSet | ∃ v ∈ leaves, v ∈ e} = T.edgeSet)
    (f_core : V ↪ Fin (2 * n + 1)) (h_core_inj : Set.InjOn (ndColouring n hn) (T_core.map f_core).edgeSet) :
    ∃ f : V ↪ Fin (2 * n + 1), Set.InjOn (ndColouring n hn) (T.map f).edgeSet := by
  sorry

lemma caseC_embedding_exists (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn_pos : 0 < n) {V : Type*} [Finite V] (T : SimpleGraph V)
    (hT : T.IsTree) (hn : T.edgeSet.ncard = n) (hC : IsCaseC δ n T) : HasRainbowCopy n T := by
  have ⟨T_core, leaves, h_decomp1, h_decomp2, h_small, h_decomp3⟩ := caseC_decompose δ n T hT hC
  have ⟨f_core, h_core_inj⟩ := caseC_embed_core n hn_pos T_core h_small
  have ⟨f, hf_inj⟩ := caseC_extend_embedding n hn_pos T T_core leaves h_decomp1 h_decomp2 h_decomp3 f_core h_core_inj
  exact ⟨f, fun _ => hf_inj⟩

/-- **Case C rainbow copy (§6–§7, M3, deterministic).** For small $\delta > 0$ and large $n$,
every Case C tree has a rainbow copy in the ND-coloured $K_{2n+1}$. -/
theorem caseC_rainbow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      IsCaseC δ n T → HasRainbowCopy n T := by
  apply Filter.eventually_atTop.2
  use 1
  intro n hn_large V _ T hT hn hC
  have hn_pos : 0 < n := by omega
  exact caseC_embedding_exists δ hδ n hn_pos T hT hn hC

end Ringel
