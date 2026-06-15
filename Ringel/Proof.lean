import Ringel.Primitives
import Ringel.CaseDivision
import Ringel.CaseA
import Ringel.CaseB
import Ringel.CaseC

namespace Ringel

/--
**Ringel's Conjecture for large $n$ (Montgomery–Pokrovskiy–Sudakov, 2020).**
We prove this by picking a sufficiently small $\delta > 0$ and delegating to the case division lemma,
which shows that every tree falls into Case A, B, or C. In each case, a rainbow copy exists,
which analytically implies the full graph decomposition.
-/
theorem ringel_conjecture_large_proof (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (hn_pos : 0 < n) (hn_large : 1 < n)
    {V : Type*} [Finite V] (T : SimpleGraph V) (hT : T.IsTree) (hcard : T.edgeSet.ncard = n) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  have h_rainbow : HasRainbowCopy n T := by
    classical
    by_cases hC : IsCaseC δ n T
    · exact caseC_rainbow δ hδ n hn_pos T hT hcard hC
    · rcases case_division δ hδ n hn_pos hn_large T hT hcard with hA | hB | hC2
      · rcases hA with ⟨S, hS_leaves, hS_indep, hS_size⟩
        exact caseA_rainbow δ hδ n hn_pos hn_large T hT hcard S hS_leaves hS_size hS_indep
      · exact caseB_rainbow δ hδ n hn_pos T hT hcard hB hC
      · exact False.elim (hC hC2)
  exact rainbow_implies_decomposition n hn_pos T hT hcard h_rainbow

end Ringel
