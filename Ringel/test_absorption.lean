import Mathlib
import Ringel.CaseA
import Ringel.CaseAObstruction

namespace Ringel

open Classical

/-!
The unconditional absorption claim is too strong: an absorbing map is a rainbow copy and therefore
forces `T.edgeSet.ncard ≤ n`; `exists_absorption_matching_statement_false` gives the explicit
counterexample `pathGraph 3` with `n = 1`.  MPS §§4–6 instead supplies positive probability of the
valid absorption event in its parameter regime.  The statement below isolates exactly that input.
-/

/-- The strongest direct absorption conclusion justified by the explicit MPS probability input. -/
lemma test_exists_absorption_matching (n : ℕ) (hn : 0 < n) {V : Type*} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree) (S : Set V)
    (hS_leaves : ∀ v ∈ S, IsLeaf T v)
    (hS_indep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬T.Adj v w)
    (f_core : (Sᶜ : Set V) ↪ Fin (2 * n + 1))
    [Fintype (S ↪ Fin (2 * n + 1))]
    (h_prob : prob_event (fun f_leaves : S ↪ Fin (2 * n + 1) =>
      valid_absorption n hn T S f_core f_leaves) > 0) :
    ∃ f_leaves : S ↪ Fin (2 * n + 1),
      valid_absorption n hn T S f_core f_leaves := by
  exact exists_absorption_matching_prob n hn T hT S hS_leaves hS_indep f_core h_prob

end Ringel
