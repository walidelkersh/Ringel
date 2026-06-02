/-
Copyright (c) 2026. Released under Apache 2.0 license.

Ringel's Conjecture.

Proved for large `n` by R. Montgomery, A. Pokrovskiy, B. Sudakov,
"A proof of Ringel's Conjecture", J. Eur. Math. Soc. 22 (2020), 3101-3132.
arXiv:2001.02665.
-/
import Mathlib

open SimpleGraph

namespace Ringel

/--
**Ringel's Conjecture.** For any tree `T` with `n` edges, the complete graph
on `2 * n + 1` vertices decomposes into `2 * n + 1` edge-disjoint copies of `T`.

A "copy" of `T` is the image `T.map (f i)` of `T` under a vertex embedding
`f i : V ↪ Fin (2 * n + 1)`; each such image is isomorphic to `T`.
The decomposition conditions are:
* `Pairwise ... Disjoint`  — the copies are pairwise edge-disjoint;
* `⨆ i, T.map (f i) = ⊤`   — together they cover every edge of `K_{2n+1}`.

This statement is minimal and well-posed, using `Set.ncard` for edge count and requiring
only `[Fintype V]` without any artificial decidability assumptions.
-/
theorem ringel_conjecture {V : Type*} [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (n : ℕ) (hn : T.edgeSet.ncard = n) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  sorry

end Ringel
