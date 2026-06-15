/-
Copyright (c) 2026 Walid K. Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid K. Elkersh
-/
import Mathlib

/-!
# Ringel's Conjecture

Proved for large $n$ by R. Montgomery, A. Pokrovskiy, B. Sudakov,
"A proof of Ringel's Conjecture", J. Eur. Math. Soc. 22 (2020), 3101-3132,
arXiv:2001.02665.
-/

open SimpleGraph

namespace Ringel

/--
**Ringel's Conjecture.** For any tree $T$ with $n$ edges, the complete graph
on $2n+1$ vertices decomposes into $2n+1$ edge-disjoint copies of $T$.

A "copy" of $T$ is the image `T.map (f i)` of $T$ under a vertex embedding
`f i : V ↪ Fin (2 * n + 1)`; each such image is isomorphic to $T$.
The decomposition conditions are:
* `Pairwise ... Disjoint`  — the copies are pairwise edge-disjoint;
* `⨆ i, T.map (f i) = ⊤`   — together they cover every edge of $K_{2n+1}$.

The hypothesis `[Finite V]` rules out infinite trees (for which `edgeSet.ncard` collapses to `0`).

In general this remains open; the large-$n$ form actually proved by Montgomery, Pokrovskiy and
Sudakov is `ringel_conjecture_large` below, which is the target of this formalization.
-/
theorem ringel_conjecture {V : Type*} [Finite V]
    (T : SimpleGraph V) (hT : T.IsTree)
    (n : ℕ) (hn : T.edgeSet.ncard = n) :
    ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
      Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
      ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  sorry

/--
**Ringel's Conjecture for large $n$ (Montgomery–Pokrovskiy–Sudakov, 2020).** For all
sufficiently large $n$, the decomposition above exists for every tree with $n$ edges. This is
the form proved in arXiv:2001.02665, and the target of this formalization.
-/
theorem ringel_conjecture_large :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n →
      ∃ f : Fin (2 * n + 1) → (V ↪ Fin (2 * n + 1)),
        Pairwise (fun i j => Disjoint (T.map (f i)).edgeSet (T.map (f j)).edgeSet) ∧
        ⨆ i, T.map (f i) = (⊤ : SimpleGraph (Fin (2 * n + 1))) := by
  sorry

end Ringel
