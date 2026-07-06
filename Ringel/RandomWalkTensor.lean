import Mathlib

open Finset
open scoped BigOperators

variable {E : Type*} [Fintype E]
variable {V : Type*} [AddCommGroup V]

/-- Maps a boolean sign assignment to an integer sign: true ↦ 1, false ↦ -1 -/
def edgeSign (b : Bool) : ℤ :=
  if b then 1 else -1

/-- A multi-dimensional random walk displacement for a specific sign assignment `σ`
on the edges of a graph/tree. `v e` represents the vector associated with edge `e`. -/
def randomWalkDisplacement (v : E → V) (σ : E → Bool) : V :=
  ∑ e, edgeSign (σ e) • v e

theorem edgeSign_not (b : Bool) : edgeSign (not b) = - edgeSign b := by
  cases b <;> rfl

/-- Flipping all signs negates the total displacement of the random walk. -/
theorem randomWalkDisplacement_neg (v : E → V) (σ : E → Bool) :
    randomWalkDisplacement v (fun e => not (σ e)) = - randomWalkDisplacement v σ := by
  simp [randomWalkDisplacement, edgeSign_not, ← Finset.sum_neg_distrib]

/-- The space of all such random walks, which can form a tensor space or module. -/
abbrev RandomWalkTensorSpace (E V : Type*) [AddCommGroup V] :=
  (E → Bool) → V

