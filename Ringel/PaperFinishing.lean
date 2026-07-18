import Ringel.ProbabilisticMatching
import Ringel.Primitives

namespace Ringel

/-!
# Finishing structures from MPS §§2, 4, and 5

This file formalizes the deterministic matching object used by the Case A finishing lemma in
`section2.tex` (Lemma `lem:finishA`) and the matching-union step used repeatedly in `section4.tex`.
These definitions expose the actual matching, target,
and colour constraints.
-/

open Classical

/-- A perfect rainbow matching from `X` into `Y`, using exactly the colours `D`.

The map chooses one target for every source in `X`.  Its injectivity says that the chosen edges
form a matching; `target_mem` keeps all targets in `Y`; `rainbow` says their colours are distinct;
and `colours_eq` says that the matching uses every colour in `D` (not merely colours from `D`). -/
structure PerfectRainbowMatching {V C : Type*} [DecidableEq C]
    (colour : Sym2 V → C) (X Y : Finset V) (D : Finset C) where
  target : (x : V) → x ∈ X → V
  target_mem : ∀ x hx, target x hx ∈ Y
  target_injective : ∀ x hx x' hx', target x hx = target x' hx' → x = x'
  rainbow : ∀ x hx x' hx',
    colour s(x, target x hx) = colour s(x', target x' hx') → x = x'
  colours_eq : Finset.image (fun x : X => colour s(x.1, target x.1 x.2)) Finset.univ = D

/-- Restrict a perfect rainbow matching to a subset of its source set. -/
lemma PerfectRainbowMatching.exists_restrict {V C : Type*} [DecidableEq V] [DecidableEq C]
    {colour : Sym2 V → C} {X Y : Finset V} {DC : Finset C}
    (M : PerfectRainbowMatching colour X Y DC) (X' : Finset V) (hX' : X' ⊆ X) :
    ∃ M' : PerfectRainbowMatching colour X' Y
      (Finset.image (fun x : X' => colour s(x.1, M.target x.1 (hX' x.2))) Finset.univ),
      ∀ x hx, M'.target x hx = M.target x (hX' hx) := by
  refine' ⟨ ⟨ _, _, _, _, _ ⟩, fun x hx => rfl ⟩;
  · exact fun x hx => M.target_mem x ( hX' hx );
  · exact fun x hx y hy hxy => M.target_injective x ( hX' hx ) y ( hX' hy ) hxy;
  · exact fun x hx y hy hxy => M.rainbow x ( hX' hx ) y ( hX' hy ) hxy;
  · ext; aesop;

/-- Deterministic union step behind the three matching stages of the Case A finishing argument.

Two rainbow matchings on disjoint source sets can be combined when their target ranges and colour
sets are disjoint.  The resulting matching uses exactly the union of the two colour sets. -/
lemma PerfectRainbowMatching.exists_disjointUnion {V C : Type*}
    [DecidableEq V] [DecidableEq C] (colour : Sym2 V → C)
    {X₁ X₂ Y : Finset V} {C₁ C₂ : Finset C}
    (M₁ : PerfectRainbowMatching colour X₁ Y C₁)
    (M₂ : PerfectRainbowMatching colour X₂ Y C₂)
    (hX : Disjoint X₁ X₂)
    (hY : ∀ x₁ hx₁ x₂ hx₂, M₁.target x₁ hx₁ ≠ M₂.target x₂ hx₂)
    (hColour : ∀ x₁ hx₁ x₂ hx₂,
      colour s(x₁, M₁.target x₁ hx₁) ≠ colour s(x₂, M₂.target x₂ hx₂)) :
    ∃ M : PerfectRainbowMatching colour (X₁ ∪ X₂) Y (C₁ ∪ C₂),
      (∀ x hx, M.target x (Finset.mem_union_left X₂ hx) = M₁.target x hx) ∧
      (∀ x hx, M.target x (Finset.mem_union_right X₁ hx) = M₂.target x hx) := by
  simp_all +decide [Finset.disjoint_left]
  refine' ⟨ ⟨ fun x hx => if hx₁ : x ∈ X₁ then M₁.target x hx₁ else M₂.target x (by aesop),
    _, _, _, _ ⟩, _, _ ⟩ <;> simp_all +decide
  · intro x hx; split_ifs <;> [ exact M₁.target_mem _ _; exact M₂.target_mem _ _ ] ;
  · grind +suggestions;
  · grind +suggestions;
  · ext c;
    simp +decide [ ← M₁.colours_eq, ← M₂.colours_eq ];
    constructor;
    · grind;
    · rintro ( ⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩ ) <;> [ exact ⟨ a, Or.inl ha, by aesop ⟩ ; exact ⟨ a, Or.inr ha, by aesop ⟩ ];
  · grind

/-- A perfect rainbow matching uses as many colours as source vertices.  This is the exact
cardinality compatibility implicit in `lem:finishA`. -/
lemma PerfectRainbowMatching.card_colours_eq_card_sources {V C : Type*}
    [DecidableEq V] [DecidableEq C] {colour : Sym2 V → C} {X Y : Finset V} {D : Finset C}
    (M : PerfectRainbowMatching colour X Y D) : D.card = X.card := by
  rw [← M.colours_eq, Finset.card_image_of_injective _ fun x y hxy => by
    have := M.rainbow _ x.2 _ y.2 hxy
    aesop]
  simp +decide

end Ringel
