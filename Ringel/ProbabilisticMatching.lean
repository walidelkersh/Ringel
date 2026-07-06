import Mathlib
import Ringel.ProbBounds
import Mathlib.Combinatorics.Hall.Basic

open Classical
open Finset

namespace Ringel

/-- Hall's condition for a bipartite graph represented as an adjacency matrix. -/
def halls_condition {A B : Type*} [Fintype A] [Fintype B] (G : A → B → Bool) : Prop :=
  ∀ X : Finset A, X.card ≤ (X.biUnion (fun a => {b : B | G a b = true}.toFinset)).card

/-- If Hall's condition holds, there is a perfect matching (an injective function `A ↪ B` using only edges in `G`). -/
lemma hall_implies_matching {A B : Type*} [Fintype A] [Fintype B] (G : A → B → Bool)
    (h : halls_condition G) : ∃ f : A ↪ B, ∀ a : A, G a (f a) = true := by
  have h2 := (all_card_le_biUnion_card_iff_exists_injective (fun a => {b : B | G a b = true}.toFinset)).mp h
  obtain ⟨f, hf, hmem⟩ := h2
  use ⟨f, hf⟩
  intro a
  have := hmem a
  simp only [Set.mem_toFinset, Set.mem_setOf_eq] at this
  exact this

lemma prob_event_ext {Ω : Type*} [Fintype Ω] (p q : Ω → Prop) [DecidablePred p] [DecidablePred q] (h : ∀ ω, p ω ↔ q ω) : prob_event p = prob_event q := by
  unfold prob_event
  have h_eq : Finset.filter p Finset.univ = Finset.filter q Finset.univ := by
    ext ω
    simp [h ω]
  rw [h_eq]

/-- The union bound for probabilities of events. -/
lemma prob_event_union {Ω : Type*} [Fintype Ω] (p q : Ω → Prop) [DecidablePred p] [DecidablePred q] :
    prob_event (fun ω => p ω ∨ q ω) ≤ prob_event p + prob_event q := by
  unfold prob_event
  rw [← add_div]
  apply div_le_div_of_nonneg_right
  · norm_cast
    have := Finset.card_union_le (Finset.filter p Finset.univ) (Finset.filter q Finset.univ)
    have h_eq : Finset.filter (fun ω => p ω ∨ q ω) Finset.univ = Finset.filter p Finset.univ ∪ Finset.filter q Finset.univ := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_union]
    rw [h_eq]
    exact this
  · exact Nat.cast_nonneg (Fintype.card Ω)

/-- Boole's inequality (union bound) over a Finset. -/
lemma prob_event_biUnion {Ω : Type*} [Fintype Ω] {ι : Type*} (s : Finset ι) (p : ι → Ω → Prop) [∀ i, DecidablePred (p i)] :
    prob_event (fun ω => ∃ i ∈ s, p i ω) ≤ ∑ i ∈ s, prob_event (p i) := by
  classical
  induction' s using Finset.induction_on with i s hi ih
  · have h_eq : prob_event (fun ω => ∃ i ∈ (∅ : Finset ι), p i ω) = prob_event (fun (_ : Ω) => False) := by
      apply prob_event_ext
      intro ω
      simp
    rw [h_eq]
    unfold prob_event
    have : Finset.filter (fun (_ : Ω) => False) Finset.univ = ∅ := by ext; simp
    rw [this]
    simp
  · simp only [Finset.sum_insert hi]
    have h_eq : prob_event (fun ω => ∃ j ∈ insert i s, p j ω) = prob_event (fun ω => p i ω ∨ ∃ j ∈ s, p j ω) := by
      apply prob_event_ext
      intro ω
      simp only [Finset.mem_insert]
      constructor
      · rintro ⟨j, rfl | hj, hj_p⟩
        · exact Or.inl hj_p
        · exact Or.inr ⟨j, hj, hj_p⟩
      · rintro (hpi | ⟨j, hj, hj_p⟩)
        · exact ⟨i, Or.inl rfl, hpi⟩
        · exact ⟨j, Or.inr hj, hj_p⟩
    rw [h_eq]
    have h_le := prob_event_union (p i) (fun ω => ∃ j ∈ s, p j ω)
    apply le_trans h_le
    exact add_le_add (le_refl _) ih

/-- The probability that Hall's condition fails is bounded by the sum of probabilities that it fails for each subset X. -/
lemma prob_hall_failure_bound {A B : Type*} [Fintype A] [Fintype B] (P : Finset A → ℝ)
    (h_prob : ∀ X : Finset A, prob_event (fun G : A → B → Bool => (X.biUnion (fun a => {b : B | G a b = true}.toFinset)).card < X.card) ≤ P X) :
    prob_event (fun G : A → B → Bool => ¬ halls_condition G) ≤ ∑ X : Finset A, P X := by
  have h_eq : prob_event (fun G : A → B → Bool => ¬ halls_condition G) = prob_event (fun G : A → B → Bool => ∃ X ∈ (Finset.univ : Finset (Finset A)), (X.biUnion (fun a => {b : B | G a b = true}.toFinset)).card < X.card) := by
    apply prob_event_ext
    intro G
    simp only [halls_condition, not_forall, not_le, Finset.mem_univ, true_and]
  rw [h_eq]
  have h_bound := prob_event_biUnion Finset.univ (fun (X : Finset A) (G : A → B → Bool) => (X.biUnion (fun a => {b : B | G a b = true}.toFinset)).card < X.card)
  apply le_trans h_bound
  apply Finset.sum_le_sum
  intro X _
  exact h_prob X

end Ringel

