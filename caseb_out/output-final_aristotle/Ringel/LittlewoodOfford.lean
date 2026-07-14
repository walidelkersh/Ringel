import Mathlib
import Ringel.RandomWalkTensor

open Finset
open scoped BigOperators

namespace Ringel

variable {E : Type*} [Fintype E] [DecidableEq E]

def subset_sum (v : E → ℝ) (S : Finset E) : ℝ :=
  ∑ e ∈ S, v e

set_option linter.unusedDecidableInType false in
lemma randomWalkDisplacement_eq (v : E → ℝ) (σ : E → Bool) :
  randomWalkDisplacement v σ = 2 • subset_sum v (Finset.filter (fun e => σ e) Finset.univ) - ∑ e : E, v e := by
  simp only [randomWalkDisplacement, subset_sum]
  have h_univ : (Finset.univ : Finset E) = (Finset.filter (fun e => σ e) Finset.univ) ∪ (Finset.filter (fun e => ¬ σ e) Finset.univ) := by
    ext x
    simp only [mem_univ, mem_union, mem_filter, true_and]
    constructor
    · intro _
      exact Classical.em (σ x = true)
    · intro _
      trivial
  have h_disj : Disjoint (Finset.filter (fun e => σ e) Finset.univ) (Finset.filter (fun e => ¬ σ e) Finset.univ) := by
    simp only [disjoint_filter]
    intro x _ h1 h2
    exact h2 h1
  have h_split : ∑ e : E, v e = ∑ e ∈ Finset.filter (fun e => σ e) Finset.univ, v e + ∑ e ∈ Finset.filter (fun e => ¬ σ e) Finset.univ, v e := by
    conv_lhs => rw [h_univ]
    exact sum_union h_disj
  have h_rw : ∑ e : E, edgeSign (σ e) • v e = ∑ e ∈ Finset.filter (fun e => σ e) Finset.univ, v e - ∑ e ∈ Finset.filter (fun e => ¬ σ e) Finset.univ, v e := by
    conv_lhs => rw [h_univ]
    rw [sum_union h_disj]
    have h_pos : ∑ e ∈ Finset.filter (fun e => σ e) Finset.univ, edgeSign (σ e) • v e = ∑ e ∈ Finset.filter (fun e => σ e) Finset.univ, v e := by
      apply sum_congr rfl
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have h1 : σ x = true := hx
      have : edgeSign (σ x) = 1 := by rw [h1]; rfl
      rw [this, one_zsmul]
    have h_neg : ∑ e ∈ Finset.filter (fun e => ¬ σ e) Finset.univ, edgeSign (σ e) • v e = - ∑ e ∈ Finset.filter (fun e => ¬ σ e) Finset.univ, v e := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have h1 : ¬ (σ x = true) := hx
      have h2 : σ x = false := by
        cases h3 : σ x
        · rfl
        · exact False.elim (h1 h3)
      have : edgeSign (σ x) = -1 := by rw [h2]; rfl
      rw [this, neg_one_zsmul]
    rw [h_pos, h_neg]
    exact sub_eq_add_neg _ _ |>.symm
  rw [h_rw]
  have h2 : 2 • ∑ e ∈ Finset.filter (fun e => σ e) Finset.univ, v e = ∑ e ∈ Finset.filter (fun e => σ e) Finset.univ, v e + ∑ e ∈ Finset.filter (fun e => σ e) Finset.univ, v e := by
    exact two_nsmul _
  rw [h2, h_split]
  abel

set_option linter.unusedDecidableInType false in
lemma lo_antichain (v : E → ℝ) (hv : ∀ e, 0 < v e) (target : ℝ) :
  IsAntichain (· ⊆ ·) (Finset.filter (fun S : Finset E => 2 • subset_sum v S = target) Finset.univ : Set (Finset E)) := by
  rintro S₁ hS₁ S₂ hS₂ hne hsub
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS₁ hS₂
  have hsum : ∑ e ∈ S₂, v e = ∑ e ∈ S₁, v e + ∑ e ∈ S₂ \ S₁, v e := by
    rw [← sum_union (Finset.disjoint_sdiff), Finset.union_sdiff_of_subset hsub]
  have hsum2 : 2 • ∑ e ∈ S₂, v e = 2 • ∑ e ∈ S₁, v e + 2 • ∑ e ∈ S₂ \ S₁, v e := by
    rw [hsum, smul_add]
  dsimp [subset_sum] at hS₁ hS₂
  have h0 : 2 • ∑ e ∈ S₂ \ S₁, v e = 0 := by
    calc 2 • ∑ e ∈ S₂ \ S₁, v e = (2 • ∑ e ∈ S₁, v e + 2 • ∑ e ∈ S₂ \ S₁, v e) - 2 • ∑ e ∈ S₁, v e := by abel
      _ = 2 • ∑ e ∈ S₂, v e - 2 • ∑ e ∈ S₁, v e := by rw [← hsum2]
      _ = target - target := by rw [hS₂, hS₁]
      _ = 0 := by abel
  have hnonempty : (S₂ \ S₁).Nonempty := by
    by_contra h_emp
    rw [Finset.not_nonempty_iff_eq_empty] at h_emp
    have : S₂ ⊆ S₁ := Finset.sdiff_eq_empty_iff_subset.mp h_emp
    exact hne (Subset.antisymm hsub this)
  have hpos : 0 < ∑ e ∈ S₂ \ S₁, v e := Finset.sum_pos (fun e _ => hv e) hnonempty
  have hpos2 : 0 < 2 • ∑ e ∈ S₂ \ S₁, v e := by
    rw [two_nsmul]
    exact add_pos hpos hpos
  rw [h0] at hpos2
  exact lt_irrefl 0 hpos2

set_option linter.unusedDecidableInType false in
theorem littlewood_offord_bound (v : E → ℝ) (hv : ∀ e, 0 < v e) (x : ℝ) :
  (Finset.filter (fun σ : E → Bool => randomWalkDisplacement v σ = x) Finset.univ).card ≤ (Fintype.card E).choose (Fintype.card E / 2) := by
  let f : (E → Bool) ↪ Finset E :=
    ⟨fun σ => Finset.filter (fun e => σ e) Finset.univ, by
      intro σ₁ σ₂ h
      ext e
      have h1 := Finset.ext_iff.mp h e
      simp only [mem_filter, mem_univ, true_and] at h1
      cases hx1 : σ₁ e <;> cases hx2 : σ₂ e
      · rfl
      · rw [hx1, hx2] at h1; contradiction
      · rw [hx1, hx2] at h1; contradiction
      · rfl⟩
  let target := x + ∑ e : E, v e
  have H_eq : ∀ σ : E → Bool, randomWalkDisplacement v σ = x ↔ 2 • subset_sum v (f σ) = target := by
    intro σ
    rw [randomWalkDisplacement_eq]
    dsimp [target, f]
    constructor
    · intro h
      rw [← h]
      abel
    · intro h
      have h1 : 2 • subset_sum v (filter (fun e => σ e) univ) - ∑ e : E, v e = target - ∑ e : E, v e := by
        rw [h]
      rw [h1]
      dsimp [target]
      abel
  have h_map : (Finset.filter (fun σ : E → Bool => randomWalkDisplacement v σ = x) Finset.univ).map f ⊆ Finset.filter (fun S : Finset E => 2 • subset_sum v S = target) Finset.univ := by
    intro S hS
    simp only [mem_map, mem_filter, mem_univ, true_and] at hS
    rcases hS with ⟨σ, hσ, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact (H_eq σ).mp hσ
  have h_card : (Finset.filter (fun σ : E → Bool => randomWalkDisplacement v σ = x) Finset.univ).card = ((Finset.filter (fun σ : E → Bool => randomWalkDisplacement v σ = x) Finset.univ).map f).card := by
    rw [card_map]
  rw [h_card]
  have h_le : ((Finset.filter (fun σ : E → Bool => randomWalkDisplacement v σ = x) Finset.univ).map f).card ≤ (Finset.filter (fun S : Finset E => 2 • subset_sum v S = target) Finset.univ).card := by
    exact card_le_card h_map
  have h_sperner := IsAntichain.sperner (lo_antichain v hv target)
  exact h_le.trans h_sperner

end Ringel
