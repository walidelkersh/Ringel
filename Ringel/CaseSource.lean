/-
Copyright (c) 2026 Walid Elkersh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walid Elkersh
-/
import Ringel.CaseA
import Ringel.CaseB
import Ringel.CaseC
import Ringel.CaseCOneVertex
import Ringel.CaseDivision

/-!
# Source theorem package for Ringel's conjecture

This file packages the source-level Case A and Case B statements at the level of the paper.
It keeps the final audited surface free of the older conditional embedding inputs.
-/

open SimpleGraph

namespace Ringel

/-- Source-level Case A statement: for sufficiently large `n`, Case A trees have rainbow copies. -/
def CaseASourceStatement (δ : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
    T.IsTree → T.edgeSet.ncard = n → IsCaseA δ n T → HasRainbowCopy n T

/-- Source-level Case B statement: for sufficiently large `n`, Case B trees have rainbow copies. -/
def CaseBSourceStatement (δ : ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
    T.IsTree → T.edgeSet.ncard = n → IsCaseB δ n T → ¬ IsCaseC δ n T → HasRainbowCopy n T

/-- Exact source package matching the paper's small-`δ` parameter choice. -/
def CaseABSourceStatement : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ CaseASourceStatement δ ∧ CaseBSourceStatement δ

/-- The source package implies eventual rainbow copies. -/
theorem rainbow_copy_exists_of_source
    (hsource : CaseABSourceStatement) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n → HasRainbowCopy n T := by
  rcases hsource with ⟨δ, hδ, hδle, hA, hB⟩
  have hC : ∀ᶠ n : ℕ in Filter.atTop, ∀ {V : Type*} [Finite V] (T : SimpleGraph V),
      T.IsTree → T.edgeSet.ncard = n → IsCaseC δ n T → HasRainbowCopy n T :=
    caseC_rainbow δ
  filter_upwards [case_division δ hδ hδle, hA, hB, hC] with n hn_div hn_A hn_B hn_C
  intro V _ T hT hcard
  rcases hn_div T hT hcard with hAcase | hBcase | hCcase
  · by_cases hCaseC : IsCaseC δ n T
    · exact hn_C T hT hcard hCaseC
    · exact hn_A T hT hcard hAcase
  · by_cases hCaseC : IsCaseC δ n T
    · exact hn_C T hT hcard hCaseC
    · exact hn_B T hT hcard hBcase hCaseC
  · exact hn_C T hT hcard hCcase

/-- Wrapper form of the source package theorem. -/
theorem rainbow_copy_exists_of_source_statement :
    CaseABSourceStatement → ∀ᶠ (n : ℕ) in Filter.atTop, ∀ {V : Type*} [Finite V]
      (T : SimpleGraph V), T.IsTree → T.edgeSet.ncard = n → HasRainbowCopy n T := by
  intro hsource
  exact rainbow_copy_exists_of_source hsource

end Ringel
