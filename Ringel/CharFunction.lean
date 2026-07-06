import Mathlib

open MeasureTheory ProbabilityTheory Complex

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

noncomputable def charFun (p : ℕ) [NeZero p] (X : Ω → ZMod p) (xi : ZMod p) : ℂ :=
  ∫ ω, exp (I * (((xi * X ω).val : ℂ)))
