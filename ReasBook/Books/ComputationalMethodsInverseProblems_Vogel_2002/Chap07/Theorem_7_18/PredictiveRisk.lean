/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.EstimationError

public section

noncomputable section

namespace TsvdEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Chapter 7 TSVD expected predictive-risk objective as a function of the
truncation index `m` at fixed data size `n`, namely
`E (‖K n (FilterRegularization.estimationError (R n m) (K n) fTrue (η n ω))‖ ^ 2 / n)`. -/
@[expose] def expectedPredictiveRiskObjective
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F) : ℕ → ℕ → ℝ :=
  fun n m ↦
    ∫ ω, ‖K n (FilterRegularization.estimationError (R n m) (K n) fTrue (η n ω))‖ ^ 2 / (n : ℝ) ∂μ

/-- Evaluate `expectedPredictiveRiskObjective` at a fixed data size `n` and
truncation index `m`. -/
@[simp] theorem expectedPredictiveRiskObjective_apply
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F)
    (n m : ℕ) :
    expectedPredictiveRiskObjective μ K R fTrue η n m =
      ∫ ω,
        ‖K n (FilterRegularization.estimationError (R n m) (K n) fTrue (η n ω))‖ ^ 2 /
          (n : ℝ) ∂μ := by
  rfl

end

end TsvdEstimation
