/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.Nullspace
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_16.ErrorConstant

public section

noncomputable section

namespace TsvdEstimation

universe u v w

section Objective

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Evaluate the Chapter 7 TSVD expected squared estimation-error objective
along a truncation-index family `m`. -/
@[expose] def expectedSqErrorAlong
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F)
    (m : ℕ → ℕ) : ℕ → ℝ :=
  fun n ↦ expectedSqErrorObjective μ K R fTrue η n (m n)

@[simp] theorem expectedSqErrorAlong_apply
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (R : ℕ → ℕ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F)
    (m : ℕ → ℕ) (n : ℕ) :
    expectedSqErrorAlong μ K R fTrue η m n =
      expectedSqErrorObjective μ K R fTrue η n (m n) :=
  rfl

end Objective

section Benchmark

variable {H : Type u} {F : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The explicit TSVD expected-error benchmark profile from `(7.64)`. -/
@[expose] def optimalErrorBenchmark
    (K : ℕ → H →L[ℝ] F) (fTrue : H)
    (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦
    ‖FilterRegularization.nullspaceComponent (K n) fTrue‖ ^ 2 +
      errorConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ ((q - 1) / (p + q)))

@[simp] theorem optimalErrorBenchmark_apply
    (K : ℕ → H →L[ℝ] F) (fTrue : H)
    (b c p q σ : ℝ) (n : ℕ) :
    optimalErrorBenchmark K fTrue b c p q σ n =
      ‖FilterRegularization.nullspaceComponent (K n) fTrue‖ ^ 2 +
        errorConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ ((q - 1) / (p + q))) :=
  rfl

end Benchmark

end TsvdEstimation
