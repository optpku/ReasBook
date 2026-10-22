/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_29
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

noncomputable section

namespace FilterRegularization

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n] [DecidableEq n]
variable {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable {η : Ω → EuclideanSpace ℝ n} {σ : ℝ}

/-- Proposition 7.6 source-facing owner for the Chapter 7 semidiscrete
white-noise model: the noise has finite second moment, zero mean, and isotropic
second-moment matrix `σ ^ 2 • 1`. -/
@[mk_iff]
structure HasSemidiscreteWhiteNoiseModel
    (μ : MeasureTheory.Measure Ω) (η : Ω → EuclideanSpace ℝ n) (σ : ℝ) : Prop where
  /-- The noise has finite second moment. -/
  memLp : MeasureTheory.MemLp η 2 μ
  /-- The noise has mean zero. -/
  mean_zero : ∫ ω, η ω ∂μ = 0
  /-- The second-moment matrix is the isotropic matrix `σ ^ 2 • 1`. -/
  secondMoment_eq :
    ProbabilityTheory.secondMomentMatrix μ η = σ ^ 2 • (1 : Matrix n n ℝ)

namespace HasSemidiscreteWhiteNoiseModel

set_option linter.defProp false in
/-- Build the Proposition 7.6 white-noise owner from the three source-facing
assumptions used in Chapter 7. -/
def ofAssumptions
    (h_memLp : MeasureTheory.MemLp η 2 μ)
    (h_mean_zero : ∫ ω, η ω ∂μ = 0)
    (h_secondMoment :
      ProbabilityTheory.secondMomentMatrix μ η = σ ^ 2 • (1 : Matrix n n ℝ)) :
    HasSemidiscreteWhiteNoiseModel μ η σ :=
  { memLp := h_memLp
    mean_zero := h_mean_zero
    secondMoment_eq := h_secondMoment }

/-- Bridge from the Proposition 7.6 white-noise owner to the canonical
expected-square-norm formula from Proposition 4.29. -/
theorem expected_sqNorm_eq_trace_secondMoment
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ) :
    ∫ ω, ‖η ω‖ ^ 2 ∂μ =
      Matrix.trace (ProbabilityTheory.secondMomentMatrix μ η) :=
  ProbabilityTheory.expected_sqNorm_eq_trace_secondMomentMatrix hη.memLp

/-- Under the Chapter 7 semidiscrete white-noise model, the expected squared
noise norm equals the trace of `σ ^ 2 • 1`. -/
theorem expected_sqNorm_eq_trace_isotropic
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ) :
    ∫ ω, ‖η ω‖ ^ 2 ∂μ = Matrix.trace (σ ^ 2 • (1 : Matrix n n ℝ)) := by
  rw [expected_sqNorm_eq_trace_secondMoment hη, hη.secondMoment_eq]

end HasSemidiscreteWhiteNoiseModel

end

end FilterRegularization
