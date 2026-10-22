/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_6.WhiteNoise

public section

noncomputable section

namespace FilterRegularization.HasSemidiscreteWhiteNoiseModel

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : Type v} [Fintype n] [DecidableEq n] [Nonempty n]
variable {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
variable {η : Ω → EuclideanSpace ℝ n} {σ : ℝ}

/-- Exercise 7.9. Equation `(7.35)`: under the Chapter 7 semidiscrete
white-noise model, the expected squared noise norm normalized by
`Fintype.card n` equals `σ ^ 2`. -/
theorem expectedSqNorm_div_card_eq_sigma_sq
    (hη : HasSemidiscreteWhiteNoiseModel μ η σ) :
    (∫ ω, ‖η ω‖ ^ 2 ∂μ) / (Fintype.card n : ℝ) = σ ^ 2 := by
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [expected_sqNorm_eq_trace_isotropic hη, Matrix.trace_smul, smul_eq_mul, Matrix.trace_one]
  rw [mul_comm]
  exact mul_div_cancel_left₀ _ hcard

end

end FilterRegularization.HasSemidiscreteWhiteNoiseModel
