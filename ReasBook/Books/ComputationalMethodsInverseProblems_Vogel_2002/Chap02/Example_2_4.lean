/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_4.Operator

public section

noncomputable section

namespace RealL2

variable {Ω : Type} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω)

/- Example 2.4 (1). Mathlib's canonical owner for real `L²(Ω)` is `MeasureTheory.Lp ℝ 2 μ`. -/
#check MeasureTheory.Lp ℝ 2 μ

/-- Example 2.4 (1). The inner product on real `L²(Ω)` is
`⟪f, g⟫ = ∫ x, f x * g x ∂μ`. -/
theorem inner_eq_integral (f g : MeasureTheory.Lp ℝ 2 μ) :
    inner ℝ f g = ∫ x, f x * g x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp [mul_comm]

/-- Example 2.4 (1). The induced norm on real `L²(Ω)` is
`‖f‖ = Real.sqrt (∫ x, (f x) ^ (2 : ℕ) ∂μ)`. -/
theorem norm_eq_sqrt_integral_sq (f : MeasureTheory.Lp ℝ 2 μ) :
    ‖f‖ = Real.sqrt (∫ x, (f x) ^ (2 : ℕ) ∂μ) := by
  calc
    ‖f‖ = Real.sqrt (inner ℝ f f) := norm_eq_sqrt_real_inner f
    _ = Real.sqrt (∫ x, f x * f x ∂μ) := by
      rw [inner_eq_integral μ f f]
    _ = Real.sqrt (∫ x, (f x) ^ (2 : ℕ) ∂μ) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [pow_two]

variable [MeasureTheory.SFinite μ]
variable (k : Ω → Ω → ℝ)

/- Example 2.4. A square-integrable Fredholm kernel determines a unique Fredholm first-kind
operator realization on real `L²(Ω)`. -/
#check existsUnique_kernelOperator

/- Example 2.4 (2). If the Fredholm kernel `k` is square-integrable on `Ω × Ω`, then every
associated operator realization on real `L²(Ω)` is bounded with norm at most the square root of
the kernel energy. -/
#check kernelOperator_norm_le

/- Example 2.4 (3). The adjoint of a Fredholm kernel operator realization is the realization with
the swapped kernel. -/
#check kernelOperator_adjoint_eq_swap

/- Example 2.4 (4). The canonical reusable self-adjointness criterion is product-measure
almost-everywhere symmetry of the Fredholm kernel on `Ω × Ω`. -/
#check kernelOperator_isSelfAdjoint_of_ae_symmetric

/- Example 2.4 (4). The textbook pointwise-symmetry statement is the direct source-facing
specialization of the canonical almost-everywhere criterion. -/
#check kernelOperator_isSelfAdjoint_of_symmetric

end RealL2
