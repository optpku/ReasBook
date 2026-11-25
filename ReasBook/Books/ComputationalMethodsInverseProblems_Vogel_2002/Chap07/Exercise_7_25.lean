/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_31.ProfilePackage
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_31.EnergyBounds

public section

noncomputable section

namespace TikhonovExpectedCurve

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Helper for Exercise 7.25: `rpow (R ^ 2) (3 / 2) = R ^ 3` for positive `R`,
so the curvature denominator can be pulled apart along the normalized ratio. -/
lemma rpow_sq_three_halves {R : ℝ} (hR : 0 < R) :
    Real.rpow (R ^ 2) (3 / 2 : ℝ) = R ^ 3 := by
  show (R ^ 2) ^ (3 / 2 : ℝ) = R ^ 3
  have h1 : (R : ℝ) ^ 2 = R ^ (2 : ℝ) := (Real.rpow_natCast R 2).symm
  rw [h1, ← Real.rpow_mul hR.le (2 : ℝ) (3 / 2 : ℝ),
    show (2 : ℝ) * (3 / 2) = 3 by norm_num]
  exact Real.rpow_natCast R 3

/-- Helper for Exercise 7.25: the curvature denominator
`(R ^ 2 + α ^ 2 * S ^ 2) ^ (3 / 2)` factors through the normalized ratio
`u = α * S / R` as `R ^ 3 * (1 + u ^ 2) ^ (3 / 2)`. -/
lemma curvatureDenominator_factor {R S a : ℝ} (hR : 0 < R) :
    Real.rpow (R ^ 2 + a ^ 2 * S ^ 2) (3 / 2 : ℝ) =
      R ^ 3 * Real.rpow (1 + (a * S / R) ^ 2) (3 / 2 : ℝ) := by
  show (R ^ 2 + a ^ 2 * S ^ 2) ^ (3 / 2 : ℝ) =
      R ^ 3 * (1 + (a * S / R) ^ 2) ^ (3 / 2 : ℝ)
  have hfac : R ^ 2 + a ^ 2 * S ^ 2 = R ^ 2 * (1 + (a * S / R) ^ 2) := by
    field_simp [hR.ne']
  rw [hfac,
    Real.mul_rpow (x := R ^ 2) (y := 1 + (a * S / R) ^ 2) (z := (3 / 2 : ℝ))
      (by positivity) (by positivity)]
  rw [show (R ^ 2) ^ (3 / 2 : ℝ) = R ^ 3 from rpow_sq_three_halves hR]

/-- Helper for Exercise 7.25: the non-derivative normalized curvature term is
the one-variable scalar profile of `u = α * S / R`. -/
lemma expectedCurvatureLeading_eq_profile {R S a : ℝ} (hR : 0 < R) :
    R * S * (a * R + a ^ 2 * S) / Real.rpow (R ^ 2 + a ^ 2 * S ^ 2) (3 / 2 : ℝ) =
      (a * S / R) * (1 + a * S / R) / Real.rpow (1 + (a * S / R) ^ 2) (3 / 2 : ℝ) := by
  have hnum : R * S * (a * R + a ^ 2 * S) = R ^ 3 * ((a * S / R) * (1 + a * S / R)) := by
    field_simp [hR.ne']
  rw [hnum, curvatureDenominator_factor hR]
  have hR3 : (R : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hR.ne'
  field_simp

/-- Helper for Exercise 7.25: the derivative-dependent normalized curvature term
is the one-variable scalar profile of `z = S ^ 2 / (R * deriv S)`. -/
lemma expectedCurvatureDerivative_eq_profile {R S d a : ℝ} (hR : 0 < R) :
    ((R * S) ^ 2 / d) / Real.rpow (R ^ 2 + a ^ 2 * S ^ 2) (3 / 2 : ℝ) =
      (S ^ 2 / (R * d)) / Real.rpow (1 + (a * S / R) ^ 2) (3 / 2 : ℝ) := by
  rw [curvatureDenominator_factor hR]
  by_cases hd : d = 0
  · rw [hd]
    simp
  · have hR3 : (R : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hR.ne'
    field_simp

/-- Helper for Exercise 7.25: the expected residual energy is nonnegative,
being the integral of a squared norm. -/
lemma expectedResidualSq_nonneg_local
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F) (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (fTrue : H) (η : ℕ → Ω → F) (n : ℕ) (α : ℝ) :
    0 ≤ expectedResidualSq μ K Rtikh fTrue η n α := by
  rw [expectedResidualSq_apply]
  exact MeasureTheory.integral_nonneg fun _ ↦ by positivity

/-- Exercise 7.25, with explicit sufficient energy hypotheses. The original
samplewise filter assumptions did not control the two required ratios. Here
`FlatnessRegime` supplies a finite Tikhonov spectral model, bounded source
energy, a positive residual noise floor, a resolved mode at the regularization
scale, and `α → 0`, `n α² → 0`. Together with mean-square convergence, these
imply both profile limits rather than assuming either of them. -/
@[expose] def profilePackage_of_meanSquareConvergent
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (fTrue : H)
    (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (η : ℕ → Ω → F)
    (alphaL : ℕ → ℝ)
    (h_regime : EnergyBounds.FlatnessRegime
      (expectedResidualSq μ K Rtikh fTrue η)
      (expectedSolutionSq μ K Rtikh fTrue η)
      (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)
    (h_ms :
      ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)) :
    NormalizedCurvatureProfilePackage μ K Rtikh fTrue η alphaL :=
  let u : ℕ → ℝ := fun n ↦
    alphaL n * expectedSolutionSq μ K Rtikh fTrue η n (alphaL n) /
      expectedResidualSq μ K Rtikh fTrue η n (alphaL n)
  let z : ℕ → ℝ := fun n ↦
    (expectedSolutionSq μ K Rtikh fTrue η n (alphaL n)) ^ 2 /
      (expectedResidualSq μ K Rtikh fTrue η n (alphaL n) *
        deriv (expectedSolutionSq μ K Rtikh fTrue η n) (alphaL n))
  { u := u
    z := z
    leading_profile := by
      -- The leading profile is an algebraic consequence of `u = α * S / R`.
      intro n
      rw [expectedCurvatureLeadingNormalizedAlong_apply,
        expectedCurvatureDenominatorAlong_apply]
      rcases eq_or_lt_of_le
        (expectedResidualSq_nonneg_local μ K Rtikh fTrue η n (alphaL n)) with hR0 | hRpos
      · simp only [u]
        rw [← hR0]
        simp
      · exact expectedCurvatureLeading_eq_profile hRpos
    derivative_profile := by
      -- The derivative profile is the same computation with `z = S ^ 2 / (R * d)`.
      intro n
      rw [expectedCurvatureDerivativeNormalizedAlong_apply,
        expectedCurvatureDenominatorAlong_apply]
      rcases eq_or_lt_of_le
        (expectedResidualSq_nonneg_local μ K Rtikh fTrue η n (alphaL n)) with hR0 | hRpos
      · simp only [z]
        rw [← hR0]
        simp
      · exact expectedCurvatureDerivative_eq_profile hRpos
    hu := (EnergyBounds.profiles_tendsto_zero h_regime
      (h_ms.tendsto_zero.congr' (Filter.Eventually.of_forall fun n ↦
        TikhonovEstimation.objectiveAlong_apply _ _ n))).1
    hz := (EnergyBounds.profiles_tendsto_zero h_regime
      (h_ms.tendsto_zero.congr' (Filter.Eventually.of_forall fun n ↦
        TikhonovEstimation.objectiveAlong_apply _ _ n))).2 }


/-- The `u`-profile used by `profilePackage_of_meanSquareConvergent` is the
normalized ratio `αL * expectedSolutionSq / expectedResidualSq`. -/
theorem profilePackage_of_meanSquareConvergent_u
    (μ : MeasureTheory.Measure Ω)
    (K : ℕ → H →L[ℝ] F)
    (fTrue : H)
    (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (η : ℕ → Ω → F)
    (alphaL : ℕ → ℝ)
    (h_regime : EnergyBounds.FlatnessRegime
      (expectedResidualSq μ K Rtikh fTrue η)
      (expectedSolutionSq μ K Rtikh fTrue η)
      (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)
    (h_ms :
      ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)) :
    (profilePackage_of_meanSquareConvergent
        μ K fTrue Rtikh η alphaL h_regime h_ms).u =
      fun n ↦
        alphaL n * expectedSolutionSq μ K Rtikh fTrue η n (alphaL n) /
          expectedResidualSq μ K Rtikh fTrue η n (alphaL n) :=
  rfl

end

end TikhonovExpectedCurve
