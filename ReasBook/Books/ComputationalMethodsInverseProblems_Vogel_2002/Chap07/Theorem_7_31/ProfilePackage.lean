/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_31.ExpectedCurve

public section

noncomputable section

namespace TikhonovExpectedCurve

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (μ : MeasureTheory.Measure Ω)
variable (K : ℕ → H →L[ℝ] F)
variable (Rtikh : ℕ → ℝ → F →L[ℝ] H)
variable (fTrue : H)
variable (η : ℕ → Ω → F)
variable (alphaL : ℕ → ℝ)

/-- Helper for Theorem 7.31: the common denominator in the normalized expected
curvature formula along `alphaL`. -/
@[expose] def expectedCurvatureDenominatorAlong : ℕ → ℝ :=
  fun n ↦
    Real.rpow
      ((expectedResidualSq μ K Rtikh fTrue η n (alphaL n)) ^ 2 +
        (alphaL n) ^ 2 * (expectedSolutionSq μ K Rtikh fTrue η n (alphaL n)) ^ 2)
      (3 / 2 : ℝ)

/-- The defining evaluation rule for `expectedCurvatureDenominatorAlong`. -/
theorem expectedCurvatureDenominatorAlong_apply (n : ℕ) :
    expectedCurvatureDenominatorAlong μ K Rtikh fTrue η alphaL n =
      Real.rpow
        ((expectedResidualSq μ K Rtikh fTrue η n (alphaL n)) ^ 2 +
          (alphaL n) ^ 2 * (expectedSolutionSq μ K Rtikh fTrue η n (alphaL n)) ^ 2)
        (3 / 2 : ℝ) := by
  -- Expose the denominator owner once before rewriting the curvature formula.
  rfl

/-- Helper for Theorem 7.31: the non-derivative normalized term in the expected
curvature formula along `alphaL`. -/
@[expose] def expectedCurvatureLeadingNormalizedAlong : ℕ → ℝ :=
  fun n ↦
    (expectedResidualSq μ K Rtikh fTrue η n (alphaL n) *
        expectedSolutionSq μ K Rtikh fTrue η n (alphaL n) *
        (alphaL n * expectedResidualSq μ K Rtikh fTrue η n (alphaL n) +
          (alphaL n) ^ 2 * expectedSolutionSq μ K Rtikh fTrue η n (alphaL n))) /
      expectedCurvatureDenominatorAlong μ K Rtikh fTrue η alphaL n

/-- The defining evaluation rule for
`expectedCurvatureLeadingNormalizedAlong`. -/
theorem expectedCurvatureLeadingNormalizedAlong_apply (n : ℕ) :
    expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL n =
      (expectedResidualSq μ K Rtikh fTrue η n (alphaL n) *
          expectedSolutionSq μ K Rtikh fTrue η n (alphaL n) *
          (alphaL n * expectedResidualSq μ K Rtikh fTrue η n (alphaL n) +
            (alphaL n) ^ 2 * expectedSolutionSq μ K Rtikh fTrue η n (alphaL n))) /
        expectedCurvatureDenominatorAlong μ K Rtikh fTrue η alphaL n := by
  -- Expose the normalized leading-term owner once before the assembly proof.
  rfl

/-- Helper for Theorem 7.31: the derivative-dependent normalized term in the
expected curvature formula along `alphaL`. -/
@[expose] def expectedCurvatureDerivativeNormalizedAlong : ℕ → ℝ :=
  fun n ↦
    (((expectedResidualSq μ K Rtikh fTrue η n (alphaL n) *
          expectedSolutionSq μ K Rtikh fTrue η n (alphaL n)) ^ 2) /
        deriv (expectedSolutionSq μ K Rtikh fTrue η n) (alphaL n)) /
      expectedCurvatureDenominatorAlong μ K Rtikh fTrue η alphaL n

/-- The defining evaluation rule for
`expectedCurvatureDerivativeNormalizedAlong`. -/
theorem expectedCurvatureDerivativeNormalizedAlong_apply (n : ℕ) :
    expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL n =
      (((expectedResidualSq μ K Rtikh fTrue η n (alphaL n) *
            expectedSolutionSq μ K Rtikh fTrue η n (alphaL n)) ^ 2) /
          deriv (expectedSolutionSq μ K Rtikh fTrue η n) (alphaL n)) /
        expectedCurvatureDenominatorAlong μ K Rtikh fTrue η alphaL n := by
  -- Expose the derivative-term owner once before the assembly proof.
  rfl

/-- Helper for Theorem 7.31: package exactly the scalar profile identities and
limits consumed by the normalized-curvature flatness lemma. -/
structure NormalizedCurvatureProfilePackage where
  u : ℕ → ℝ
  z : ℕ → ℝ
  leading_profile :
    ∀ n,
      expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL n =
        u n * (1 + u n) / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ)
  derivative_profile :
    ∀ n,
      expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL n =
        z n / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ)
  hu : Filter.Tendsto u Filter.atTop (nhds (0 : ℝ))
  hz : Filter.Tendsto z Filter.atTop (nhds (0 : ℝ))

end

end TikhonovExpectedCurve
