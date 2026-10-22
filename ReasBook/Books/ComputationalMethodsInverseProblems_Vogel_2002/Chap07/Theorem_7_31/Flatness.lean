/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_31.ExpectedCurve
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_31.ProfilePackage

public section

noncomputable section

namespace TikhonovExpectedCurve

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
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

/-- Helper for Theorem 7.31: rewrite the expected curvature along `alphaL`
into the exact normalized quotient terms coming from
`LCurve.curvatureFromEnergies`. -/
theorem expectedCurvatureAlong_eq_normalizedTerms :
    (fun n ↦ expectedCurvature μ K Rtikh fTrue η n (alphaL n)) =
      fun n ↦
        -(expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL n +
          expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL n) := by
  funext n
  -- Rewrite to the energy-only curvature formula and split the common denominator once.
  rw [expectedCurvature_apply, LCurve.curvatureFromEnergies_def]
  rw [expectedCurvatureLeadingNormalizedAlong_apply,
    expectedCurvatureDerivativeNormalizedAlong_apply,
    expectedCurvatureDenominatorAlong_apply]
  rw [neg_div, add_div]

/-- Helper for Theorem 7.31: the expected residual energy is nonnegative
because it is the integral of a squared norm. -/
theorem expectedResidualSq_nonneg (n : ℕ) (α : ℝ) :
    0 ≤ expectedResidualSq μ K Rtikh fTrue η n α := by
  -- Rewrite to the defining integral and use pointwise nonnegativity of `‖·‖ ^ 2`.
  rw [expectedResidualSq_apply]
  exact MeasureTheory.integral_nonneg fun _ ↦ by positivity

/-- Helper for Theorem 7.31: the expected solution energy is nonnegative
because it is the integral of a squared norm. -/
theorem expectedSolutionSq_nonneg (n : ℕ) (α : ℝ) :
    0 ≤ expectedSolutionSq μ K Rtikh fTrue η n α := by
  -- Rewrite to the defining integral and use pointwise nonnegativity of `‖·‖ ^ 2`.
  rw [expectedSolutionSq_apply]
  exact MeasureTheory.integral_nonneg fun _ ↦ by positivity

/-- Helper for Theorem 7.31: once the leading normalized curvature term is
rewritten as its one-variable scalar profile, the profile tends to `0` with the
normalized ratio. -/
theorem leadingCurvatureProfile_tendsto_zero {u : ℕ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (fun n ↦ u n * (1 + u n) / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
  have h_num : Filter.Tendsto (fun n ↦ u n * (1 + u n)) Filter.atTop (nhds (0 : ℝ)) := by
    -- The numerator is a product of a vanishing factor and a factor tending to `1`.
    have h_one_add : Filter.Tendsto (fun n ↦ 1 + u n) Filter.atTop (nhds (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add hu
    simpa using hu.mul h_one_add
  have h_den :
      Filter.Tendsto
        (fun n ↦ Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))
        Filter.atTop (nhds (1 : ℝ)) := by
    -- The denominator profile is continuous at the positive base value `1`.
    have h_base : Filter.Tendsto (fun n ↦ 1 + u n ^ 2) Filter.atTop (nhds (1 : ℝ)) := by
      simpa [pow_two] using tendsto_const_nhds.add (hu.mul hu)
    simpa using h_base.rpow_const (Or.inl one_ne_zero)
  have h_inv :
      Filter.Tendsto
        (fun n ↦ (Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))⁻¹)
        Filter.atTop (nhds (1 : ℝ)) := by
    -- Inverting the positive denominator profile preserves convergence to `1`.
    simpa using h_den.inv₀ one_ne_zero
  -- Multiply the vanishing numerator by the inverse denominator profile.
  simpa [div_eq_mul_inv] using h_num.mul h_inv

/-- Helper for Theorem 7.31: once the derivative normalized curvature term is
rewritten as a bounded denominator profile times a vanishing numerator, the
whole term tends to `0`. -/
theorem derivativeCurvatureProfile_tendsto_zero {u z : ℕ → ℝ}
    (hu : Filter.Tendsto u Filter.atTop (nhds (0 : ℝ)))
    (hz : Filter.Tendsto z Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (fun n ↦ z n / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
  have h_den :
      Filter.Tendsto
        (fun n ↦ Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))
        Filter.atTop (nhds (1 : ℝ)) := by
    -- The same positive denominator profile appears in the derivative term.
    have h_base : Filter.Tendsto (fun n ↦ 1 + u n ^ 2) Filter.atTop (nhds (1 : ℝ)) := by
      simpa [pow_two] using tendsto_const_nhds.add (hu.mul hu)
    simpa using h_base.rpow_const (Or.inl one_ne_zero)
  have h_inv :
      Filter.Tendsto
        (fun n ↦ (Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))⁻¹)
        Filter.atTop (nhds (1 : ℝ)) := by
    -- The inverse denominator profile also tends to `1`.
    simpa using h_den.inv₀ one_ne_zero
  -- The numerator tends to `0`, and multiplying by a factor tending to `1` preserves that limit.
  simpa [div_eq_mul_inv] using hz.mul h_inv

/-- Helper for Theorem 7.31: a pointwise scalar-profile rewrite plus `u → 0`
is enough to make the concrete leading normalized term vanish. -/
theorem leadingNormalizedAlong_tendsto_zero_of_profile {u : ℕ → ℝ}
    (h_profile :
      ∀ n,
        expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL n =
          u n * (1 + u n) / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))
    (hu : Filter.Tendsto u Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL)
      Filter.atTop (nhds (0 : ℝ)) := by
  have h_eq :
      expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL =
        fun n ↦ u n * (1 + u n) / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ) := by
    -- Package the pointwise profile identity into a function equality once.
    funext n
    exact h_profile n
  -- Reuse the scalar profile limit after rewriting the concrete normalized term.
  simpa [h_eq] using leadingCurvatureProfile_tendsto_zero (u := u) hu

/-- Helper for Theorem 7.31: a pointwise scalar-profile rewrite plus `u → 0`
and `z → 0` is enough to make the concrete derivative normalized term vanish. -/
theorem derivativeNormalizedAlong_tendsto_zero_of_profile {u z : ℕ → ℝ}
    (h_profile :
      ∀ n,
        expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL n =
          z n / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))
    (hu : Filter.Tendsto u Filter.atTop (nhds (0 : ℝ)))
    (hz : Filter.Tendsto z Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL)
      Filter.atTop (nhds (0 : ℝ)) := by
  have h_eq :
      expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL =
        fun n ↦ z n / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ) := by
    -- Package the pointwise profile identity into a function equality once.
    funext n
    exact h_profile n
  -- Reuse the scalar profile limit after rewriting the concrete normalized term.
  simpa [h_eq] using derivativeCurvatureProfile_tendsto_zero (u := u) (z := z) hu hz

/-- Helper for Theorem 7.31: once Exercise 7.25 supplies scalar profile
sequences for both normalized curvature terms and proves that those profiles
vanish, the along-sequence normalized terms vanish by the two profile adapters
already proved in this file. -/
theorem normalizedCurvatureTerms_tendsto_zero_of_profiles {u z : ℕ → ℝ}
    (h_leading_profile :
      ∀ n,
        expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL n =
          u n * (1 + u n) / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))
    (h_derivative_profile :
      ∀ n,
        expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL n =
          z n / Real.rpow (1 + u n ^ 2) (3 / 2 : ℝ))
    (hu : Filter.Tendsto u Filter.atTop (nhds (0 : ℝ)))
    (hz : Filter.Tendsto z Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
        (expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto
        (expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL)
        Filter.atTop (nhds (0 : ℝ)) := by
  constructor
  · -- The leading term is a direct application of the scalar profile adapter.
    exact
      leadingNormalizedAlong_tendsto_zero_of_profile
        (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
        (alphaL := alphaL) h_leading_profile hu
  · -- The derivative term uses the companion scalar profile adapter.
    exact
      derivativeNormalizedAlong_tendsto_zero_of_profile
        (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
        (alphaL := alphaL) h_derivative_profile hu hz

/-- Helper for Theorem 7.31: once the source-facing profile data has already
been packaged, the normalized-term vanishing result is a direct application of
`normalizedCurvatureTerms_tendsto_zero_of_profiles`. -/
theorem normalizedCurvatureTerms_tendsto_zero_of_profilePackage
    (hPkg : NormalizedCurvatureProfilePackage μ K Rtikh fTrue η alphaL) :
    Filter.Tendsto
        (expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto
        (expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL)
        Filter.atTop (nhds (0 : ℝ)) := by
  rcases hPkg with ⟨u, z, h_leading_profile, h_derivative_profile, hu, hz⟩
  -- Consume the packaged profile identities and limits in one flat application.
  exact
    normalizedCurvatureTerms_tendsto_zero_of_profiles
      (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
      (alphaL := alphaL) h_leading_profile h_derivative_profile hu hz

/-- Helper for Theorem 7.31: the only remaining source-facing frontier is to
package the Exercise 7.25 asymptotics into the local normalized-profile
interface consumed downstream. -/
theorem sourceProfilePackage_of_cornerMeanSquareConvergent
    (h_corner :
      ∀ n,
        LCurve.IsCornerParameter
          (expectedCurvature μ K Rtikh fTrue η n) (alphaL n))
    (h_alpha_pos : ∀ n, 0 < alphaL n)
    (h_ms :
      ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)) :
    NormalizedCurvatureProfilePackage μ K Rtikh fTrue η alphaL := by
  -- Route correction: isolate the missing Exercise 7.25 asymptotics behind one
  -- support-level theorem instead of leaving the downstream wrapper open.
  -- TODO: destruct the earlier-owner theorem
  -- `Book.Ch7.Exercise_7_25.expectedCurvatureNormalizedProfiles_of_cornerMeanSquareConvergent`
  -- once it exists, audit any extra standing-assumption hypotheses it
  -- requires, and repackage its witnesses
  -- `⟨u, z, h_leading_profile, h_derivative_profile, hu, hz⟩`
  -- directly into `NormalizedCurvatureProfilePackage`.
  -- Current blocker: `Book/Ch7/Exercise_7_25.lean` still exports only the
  -- labeled blocker theorem `exercise725Blocker`, so there is no source-owned
  -- profile theorem available to destruct here.
  sorry

/-- Helper for Theorem 7.31: mean-square convergence at pointwise expected
L-curve corners should force both normalized curvature terms to vanish. -/
theorem normalizedCurvatureTerms_tendsto_zero_of_cornerMeanSquareConvergent
    (h_corner :
      ∀ n,
        LCurve.IsCornerParameter
          (expectedCurvature μ K Rtikh fTrue η n) (alphaL n))
    (h_alpha_pos : ∀ n, 0 < alphaL n)
    (h_ms :
      ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)) :
    Filter.Tendsto
        (expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL)
        Filter.atTop (nhds (0 : ℝ)) ∧
      Filter.Tendsto
        (expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL)
        Filter.atTop (nhds (0 : ℝ)) := by
  obtain hPkg :=
    sourceProfilePackage_of_cornerMeanSquareConvergent
      (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
      (alphaL := alphaL) h_corner h_alpha_pos h_ms
  -- Once the source-facing package is available, the flatness conclusion is immediate.
  exact
    normalizedCurvatureTerms_tendsto_zero_of_profilePackage
      (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
      (alphaL := alphaL) hPkg

end

end TikhonovExpectedCurve
