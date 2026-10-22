/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_31.ExpectedCurve

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

/-- Helper for Theorem 7.31: if mean-square convergence along `alphaL` forces
the expected curvature values to tend to `0`, then any family whose expected
curvature does not tend to `0` cannot be mean-square convergent. -/
theorem not_meanSquareConvergent_of_not_tendsto_expectedCurvature
    (h_curvature_of_convergent :
      ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL) →
      Filter.Tendsto
        (fun n ↦ expectedCurvature μ K Rtikh fTrue η n (alphaL n))
        Filter.atTop (nhds (0 : ℝ)))
    (h_curvature :
      ¬ Filter.Tendsto
        (fun n ↦ expectedCurvature μ K Rtikh fTrue η n (alphaL n))
        Filter.atTop (nhds (0 : ℝ))) :
    ¬ ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL) := by
  -- Take the contrapositive of the curvature-flatness implication.
  exact fun h_ms ↦ h_curvature (h_curvature_of_convergent h_ms)

/-- Helper for Theorem 7.31: the backend owner
`ParameterChoice.IsMeanSquareNonconvergent` should be introduced from the
negated convergence statement already proved in this file. -/
theorem isMeanSquareNonconvergent_of_not_meanSquareConvergent
    (h_not_ms :
      ¬ ParameterChoice.IsMeanSquareConvergent
          (TikhonovEstimation.objectiveAlong
            (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)) :
    ParameterChoice.IsMeanSquareNonconvergent
      (TikhonovEstimation.objectiveAlong
        (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL) := by
  -- Route correction: use the canonical owner theorem instead of unfolding the
  -- `ParameterChoice` definition locally inside the theorem proof.
  exact
    ParameterChoice.isMeanSquareNonconvergent_of_not_meanSquareConvergent h_not_ms

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
def sourceProfilePackage_of_cornerMeanSquareConvergent
    (h_corner :
      ∀ n,
        LCurve.IsCornerParameter
          (expectedCurvature μ K Rtikh fTrue η n) (alphaL n))
    (h_alpha_pos : ∀ n, 0 < alphaL n)
    (h_ms :
      ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)) :
    NormalizedCurvatureProfilePackage μ K Rtikh fTrue η alphaL :=
  -- Route correction: keep the local flatness interface stable and wait for the
  -- exact Exercise 7.25 profile theorem instead of inventing a new surrogate.
  -- TODO: destruct the earlier-owner theorem
  -- `Book.Ch7.Exercise_7_25.expectedCurvatureNormalizedProfiles_of_cornerMeanSquareConvergent`
  -- once it exists, audit any extra standing-assumption hypotheses it
  -- requires, and repackage its witnesses
  -- `⟨u, z, h_leading_profile, h_derivative_profile, hu, hz⟩`
  -- directly into `NormalizedCurvatureProfilePackage`.
  -- Statement-defect audit: the only recovered source owner for this bridge is
  -- Exercise 7.25, and that item explicitly assumes
  -- `FilterRegularization.StandingAssumptions ...`. The current main theorem
  -- quantifies over arbitrary `K`, `Rtikh`, and `η` with no comparable
  -- regularity bundle, so finishing this helper would require smuggling a
  -- missing source-side hypothesis into the proof rather than closing a local
  -- Lean proof gap.
  -- Current blocker: `Book/Ch7/Exercise_7_25.lean` still contains only the
  -- source-blocker prose plus `#check`s, and it imports `Book.Ch7.Theorem_7_31`.
  -- There is therefore no earlier source-owned profile theorem available to
  -- destruct here without first repairing that module boundary.
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


/-- Helper for Theorem 7.31: if both normalized expected-curvature terms vanish,
then the expected curvature itself vanishes along `alphaL`. -/
theorem expectedCurvatureAlong_tendsto_zero_of_normalizedTerms
    (h_leading :
      Filter.Tendsto
        (expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL)
        Filter.atTop (nhds (0 : ℝ)))
    (h_derivative :
      Filter.Tendsto
        (expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL)
        Filter.atTop (nhds (0 : ℝ))) :
    Filter.Tendsto
      (fun n ↦ expectedCurvature μ K Rtikh fTrue η n (alphaL n))
      Filter.atTop (nhds (0 : ℝ)) := by
  have h_sum :
      Filter.Tendsto
        (fun n ↦
          expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL n +
            expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL n)
        Filter.atTop (nhds (0 : ℝ)) := by
    -- Add the two vanishing normalized terms before applying the outer minus sign.
    simpa using h_leading.add h_derivative
  have h_neg :
      Filter.Tendsto
        (fun n ↦
          -(expectedCurvatureLeadingNormalizedAlong μ K Rtikh fTrue η alphaL n +
            expectedCurvatureDerivativeNormalizedAlong μ K Rtikh fTrue η alphaL n))
        Filter.atTop (nhds (0 : ℝ)) := by
    -- Negating a sequence that tends to `0` preserves the limit.
    simpa using h_sum.neg
  -- Rewrite the curvature sequence once into the normalized-term normal form.
  rw [expectedCurvatureAlong_eq_normalizedTerms]
  exact h_neg

/-- Helper for Theorem 7.31: the missing Exercise 7.25 bridge should show that
mean-square convergence along `alphaL` forces the expected Tikhonov L-curve
curvature along `alphaL` to tend to `0`. -/
theorem expectedCurvatureAlong_tendsto_zero_of_meanSquareConvergent
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
      (fun n ↦ expectedCurvature μ K Rtikh fTrue η n (alphaL n))
      Filter.atTop (nhds (0 : ℝ)) := by
  obtain ⟨h_leading, h_derivative⟩ :=
    normalizedCurvatureTerms_tendsto_zero_of_cornerMeanSquareConvergent
      μ K Rtikh fTrue η alphaL h_corner h_alpha_pos h_ms
  -- Route correction: isolate the missing Exercise 7.25 asymptotics and keep
  -- the curvature-to-zero step as a deterministic normalization argument.
  exact
    expectedCurvatureAlong_tendsto_zero_of_normalizedTerms
      μ K Rtikh fTrue η alphaL h_leading h_derivative

/-- thm_7_31. Theorem 7.31. If `alphaL n` is a corner parameter of the expected
Tikhonov L-curve for every `n`, the attained curvature values do not tend to
`0`, and `alphaL n` stays positive, then the expected squared reconstruction
error along `alphaL` does not converge to `0`. -/
-- Route correction: the source contradiction route needs the selected corner
-- parameters to lie in `Set.Ioi 0`, but the current `LCurve.IsCornerParameter`
-- owner is defined via `IsMaxOn`, which does not encode membership.
theorem meanSquareNonconvergent_of_cornerCurvature_not_tendsto_zero
    (h_corner :
      ∀ n,
        LCurve.IsCornerParameter
          (expectedCurvature μ K Rtikh fTrue η n) (alphaL n))
    (h_alpha_pos : ∀ n, 0 < alphaL n)
    (h_curvature :
      ¬ Filter.Tendsto
        (fun n ↦ expectedCurvature μ K Rtikh fTrue η n (alphaL n))
        Filter.atTop (nhds (0 : ℝ))) :
    ParameterChoice.IsMeanSquareNonconvergent
      (TikhonovEstimation.objectiveAlong
        (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL) := by
  have h_not_ms :
      ¬ ParameterChoice.IsMeanSquareConvergent
          (TikhonovEstimation.objectiveAlong
            (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL) := by
    -- Specialize the curvature-flatness bridge to the current corner family and
    -- contradict the nonvanishing curvature hypothesis.
    exact
      not_meanSquareConvergent_of_not_tendsto_expectedCurvature
        (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
        (alphaL := alphaL)
        (h_curvature_of_convergent :=
          expectedCurvatureAlong_tendsto_zero_of_meanSquareConvergent
            μ K Rtikh fTrue η alphaL h_corner h_alpha_pos)
        h_curvature
  -- Repackage the contradiction result through the canonical owner theorem.
  exact
    isMeanSquareNonconvergent_of_not_meanSquareConvergent
      (μ := μ) (K := K) (Rtikh := Rtikh) (fTrue := fTrue) (η := η)
      (alphaL := alphaL) h_not_ms

/-- Canonical optimal-family bridge for Theorem 7.31. Minimizing the negated
expected curvature on `Set.Ioi 0` recovers the pointwise corner-parameter
hypothesis through `cornerFamily_iff`, so the source-facing theorem applies
without restating the pointwise maximizer inequality. The explicit positivity
side condition is still needed because `IsMinOn` does not encode membership. -/
theorem meanSquareNonconvergent_of_cornerFamily_curvature_not_tendsto_zero
    (h_corner :
      ParameterChoice.IsOptimalParameterFamily
        (fun n α ↦ -(expectedCurvature μ K Rtikh fTrue η n α))
        (fun _ ↦ Set.Ioi (0 : ℝ)) alphaL)
    (h_alpha_pos : ∀ n, 0 < alphaL n)
    (h_curvature :
      ¬ Filter.Tendsto
        (fun n ↦ expectedCurvature μ K Rtikh fTrue η n (alphaL n))
        Filter.atTop (nhds (0 : ℝ))) :
    ParameterChoice.IsMeanSquareNonconvergent
      (TikhonovEstimation.objectiveAlong
        (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL) := by
  have h_pointwise_corner :
      ∀ n,
        LCurve.IsCornerParameter
          (expectedCurvature μ K Rtikh fTrue η n) (alphaL n) := by
    -- Translate the optimal-family owner back to the pointwise corner condition.
    exact (cornerFamily_iff μ K Rtikh fTrue η alphaL).mp h_corner
  -- Reuse the source-facing theorem after transporting the corner hypothesis.
  exact
    meanSquareNonconvergent_of_cornerCurvature_not_tendsto_zero
      μ K Rtikh fTrue η alphaL h_pointwise_corner h_alpha_pos h_curvature

end

end TikhonovExpectedCurve
