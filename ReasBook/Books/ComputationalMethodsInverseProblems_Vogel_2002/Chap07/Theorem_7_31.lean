/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_31.Flatness

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

/-- Under the finite spectral and parameter-scale conditions of
`FlatnessRegime`, mean-square convergence forces the expected curvature to zero. -/
theorem expectedCurvatureAlong_tendsto_zero_of_meanSquareConvergent
    (h_corner :
      ∀ n,
        LCurve.IsCornerParameter
          (expectedCurvature μ K Rtikh fTrue η n) (alphaL n))
    (h_alpha_pos : ∀ n, 0 < alphaL n)
    (h_regime : EnergyBounds.FlatnessRegime
      (expectedResidualSq μ K Rtikh fTrue η)
      (expectedSolutionSq μ K Rtikh fTrue η)
      (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)
    (h_ms :
      ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)) :
    Filter.Tendsto
      (fun n ↦ expectedCurvature μ K Rtikh fTrue η n (alphaL n))
      Filter.atTop (nhds (0 : ℝ)) := by
  obtain ⟨h_leading, h_derivative⟩ :=
    normalizedCurvatureTerms_tendsto_zero_of_cornerMeanSquareConvergent
      μ K Rtikh fTrue η alphaL h_corner h_alpha_pos h_regime h_ms
  exact
    expectedCurvatureAlong_tendsto_zero_of_normalizedTerms
      μ K Rtikh fTrue η alphaL h_leading h_derivative

/-- thm_7_31. Theorem 7.31. If `alphaL n` is a corner parameter of the expected
Tikhonov L-curve for every `n`, the attained curvature values do not tend to
`0`, and `alphaL n` stays positive, then the expected squared reconstruction
error along `alphaL` does not converge to `0`.

The earlier unrestricted declaration was missing the energy hypotheses needed
by Exercise 7.25. This corrected version explicitly assumes a finite spectral
energy model, a positive residual noise floor, a resolved mode `α ≤ λ ≤ 2α`,
`α → 0`, and `n α² → 0`, as bundled in `FlatnessRegime`. -/
-- Route correction: the source contradiction route needs the selected corner
-- parameters to lie in `Set.Ioi 0`, but the current `LCurve.IsCornerParameter`
-- owner is defined via `IsMaxOn`, which does not encode membership.
theorem meanSquareNonconvergent_of_cornerCurvature_not_tendsto_zero
    (h_corner :
      ∀ n,
        LCurve.IsCornerParameter
          (expectedCurvature μ K Rtikh fTrue η n) (alphaL n))
    (h_alpha_pos : ∀ n, 0 < alphaL n)
    (h_regime : EnergyBounds.FlatnessRegime
      (expectedResidualSq μ K Rtikh fTrue η)
      (expectedSolutionSq μ K Rtikh fTrue η)
      (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)
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
            μ K Rtikh fTrue η alphaL h_corner h_alpha_pos h_regime)
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
    (h_regime : EnergyBounds.FlatnessRegime
      (expectedResidualSq μ K Rtikh fTrue η)
      (expectedSolutionSq μ K Rtikh fTrue η)
      (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)
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
      μ K Rtikh fTrue η alphaL h_pointwise_corner h_alpha_pos h_regime h_curvature

end

end TikhonovExpectedCurve
