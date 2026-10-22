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
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable (K : ℕ → H →L[ℝ] F)
variable (Rtikh : ℕ → ℝ → F →L[ℝ] H)
variable (fTrue : H)
variable (η : ℕ → Ω → F)
variable (alphaL : ℕ → ℝ)

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
