/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_31

public section

noncomputable section

namespace TikhonovExpectedCurve

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Exercise 7.25. If the Chapter 7 standing assumptions from Remark 7.12 hold
samplewise along the Tikhonov family `Rtikh`, and the expected squared
estimation error along `alphaL` tends to `0`, then the four source clauses
`(7.109)`-`(7.112)` are packaged by
`NormalizedCurvatureProfilePackage μ K Rtikh fTrue η alphaL`. -/
def profilePackage_of_meanSquareConvergent
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H) (c p b q : ℝ)
    (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (η : ℕ → Ω → F)
    (alphaL : ℕ → ℝ)
    (h_standing :
      ∀ ω,
        FilterRegularization.StandingAssumptions
          K S h_length fTrue c p b q
          (fun n ↦ K n fTrue + η n ω) (fun n ↦ η n ω)
          (fun n ↦ Rtikh n (alphaL n)) alphaL)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
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
    leading_profile := sorry
    derivative_profile := sorry
    hu := sorry
    hz := sorry }

/-- The `u`-profile used by `profilePackage_of_meanSquareConvergent` is the
normalized ratio `αL * expectedSolutionSq / expectedResidualSq`. -/
theorem profilePackage_of_meanSquareConvergent_u
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H) (c p b q : ℝ)
    (Rtikh : ℕ → ℝ → F →L[ℝ] H)
    (η : ℕ → Ω → F)
    (alphaL : ℕ → ℝ)
    (h_standing :
      ∀ ω,
        FilterRegularization.StandingAssumptions
          K S h_length fTrue c p b q
          (fun n ↦ K n fTrue + η n ω) (fun n ↦ η n ω)
          (fun n ↦ Rtikh n (alphaL n)) alphaL)
    (h_tikhonov : TikhonovEstimation.IsTikhonovReconstructionFamily K S Rtikh)
    (h_ms :
      ParameterChoice.IsMeanSquareConvergent
        (TikhonovEstimation.objectiveAlong
          (TikhonovEstimation.expectedObjective μ K Rtikh fTrue η) alphaL)) :
    (profilePackage_of_meanSquareConvergent
        μ K S h_length fTrue c p b q Rtikh η alphaL
        h_standing h_tikhonov h_ms).u =
      fun n ↦
        alphaL n * expectedSolutionSq μ K Rtikh fTrue η n (alphaL n) /
          expectedResidualSq μ K Rtikh fTrue η n (alphaL n) := sorry

end

end TikhonovExpectedCurve
