/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_4.Curve
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7.OptimalFamily
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError

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
variable (fTrue : H) (η : ℕ → Ω → F)

/-- The expected residual energy `(7.105)` of the expected Tikhonov L-curve,
written as the expectation of the squared residual norm at data size `n` and
parameter `α`. -/
@[expose] def expectedResidualSq : ℕ → ℝ → ℝ :=
  fun n α ↦
    ∫ ω, ‖K n (Rtikh n α (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 ∂μ

/-- The defining evaluation rule for `expectedResidualSq`. -/
theorem expectedResidualSq_apply (n : ℕ) (α : ℝ) :
    expectedResidualSq μ K Rtikh fTrue η n α =
      ∫ ω, ‖K n (Rtikh n α (K n fTrue + η n ω)) - (K n fTrue + η n ω)‖ ^ 2 ∂μ := by
  -- Expose the owner wrapper once to recover the defining integral.
  rfl

/-- The expected solution energy `(7.106)` of the expected Tikhonov L-curve,
written as the expectation of the squared reconstruction norm at data size `n`
and parameter `α`. -/
@[expose] def expectedSolutionSq : ℕ → ℝ → ℝ :=
  fun n α ↦
    ∫ ω, ‖Rtikh n α (K n fTrue + η n ω)‖ ^ 2 ∂μ

/-- The defining evaluation rule for `expectedSolutionSq`. -/
theorem expectedSolutionSq_apply (n : ℕ) (α : ℝ) :
    expectedSolutionSq μ K Rtikh fTrue η n α =
      ∫ ω, ‖Rtikh n α (K n fTrue + η n ω)‖ ^ 2 ∂μ := by
  -- Expose the owner wrapper once to recover the defining integral.
  rfl

/-- The expected Tikhonov L-curve curvature obtained by applying
`LCurve.curvatureFromEnergies` to the expected residual and solution energies. -/
@[expose] def expectedCurvature : ℕ → ℝ → ℝ :=
  fun n α ↦
    LCurve.curvatureFromEnergies
      (expectedResidualSq μ K Rtikh fTrue η n)
      (expectedSolutionSq μ K Rtikh fTrue η n) α

/-- The defining evaluation rule for `expectedCurvature`. -/
theorem expectedCurvature_apply (n : ℕ) (α : ℝ) :
    expectedCurvature μ K Rtikh fTrue η n α =
      LCurve.curvatureFromEnergies
        (expectedResidualSq μ K Rtikh fTrue η n)
        (expectedSolutionSq μ K Rtikh fTrue η n) α := by
  -- Expose the curvature owner once before rewriting through the energy API.
  rfl

/-- Minimizing the negated expected curvature on `Set.Ioi 0` is equivalent to
choosing a corner parameter of the expected Tikhonov L-curve at each index. -/
theorem cornerFamily_iff (alphaL : ℕ → ℝ) :
    ParameterChoice.IsOptimalParameterFamily
        (fun n α ↦ -(expectedCurvature μ K Rtikh fTrue η n α))
        (fun _ ↦ Set.Ioi (0 : ℝ)) alphaL ↔
      ∀ n, LCurve.IsCornerParameter (expectedCurvature μ K Rtikh fTrue η n) (alphaL n) := by
  constructor
  · intro h_corner n
    -- Rewrite the optimal-family owner to the pointwise minimizer relation.
    rw [ParameterChoice.isOptimalParameterFamily_iff] at h_corner
    rw [LCurve.IsCornerParameter_iff, isMaxOn_iff]
    intro β hβ
    -- Convert minimizing `-κ` into maximizing `κ` by negating the comparison.
    exact neg_le_neg_iff.mp ((isMinOn_iff.mp (h_corner n)) β hβ)
  · intro h_corner
    -- Repackage the pointwise corner maximizers as the optimal family for `-κ`.
    rw [ParameterChoice.isOptimalParameterFamily_iff]
    intro n
    rw [isMinOn_iff]
    intro β hβ
    -- Negating the pointwise maximality inequality gives the minimizer inequality.
    exact
      neg_le_neg_iff.mpr
        ((isMaxOn_iff.mp ((LCurve.IsCornerParameter_iff _ _).mp (h_corner n))) β hβ)

end

end TikhonovExpectedCurve
