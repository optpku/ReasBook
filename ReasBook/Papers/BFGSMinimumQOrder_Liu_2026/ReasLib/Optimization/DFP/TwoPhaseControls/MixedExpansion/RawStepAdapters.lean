module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.AbstractSecantStep
import all ReasLib.Optimization.DFP.TwoPhaseControls

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.Mixed

/-- The first independent-radius raw step is the
    normalized first-step metric and gradient once its secant-step side conditions
    are supplied. -/
theorem independentRawStep_first_eq
    (b r p h : ℝ) (hH : (Matrix.diagonal ![h * p * r ^ 2, h] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef)
    (hA : (TwoPhaseControls.first b).matrix.PosDef)
    (hτ : 0 < (TwoPhaseControls.first b).tau)
    (hg : (![(1 : ℝ), p * r] : Fin 2 → ℝ) ≠ 0)
    (hr : r ≠ 0) :
    independentRawStep (Matrix.diagonal ![h * p * r ^ 2, h])
        ![(1 : ℝ), p * r] (TwoPhaseControls.first b) =
      (independentFirstMetric b r p h, independentFirstGradient b r p) := by
  let z := DFP.AbstractSecantStep.ofMatrices
    (Matrix.diagonal ![h * p * r ^ 2, h]) ![(1 : ℝ), p * r]
    (TwoPhaseControls.first b).matrix (TwoPhaseControls.first b).tau
    hH hA hτ hg
  have hraw : independentRawStep (Matrix.diagonal ![h * p * r ^ 2, h])
      ![(1 : ℝ), p * r] (TwoPhaseControls.first b) =
      (z.nextInverseHessian, z.nextGradient) := by
    simp only [independentRawStep, z, AbstractSecantStep.ofMatrices,
      AbstractSecantStep.nextInverseHessian, AbstractSecantStep.nextGradient,
      AbstractSecantStep.gradientChange, AbstractSecantStep.displacement,
      AbstractSecantStep.stepLength, AbstractSecantStep.preconditionedGradient]
  have hHspec : z.inverseHessian = Matrix.diagonal ![h * p * r ^ 2, h] := by
    rfl
  have hgspec : z.gradient = (1 : ℝ) • ![(1 : ℝ), p * r] := by
    change ![(1 : ℝ), p * r] = (1 : ℝ) • ![(1 : ℝ), p * r]
    simp
  have hAspec : z.secantMatrix = (TwoPhaseControls.first b).matrix := by
    rfl
  have hτspec : z.tau = (TwoPhaseControls.first b).tau := by
    rfl
  have hout := independentFirstStep_spec z b r p h 1 hHspec hgspec hAspec hτspec hr
  rw [hraw, hout]
  simp

/-- The second independent-radius raw step is the
    normalized second-step metric and gradient for a diagonal first-leg state. -/
theorem independentRawStep_second_eq
    (b r L H Q U : ℝ) (hG : ℝ)
    (hH : (Matrix.diagonal ![r ^ 2 * L, H] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef)
    (hA : (TwoPhaseControls.second b).matrix.PosDef)
    (hτ : 0 < (TwoPhaseControls.second b).tau)
    (hg : (hG • ![Q, r * U] : Fin 2 → ℝ) ≠ 0)
    (hr : r ≠ 0) :
    independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
        (hG • ![Q, r * U]) (TwoPhaseControls.second b) =
      (independentSecondMetric b r L H Q U,
        hG • independentSecondGradient b r L H Q U) := by
  let z := DFP.AbstractSecantStep.ofMatrices
    (Matrix.diagonal ![r ^ 2 * L, H]) (hG • ![Q, r * U])
    (TwoPhaseControls.second b).matrix (TwoPhaseControls.second b).tau
    hH hA hτ hg
  have hraw : independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
      (hG • ![Q, r * U]) (TwoPhaseControls.second b) =
      (z.nextInverseHessian, z.nextGradient) := by
    simp only [independentRawStep, z, AbstractSecantStep.ofMatrices,
      AbstractSecantStep.nextInverseHessian, AbstractSecantStep.nextGradient,
      AbstractSecantStep.gradientChange, AbstractSecantStep.displacement,
      AbstractSecantStep.stepLength, AbstractSecantStep.preconditionedGradient]
  have hHspec : z.inverseHessian = Matrix.diagonal ![r ^ 2 * L, H] := by
    rfl
  have hgspec : z.gradient = hG • ![Q, r * U] := by
    change (hG • ![Q, r * U] : Fin 2 → ℝ) = hG • ![Q, r * U]
    rfl
  have hAspec : z.secantMatrix = (TwoPhaseControls.second b).matrix := by
    rfl
  have hτspec : z.tau = (TwoPhaseControls.second b).tau := by
    rfl
  have hout := independentSecondStep_spec z b r L H Q U hG hHspec hgspec hAspec hτspec hr
  rw [hraw, hout]

end DFP.TwoLeg.Mixed
