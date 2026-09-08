module

public import ReasLib.Optimization.DFP.AbstractSecantStep

public section

open scoped Matrix

namespace DFP.AbstractSecantStep

/-- The preconditioned gradient of an abstract secant step is nonzero. -/
theorem preconditionedGradient_ne_zero {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) :
    z.preconditionedGradient ≠ 0 := by
  intro hzero
  have hpos := z.gradientEnergy_pos
  rw [← z.preconditionedGradient_def, hzero, dotProduct_zero] at hpos
  exact (lt_irrefl 0 hpos)

/-- The predicted decrease is the step length times the inverse-Hessian energy of the
gradient. -/
theorem predictedDecrease_eq_stepLength_mul_gradientEnergy {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) :
    z.predictedDecrease =
      z.stepLength * (z.gradient ⬝ᵥ (z.inverseHessian *ᵥ z.gradient)) := by
  rw [z.predictedDecrease_def, z.displacement_def, z.preconditionedGradient_def]
  simp only [dotProduct_neg, dotProduct_smul, smul_eq_mul, neg_neg]

/-- The secant curvature is the squared step length times the secant-matrix energy of
the preconditioned gradient. -/
theorem secantCurvature_eq_stepLength_sq_mul_preconditionedEnergy
    {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.secantCurvature = z.stepLength ^ 2 *
      (z.preconditionedGradient ⬝ᵥ
        (z.secantMatrix *ᵥ z.preconditionedGradient)) := by
  rw [z.secantCurvature_def, z.gradientChange_def, z.displacement_def]
  simp only [Matrix.mulVec_neg, Matrix.mulVec_smul, neg_dotProduct_neg,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two]
  ring

/-- The secant curvature is `tau` times the predicted decrease. -/
theorem secantCurvature_eq_tau_mul_predictedDecrease {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) :
    z.secantCurvature = z.tau * z.predictedDecrease := by
  exact (div_eq_iff (ne_of_gt z.predictedDecrease_pos)).mp z.lineRatio

end DFP.AbstractSecantStep
