module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_3_2_Abstract_secant_step_with_prescribed_line_ratio_Step

open scoped Matrix

section

variable {n : Type u} [Fintype n]

/- Definition 3.2 (Abstract secant step with prescribed line ratio).
For positive-definite `H` and `A`, a nonzero `g`, and `τ > 0`, the constructor
determines the abstract secant step. The matrix `A` prescribes a positive-curvature
secant pair and is not asserted to be a Hessian of the eventual objective. -/
#check (DFP.AbstractSecantStep.ofMatrices :
  (H : Matrix n n ℝ) → (g : n → ℝ) → (A : Matrix n n ℝ) → (τ : ℝ) →
    H.PosDef → A.PosDef → 0 < τ → g ≠ 0 → DFP.AbstractSecantStep n)

#check (DFP.AbstractSecantStep.preconditionedGradient_def :
  (z : DFP.AbstractSecantStep n) →
    z.preconditionedGradient = z.inverseHessian *ᵥ z.gradient)

#check (DFP.AbstractSecantStep.stepLength_def :
  (z : DFP.AbstractSecantStep n) →
    z.stepLength = z.tau * (z.gradient ⬝ᵥ (z.inverseHessian *ᵥ z.gradient)) /
      ((z.inverseHessian *ᵥ z.gradient) ⬝ᵥ
        (z.secantMatrix *ᵥ (z.inverseHessian *ᵥ z.gradient))))

#check (DFP.AbstractSecantStep.displacement_def :
  (z : DFP.AbstractSecantStep n) →
    z.displacement = -(z.stepLength • z.preconditionedGradient))

#check (DFP.AbstractSecantStep.gradientChange_def :
  (z : DFP.AbstractSecantStep n) →
    z.gradientChange = z.secantMatrix *ᵥ z.displacement)

#check (DFP.AbstractSecantStep.nextGradient_def :
  (z : DFP.AbstractSecantStep n) → z.nextGradient = z.gradient + z.gradientChange)

#check (DFP.AbstractSecantStep.nextInverseHessian_def :
  (z : DFP.AbstractSecantStep n) → z.nextInverseHessian =
    Matrix.inverseDFPUpdate z.inverseHessian z.displacement z.gradientChange)

#check (DFP.AbstractSecantStep.predictedDecrease_def :
  (z : DFP.AbstractSecantStep n) →
    z.predictedDecrease = -(z.gradient ⬝ᵥ z.displacement))

#check (DFP.AbstractSecantStep.secantCurvature_def :
  (z : DFP.AbstractSecantStep n) →
    z.secantCurvature = z.displacement ⬝ᵥ z.gradientChange)

#check (DFP.AbstractSecantStep.predictedDecrease_pos :
  (z : DFP.AbstractSecantStep n) → 0 < z.predictedDecrease)

#check (DFP.AbstractSecantStep.secantCurvature_pos :
  (z : DFP.AbstractSecantStep n) → 0 < z.secantCurvature)

#check (DFP.AbstractSecantStep.lineRatio :
  (z : DFP.AbstractSecantStep n) → z.secantCurvature / z.predictedDecrease = z.tau)

#check (DFP.AbstractSecantStep.nextInverseHessian_posDef :
  (z : DFP.AbstractSecantStep n) → z.nextInverseHessian.PosDef)

end
