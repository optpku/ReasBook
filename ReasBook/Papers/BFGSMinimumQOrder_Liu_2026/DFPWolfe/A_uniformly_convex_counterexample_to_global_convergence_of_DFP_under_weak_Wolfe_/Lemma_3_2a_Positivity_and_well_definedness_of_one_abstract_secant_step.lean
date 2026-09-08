module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_3_2_Abstract_secant_step_with_prescribed_line_ratio_Step

open scoped Matrix

namespace DFP.AbstractSecantStep

universe u

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (1):
the gradient energy `gᵀHg` is strictly positive. -/
#check (DFP.AbstractSecantStep.gradientEnergy_pos :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    0 < z.gradient ⬝ᵥ (z.inverseHessian *ᵥ z.gradient))

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (2):
the preconditioned energy `(Hg)ᵀA(Hg)` is strictly positive. -/
#check (DFP.AbstractSecantStep.preconditionedEnergy_pos :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    0 < z.preconditionedGradient ⬝ᵥ
      (z.secantMatrix *ᵥ z.preconditionedGradient))

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (3):
the prescribed step length `α` is strictly positive. -/
#check (DFP.AbstractSecantStep.stepLength_pos :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n), 0 < z.stepLength)

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (4):
the predicted decrease `q = -(g ⬝ᵥ s)` is strictly positive. -/
#check (DFP.AbstractSecantStep.predictedDecrease_pos :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n), 0 < z.predictedDecrease)

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (5):
the secant curvature `t = s ⬝ᵥ y` is strictly positive. -/
#check (DFP.AbstractSecantStep.secantCurvature_pos :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n), 0 < z.secantCurvature)

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (6):
the secant-image energy `(AHg)ᵀH(AHg)` is strictly positive. -/
#check (DFP.AbstractSecantStep.secantImageEnergy_pos :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    0 < (z.secantMatrix *ᵥ z.preconditionedGradient) ⬝ᵥ
      (z.inverseHessian *ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient)))

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (7):
the displacement `s` is nonzero. -/
#check (DFP.AbstractSecantStep.displacement_ne_zero :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n), z.displacement ≠ 0)

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (8):
the gradient change `y` is nonzero. -/
#check (DFP.AbstractSecantStep.gradientChange_ne_zero :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n), z.gradientChange ≠ 0)

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (9):
the inverse-Hessian energy `yᵀHy` is strictly positive. -/
#check (DFP.AbstractSecantStep.gradientChangeEnergy_pos :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    0 < z.gradientChange ⬝ᵥ (z.inverseHessian *ᵥ z.gradientChange))

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (10):
the denominator `(Hg)ᵀA(Hg)` in the abstract step is nonzero. -/
#check (DFP.AbstractSecantStep.stepLengthDenominator_ne_zero :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    z.preconditionedGradient ⬝ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient) ≠ 0)

/- Lemma 3.2a (Positivity and well-definedness of one abstract secant step) (11):
both scalar denominators in the inverse-form DFP update are nonzero. -/
#check (DFP.AbstractSecantStep.dfpDenominators_ne_zero :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    z.gradientChange ⬝ᵥ (z.inverseHessian *ᵥ z.gradientChange) ≠ 0 ∧
      z.displacement ⬝ᵥ z.gradientChange ≠ 0)

end DFP.AbstractSecantStep
