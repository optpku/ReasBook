module

public import ReasLib.Optimization.DFP.InverseUpdate

public section

noncomputable section

open scoped Matrix

namespace DFP

/-- The valid inputs for one abstract secant step of the inverse-form DFP method. -/
structure AbstractSecantStep (n : Type u) [Fintype n] where
  inverseHessian : Matrix n n ℝ
  gradient : n → ℝ
  secantMatrix : Matrix n n ℝ
  tau : ℝ
  inverseHessian_posDef : inverseHessian.PosDef
  secantMatrix_posDef : secantMatrix.PosDef
  tau_pos : 0 < tau
  gradient_ne_zero : gradient ≠ 0

namespace AbstractSecantStep

/-- Construct an abstract secant step from explicit matrices, a gradient, a ratio,
and their validity certificates. -/
def ofMatrices {n : Type u} [Fintype n] (H : Matrix n n ℝ) (g : n → ℝ)
    (A : Matrix n n ℝ) (τ : ℝ) (hH : H.PosDef) (hA : A.PosDef) (hτ : 0 < τ)
    (hg : g ≠ 0) : AbstractSecantStep n where
  inverseHessian := H
  gradient := g
  secantMatrix := A
  tau := τ
  inverseHessian_posDef := hH
  secantMatrix_posDef := hA
  tau_pos := hτ
  gradient_ne_zero := hg

/-- The preconditioned gradient `H *ᵥ g`. -/
def preconditionedGradient {n : Type u} [Fintype n] (z : AbstractSecantStep n) : n → ℝ :=
  z.inverseHessian *ᵥ z.gradient

/-- The prescribed step length
`τ * (g ⬝ᵥ H *ᵥ g) / ((H *ᵥ g) ⬝ᵥ A *ᵥ (H *ᵥ g))`. -/
def stepLength {n : Type u} [Fintype n] (z : AbstractSecantStep n) : ℝ :=
  z.tau * (z.gradient ⬝ᵥ (z.inverseHessian *ᵥ z.gradient)) /
    ((z.inverseHessian *ᵥ z.gradient) ⬝ᵥ
      (z.secantMatrix *ᵥ (z.inverseHessian *ᵥ z.gradient)))

/-- The displacement `s = -α H *ᵥ g`. -/
def displacement {n : Type u} [Fintype n] (z : AbstractSecantStep n) : n → ℝ :=
  -(z.stepLength • z.preconditionedGradient)

/-- The abstract secant gradient change `y = A *ᵥ s`. -/
def gradientChange {n : Type u} [Fintype n] (z : AbstractSecantStep n) : n → ℝ :=
  z.secantMatrix *ᵥ z.displacement

/-- The next gradient `g₊ = g + y`. -/
def nextGradient {n : Type u} [Fintype n] (z : AbstractSecantStep n) : n → ℝ :=
  z.gradient + z.gradientChange

/-- The next inverse-Hessian approximation given by the inverse-form DFP update. -/
def nextInverseHessian {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    Matrix n n ℝ :=
  Matrix.inverseDFPUpdate z.inverseHessian z.displacement z.gradientChange

/-- The predicted decrease `q = -(g ⬝ᵥ s)`. -/
def predictedDecrease {n : Type u} [Fintype n] (z : AbstractSecantStep n) : ℝ :=
  -(z.gradient ⬝ᵥ z.displacement)

/-- The secant curvature `t = s ⬝ᵥ y`. -/
def secantCurvature {n : Type u} [Fintype n] (z : AbstractSecantStep n) : ℝ :=
  z.displacement ⬝ᵥ z.gradientChange

/-- The preconditioned gradient is obtained by multiplying the gradient by `H`. -/
theorem preconditionedGradient_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.preconditionedGradient = z.inverseHessian *ᵥ z.gradient := by
  -- Unfolding the preconditioned gradient exposes the defining matrix-vector product.
  rfl

/-- The step length has the prescribed positive-curvature quotient formula. -/
theorem stepLength_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.stepLength = z.tau * (z.gradient ⬝ᵥ (z.inverseHessian *ᵥ z.gradient)) /
      ((z.inverseHessian *ᵥ z.gradient) ⬝ᵥ
        (z.secantMatrix *ᵥ (z.inverseHessian *ᵥ z.gradient))) := by
  -- This is the quotient used in the construction of the step.
  rfl

/-- The displacement is the negative scaled preconditioned gradient. -/
theorem displacement_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.displacement = -(z.stepLength • z.preconditionedGradient) := by
  -- The displacement equation is the defining scaling relation.
  rfl

/-- The gradient change is the abstract secant matrix applied to the displacement. -/
theorem gradientChange_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.gradientChange = z.secantMatrix *ᵥ z.displacement := by
  -- The secant matrix defines the gradient change.
  rfl

/-- The next gradient is the current gradient plus the secant change. -/
theorem nextGradient_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.nextGradient = z.gradient + z.gradientChange := by
  -- The next gradient is defined by adding the secant change.
  rfl

/-- Writing `v = H *ᵥ g`, `δ = g ⬝ᵥ v`, `w = A *ᵥ v`, and `β = v ⬝ᵥ w`,
the next gradient is `g - (τ * δ / β) • w`. -/
theorem nextGradient_formula {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    let v := z.preconditionedGradient
    let δ := z.gradient ⬝ᵥ v
    let w := z.secantMatrix *ᵥ v
    let β := v ⬝ᵥ w
    z.nextGradient = z.gradient - (z.tau * δ / β) • w := by
  -- Expose the update equations and the common preconditioned-gradient expression.
  dsimp only
  rw [z.nextGradient_def, z.gradientChange_def, z.displacement_def,
    z.stepLength_def, z.preconditionedGradient_def]
  -- Linearity of matrix-vector multiplication turns the secant change into the
  -- negative scalar multiple appearing in the claimed subtraction.
  simp only [Matrix.mulVec_neg, Matrix.mulVec_smul, sub_eq_add_neg]

/-- The next inverse-Hessian approximation is the inverse-form DFP update. -/
theorem nextInverseHessian_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.nextInverseHessian =
      Matrix.inverseDFPUpdate z.inverseHessian z.displacement z.gradientChange := by
  -- The next matrix is definitionally the inverse-form DFP update.
  rfl

/-- The predicted decrease is the negative gradient-displacement pairing. -/
theorem predictedDecrease_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.predictedDecrease = -(z.gradient ⬝ᵥ z.displacement) := by
  -- The predicted decrease is the negated gradient-displacement pairing.
  rfl

/-- The secant curvature is the displacement-gradient-change pairing. -/
theorem secantCurvature_def {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.secantCurvature = z.displacement ⬝ᵥ z.gradientChange := by
  -- The secant curvature is its defining dot product.
  rfl

/-- The gradient has strictly positive energy with respect to the inverse-Hessian matrix. -/
theorem gradientEnergy_pos {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    0 < z.gradient ⬝ᵥ (z.inverseHessian *ᵥ z.gradient) := by
  -- Positive definiteness is strict on the nonzero gradient.
  simpa using z.inverseHessian_posDef.dotProduct_mulVec_pos z.gradient_ne_zero

/-- The preconditioned gradient has strictly positive energy with respect to the secant
matrix. -/
theorem preconditionedEnergy_pos {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    0 < z.preconditionedGradient ⬝ᵥ
      (z.secantMatrix *ᵥ z.preconditionedGradient) := by
  have hpreconditioned : z.preconditionedGradient ≠ 0 := by
    intro hzero
    have hpositive := z.gradientEnergy_pos
    rw [← z.preconditionedGradient_def, hzero, dotProduct_zero] at hpositive
    exact (lt_irrefl 0 hpositive)
  -- Apply positive definiteness of the secant matrix to `H *ᵥ g`.
  simpa using z.secantMatrix_posDef.dotProduct_mulVec_pos hpreconditioned

/-- The prescribed step length is strictly positive. -/
theorem stepLength_pos {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    0 < z.stepLength := by
  rw [z.stepLength_def, ← z.preconditionedGradient_def]
  -- Both the numerator and denominator of the prescribed quotient are positive.
  exact div_pos (mul_pos z.tau_pos z.gradientEnergy_pos) z.preconditionedEnergy_pos

/-- The displacement produced by an abstract secant step is nonzero. -/
theorem displacement_ne_zero {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.displacement ≠ 0 := by
  have hpreconditioned : z.preconditionedGradient ≠ 0 := by
    intro hzero
    have hpositive := z.gradientEnergy_pos
    rw [← z.preconditionedGradient_def, hzero, dotProduct_zero] at hpositive
    exact (lt_irrefl 0 hpositive)
  rw [z.displacement_def]
  -- A nonzero scalar multiple of the preconditioned gradient remains nonzero.
  exact neg_ne_zero.mpr (smul_ne_zero (ne_of_gt z.stepLength_pos) hpreconditioned)

/-- The gradient change produced by an abstract secant step is nonzero. -/
theorem gradientChange_ne_zero {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.gradientChange ≠ 0 := by
  intro hzero
  have hpositive := z.secantMatrix_posDef.dotProduct_mulVec_pos z.displacement_ne_zero
  -- A zero secant image would contradict strict positivity on the displacement.
  rw [← z.gradientChange_def, hzero, dotProduct_zero] at hpositive
  exact (lt_irrefl 0 hpositive)

/-- The secant image of the preconditioned gradient has strictly positive energy with
respect to the inverse-Hessian matrix. -/
theorem secantImageEnergy_pos {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    0 < (z.secantMatrix *ᵥ z.preconditionedGradient) ⬝ᵥ
      (z.inverseHessian *ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient)) := by
  have himage : z.secantMatrix *ᵥ z.preconditionedGradient ≠ 0 := by
    intro hzero
    have hpositive := z.preconditionedEnergy_pos
    rw [hzero, dotProduct_zero] at hpositive
    exact (lt_irrefl 0 hpositive)
  -- The secant image is nonzero, so its inverse-Hessian energy is positive.
  simpa using z.inverseHessian_posDef.dotProduct_mulVec_pos himage

/-- The gradient change has strictly positive energy with respect to the inverse-Hessian
matrix. -/
theorem gradientChangeEnergy_pos {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    0 < z.gradientChange ⬝ᵥ (z.inverseHessian *ᵥ z.gradientChange) := by
  -- Positive definiteness is strict on the nonzero gradient change.
  simpa using z.inverseHessian_posDef.dotProduct_mulVec_pos z.gradientChange_ne_zero

/-- The preconditioned-gradient energy occurring in the step-length denominator is
nonzero. -/
theorem stepLengthDenominator_ne_zero {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) :
    z.preconditionedGradient ⬝ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient) ≠ 0 := by
  -- Strict positivity excludes a zero denominator.
  exact ne_of_gt z.preconditionedEnergy_pos

/-- The abstract secant step has positive predicted decrease. -/
theorem predictedDecrease_pos {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    0 < z.predictedDecrease := by
  rw [z.predictedDecrease_def, z.displacement_def, z.preconditionedGradient_def]
  simp only [dotProduct_neg, dotProduct_smul, smul_eq_mul, neg_neg]
  -- The decrease is the product of the positive step length and gradient energy.
  exact mul_pos z.stepLength_pos z.gradientEnergy_pos

/-- The abstract secant pair has positive curvature. -/
theorem secantCurvature_pos {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    0 < z.secantCurvature := by
  rw [z.secantCurvature_def, z.gradientChange_def]
  -- Positive definiteness of the secant matrix controls the nonzero displacement.
  simpa using z.secantMatrix_posDef.dotProduct_mulVec_pos z.displacement_ne_zero

/-- Both scalar denominators in the inverse-form DFP update of an abstract secant step
are nonzero. -/
theorem dfpDenominators_ne_zero {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.gradientChange ⬝ᵥ (z.inverseHessian *ᵥ z.gradientChange) ≠ 0 ∧
      z.displacement ⬝ᵥ z.gradientChange ≠ 0 := by
  -- Both DFP denominators are strictly positive.
  exact ⟨ne_of_gt z.gradientChangeEnergy_pos, ne_of_gt z.secantCurvature_pos⟩

/-- The constructed secant curvature has the prescribed ratio to predicted decrease. -/
theorem lineRatio {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.secantCurvature / z.predictedDecrease = z.tau := by
  have hdecrease : z.predictedDecrease =
      z.stepLength * (z.gradient ⬝ᵥ (z.inverseHessian *ᵥ z.gradient)) := by
    rw [z.predictedDecrease_def, z.displacement_def, z.preconditionedGradient_def]
    simp only [dotProduct_neg, dotProduct_smul, smul_eq_mul, neg_neg]
  have hcurvature : z.secantCurvature = z.stepLength ^ 2 *
      (z.preconditionedGradient ⬝ᵥ
        (z.secantMatrix *ᵥ z.preconditionedGradient)) := by
    rw [z.secantCurvature_def, z.gradientChange_def, z.displacement_def]
    simp only [Matrix.mulVec_neg, Matrix.mulVec_smul, neg_dotProduct_neg,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two]
    ring
  have hstep : z.stepLength *
      (z.preconditionedGradient ⬝ᵥ
        (z.secantMatrix *ᵥ z.preconditionedGradient)) =
      z.tau * (z.gradient ⬝ᵥ (z.inverseHessian *ᵥ z.gradient)) := by
    rw [z.stepLength_def, ← z.preconditionedGradient_def]
    field_simp [ne_of_gt z.preconditionedEnergy_pos]
  -- Cancel the positive step length and gradient energy, then use its defining quotient.
  rw [hcurvature, hdecrease]
  field_simp [ne_of_gt z.stepLength_pos, ne_of_gt z.gradientEnergy_pos]
  simpa [mul_comm] using hstep

/-- The inverse-form DFP update of an abstract secant step remains positive definite. -/
theorem nextInverseHessian_posDef {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    z.nextInverseHessian.PosDef := by
  rw [z.nextInverseHessian_def]
  -- Positive secant curvature is exactly the hypothesis needed by the DFP update theorem.
  exact z.inverseHessian_posDef.inverseDFPUpdate z.secantCurvature_pos

end AbstractSecantStep

end DFP
