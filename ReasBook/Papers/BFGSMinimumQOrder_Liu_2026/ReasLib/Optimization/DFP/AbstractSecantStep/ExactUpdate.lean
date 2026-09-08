module

public import ReasLib.Optimization.DFP.AbstractSecantStep
public import ReasLib.Optimization.DFP.InverseUpdate.Scaling

public section

open scoped Matrix

namespace DFP.AbstractSecantStep

/-- The displacement is the preconditioned gradient scaled by the negative step length. -/
private lemma displacement_eq_neg_smul_preconditionedGradient {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) :
    z.displacement = (-z.stepLength) • z.preconditionedGradient := by
  -- Put the defining outer negation into the common scalar used by both secant vectors.
  rw [z.displacement_def, neg_smul]

/-- The gradient change is the secant image scaled by the negative step length. -/
private lemma gradientChange_eq_neg_smul_secantImage {n : Type u} [Fintype n]
    (z : AbstractSecantStep n) :
    z.gradientChange =
      (-z.stepLength) • (z.secantMatrix *ᵥ z.preconditionedGradient) := by
  -- Substitute the displacement normalization and pull its scalar through the matrix action.
  rw [z.gradientChange_def, displacement_eq_neg_smul_preconditionedGradient,
    Matrix.mulVec_smul]

/-- Writing `v = Hg`, `w = Av`, `β = vᵀw`, and `γ = wᵀHw`, the next
inverse-Hessian matrix has the exact rank-two DFP formula. -/
theorem nextInverseHessian_formula {n : Type u} [Fintype n] (z : AbstractSecantStep n) :
    let v := z.preconditionedGradient
    let w := z.secantMatrix *ᵥ v
    let β := v ⬝ᵥ w
    let γ := w ⬝ᵥ (z.inverseHessian *ᵥ w)
    z.nextInverseHessian =
      z.inverseHessian -
        γ⁻¹ • Matrix.vecMulVec (z.inverseHessian *ᵥ w) (w ᵥ* z.inverseHessian) +
        β⁻¹ • Matrix.vecMulVec v v := by
  dsimp
  have hscale : -z.stepLength ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt z.stepLength_pos)
  -- Normalize both secant vectors to the same nonzero scale, then cancel that scale.
  calc
    z.nextInverseHessian =
        Matrix.inverseDFPUpdate z.inverseHessian z.displacement z.gradientChange :=
      z.nextInverseHessian_def
    _ = Matrix.inverseDFPUpdate z.inverseHessian
        ((-z.stepLength) • z.preconditionedGradient)
        ((-z.stepLength) • (z.secantMatrix *ᵥ z.preconditionedGradient)) := by
      rw [displacement_eq_neg_smul_preconditionedGradient,
        gradientChange_eq_neg_smul_secantImage]
    _ = Matrix.inverseDFPUpdate z.inverseHessian z.preconditionedGradient
        (z.secantMatrix *ᵥ z.preconditionedGradient) :=
      Matrix.inverseDFPUpdate_smul_pair _ _ _ hscale
    _ = z.inverseHessian -
        ((z.secantMatrix *ᵥ z.preconditionedGradient) ⬝ᵥ
          (z.inverseHessian *ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient)))⁻¹ •
          Matrix.vecMulVec
            (z.inverseHessian *ᵥ (z.secantMatrix *ᵥ z.preconditionedGradient))
            ((z.secantMatrix *ᵥ z.preconditionedGradient) ᵥ* z.inverseHessian) +
        (z.preconditionedGradient ⬝ᵥ
          (z.secantMatrix *ᵥ z.preconditionedGradient))⁻¹ •
          Matrix.vecMulVec z.preconditionedGradient z.preconditionedGradient := by
      -- Route correction: use the public entrywise API because the imported definition is opaque.
      ext i j
      simp only [Matrix.inverseDFPUpdate_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]

/-- Abstract secant steps with the same inverse Hessian, gradient, and secant
matrix have the same next inverse-Hessian matrix, independently of their positive scales. -/
theorem nextInverseHessian_tau_independent {n : Type u} [Fintype n]
    (z₁ z₂ : AbstractSecantStep n)
    (hH : z₁.inverseHessian = z₂.inverseHessian)
    (hg : z₁.gradient = z₂.gradient)
    (hA : z₁.secantMatrix = z₂.secantMatrix) :
    z₁.nextInverseHessian = z₂.nextInverseHessian := by
  -- Replace each update by the scale-free formula and identify its three input data.
  rw [z₁.nextInverseHessian_formula, z₂.nextInverseHessian_formula]
  simp only [preconditionedGradient_def, hH, hg, hA]

end DFP.AbstractSecantStep
