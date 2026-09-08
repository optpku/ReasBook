module

public import ReasLib.Optimization.DFP.AbstractSecantStep
public import ReasLib.Optimization.DFP.InverseUpdate.OrthogonalTransport
import Mathlib.Tactic.Abel

/-!
# Orthogonal transport of abstract DFP secant steps

These lemmas transport the normalized displacement, gradient change, and
inverse-Hessian recurrence of an abstract secant step into physical Euclidean
coordinates.
-/

public section

open scoped Matrix

namespace DFP.AbstractSecantStep

/-- Transporting an abstract displacement by an orthogonal frame gives the
physical inverse-Hessian search step for the conjugated metric and transported
gradient. -/
theorem transportedDisplacement_eq_step
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : DFP.AbstractSecantStep n) (R : Matrix n n ℝ)
    (hR : R ∈ Matrix.orthogonalGroup n ℝ) :
    WithLp.toLp 2 (R *ᵥ z.displacement) =
      z.stepLength •
        (-WithLp.toLp 2
          ((R * z.inverseHessian * R.transpose) *ᵥ
            WithLp.ofLp (WithLp.toLp 2 (R *ᵥ z.gradient)))) := by
  rw [z.displacement_def, z.preconditionedGradient_def]
  simp only [Matrix.mulVec_neg, Matrix.mulVec_smul, WithLp.toLp_neg,
    WithLp.toLp_smul]
  rw [Matrix.conjugate_mulVec_of_mem_orthogonalGroup
    R z.inverseHessian hR z.gradient]
  rw [smul_neg]

/-- Transporting the difference of the next and current gradients gives the
transport of the abstract gradient change. -/
theorem transportedGradientChange
    {n : Type*} [Fintype n]
    (z : DFP.AbstractSecantStep n) (R : Matrix n n ℝ) :
    WithLp.ofLp
        (WithLp.toLp 2 (R *ᵥ z.nextGradient) -
          WithLp.toLp 2 (R *ᵥ z.gradient)) =
      R *ᵥ z.gradientChange := by
  simp only [WithLp.ofLp_sub]
  rw [z.nextGradient_def, Matrix.mulVec_add]
  abel

/-- Coordinate identifications with one orthogonally transported abstract
secant step imply the physical point and inverse-Hessian DFP recurrences. -/
theorem recurrences_of_orthogonalTransport
    {n : Type*} [Fintype n] [DecidableEq n]
    (z : DFP.AbstractSecantStep n) (R : Matrix n n ℝ)
    (hR : R ∈ Matrix.orthogonalGroup n ℝ)
    (x₀ x₁ g₀ g₁ : EuclideanSpace ℝ n)
    (H₀ H₁ : Matrix n n ℝ) (α : ℝ)
    (hα : α = z.stepLength)
    (hx₁ : x₁ = x₀ + WithLp.toLp 2 (R *ᵥ z.displacement))
    (hg₀ : g₀ = WithLp.toLp 2 (R *ᵥ z.gradient))
    (hg₁ : g₁ = WithLp.toLp 2 (R *ᵥ z.nextGradient))
    (hH₀ : H₀ = R * z.inverseHessian * R.transpose)
    (hH₁ : H₁ = R * z.nextInverseHessian * R.transpose) :
    x₁ = x₀ + α • (-WithLp.toLp 2 (H₀ *ᵥ WithLp.ofLp g₀)) ∧
      H₁ = Matrix.inverseDFPUpdate H₀
        (WithLp.ofLp (α • (-WithLp.toLp 2 (H₀ *ᵥ WithLp.ofLp g₀))))
        (WithLp.ofLp (g₁ - g₀)) := by
  constructor
  · rw [hx₁, hα, hH₀, hg₀]
    rw [← z.transportedDisplacement_eq_step R hR]
  · rw [hH₁, z.nextInverseHessian_def, hH₀, hg₀, hg₁, hα]
    rw [← z.transportedDisplacement_eq_step R hR]
    rw [z.transportedGradientChange R]
    exact Matrix.inverseDFPUpdate_conjugate_of_mem_orthogonalGroup
      R z.inverseHessian z.displacement z.gradientChange
      hR z.inverseHessian_posDef.isHermitian

end DFP.AbstractSecantStep
