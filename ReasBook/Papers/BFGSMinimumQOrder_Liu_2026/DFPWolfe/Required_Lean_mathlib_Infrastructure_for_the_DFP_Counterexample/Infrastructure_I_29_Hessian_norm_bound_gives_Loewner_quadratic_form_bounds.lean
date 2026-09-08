module

public import ReasLib.Analysis.Calculus.EuclideanPlaneHessian

public section

open scoped Matrix

universe u

/- Infrastructure I.29 (Hessian norm bound gives Loewner quadratic-form bounds) (1):
a continuous linear endomorphism whose norm is at most `η` has quadratic form
between `-η * ‖v‖ ^ 2` and `η * ‖v‖ ^ 2`. -/
#check (ContinuousLinearMap.inner_apply_bounds_of_norm_le :
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : E →L[ℝ] E) (η : ℝ) (h_norm : ‖B‖ ≤ η) (v : E),
    -η * ‖v‖ ^ 2 ≤ inner ℝ (B v) v ∧ inner ℝ (B v) v ≤ η * ‖v‖ ^ 2)

/- Infrastructure I.29 (Hessian norm bound gives Loewner quadratic-form bounds) (2):
for `f(x) = (1 / 2) * ‖x - C‖ ^ 2 + Ψ x`, a norm bound on the Hessian of `Ψ` places the
Hessian matrix of `f` between `(1 - η)I` and `(1 + η)I` in Loewner order. -/
#check (EuclideanPlane.hessianMatrix_sqNorm_add_bounds_of_norm_le :
  ∀ (C : EuclideanSpace ℝ (Fin 2)) (Ψ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) (η : ℝ) (hΨ : ContDiffAt ℝ 2 Ψ z)
    (h_norm : ‖EuclideanPlane.hessian Ψ z‖ ≤ η),
    (EuclideanPlane.hessianMatrix (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x) z -
      (1 - η) • 1).PosSemidef ∧
    ((1 + η) • 1 -
      EuclideanPlane.hessianMatrix
        (fun x ↦ (1 / 2 : ℝ) * ‖x - C‖ ^ 2 + Ψ x) z).PosSemidef)
