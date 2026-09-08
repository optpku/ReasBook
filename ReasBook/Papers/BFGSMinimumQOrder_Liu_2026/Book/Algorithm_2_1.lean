module

import Book.Algorithm_2_1_QuasiNewton

section

variable {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
variable (x : EuclideanSpace ℝ (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ)
variable (s y : EuclideanSpace ℝ (Fin n)) (φ : ℝ)

/- Algorithm 2.1 (1): differentiability, the positive-definite Hessian approximation,
the inverse-Hessian search direction, and an explicit exact-line-search choice. -/
#check (BFGS.Step F x B)
#check BFGS.searchDirection_spec
#check LineSearch.isExact_iff

/- Algorithm 2.1 (2): the next iterate, displacement, and gradient change. -/
#check BFGS.Step.nextPoint
#check BFGS.Step.displacement
#check BFGS.Step.gradientChange

/- Algorithm 2.1 (3): the Hessian-form BFGS update formula. -/
#check (BFGS.update B s y)
#check BFGS.update_def

/- Algorithm 2.1 (4): positive curvature makes the BFGS update well defined and
positive definite. -/
#check BFGS.quadraticDenominator_pos
#check BFGS.update_posDef

/- Algorithm 2.1 (5): the Hessian-form DFP update formula. -/
#check (DFP.update B s y)
#check DFP.update_def

/- Algorithm 2.1 (6): the DFP endpoint preserves positive definiteness under
positive curvature. -/
#check DFP.update_secant
#check DFP.update_posDef

/- Algorithm 2.1 (7): the convex Broyden interpolation with explicit parameter `φ`. -/
#check (Broyden.update φ B s y)
#check Broyden.update_def

/- Algorithm 2.1 (8): both endpoints and every interpolation with `φ ∈ Set.Icc 0 1`
are positive definite under positive curvature. -/
#check Broyden.update_zero
#check Broyden.update_one
#check Broyden.update_posDef

end
