/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_8_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_9_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open Matrix

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Example 1.8.7 is `source-facing`: it identifies the textbook Newton direction for a quadratic
objective with the displacement to the minimizer, and therefore shows that one Newton step lands
at the minimizer.

Sampled owner-style declarations:
* `NewtonSystem.step` from Algorithm 1.7.1
* `newtonSystem_step_eq_matrixFormula` from Proposition 1.8.2
* `UnconstrainedQuadraticMinimizationProblem.gradient_eq` from Proposition 1.9.11

Best owner abstractions:
* the canonical Newton step `NewtonSystem.step (∇ problem.objective)`
* `UnconstrainedQuadraticMinimizationProblem n` for the quadratic objective data

Primitive data:
* `problem`
* `x`

Derived API:
* the source-facing Newton direction formula
* the source-facing textbook Newton update formula

Source/core/bridge triage:
* source-facing: the Newton direction and the one-step textbook update formula
* core/canonical: the Newton owner `NewtonSystem.step (∇ problem.objective)`
* bridge/view: the quadratic identities `problem.gradient_eq x` and
  `newtonSystem_step_eq_matrixFormula`
-/

namespace UnconstrainedQuadraticMinimizationProblem

private theorem hessian_eq
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    ∇² problem.objective x = problem.A := by
  let A := problem.A.toEuclideanLin
  apply Matrix.toEuclideanLin.injective
  have hgrad :
      fderiv ℝ (∇ problem.objective) x = A.toContinuousLinearMap := by
    have hfun :
        ∇ problem.objective = fun y : E ↦
          A y - A problem.minimizer := by
      funext y
      simpa [LinearMap.map_sub] using problem.gradient_eq y
    rw [hfun]
    simpa [A] using ((A.toContinuousLinearMap.hasFDerivAt).sub_const
      (A problem.minimizer)).fderiv
  calc
    (∇² problem.objective x).toEuclideanLin = hessian problem.objective x := by
      simpa using hessianMatrix_toEuclideanLin problem.objective x
    _ = A := by
      exact congrArg ContinuousLinearMap.toLinearMap hgrad

private theorem hessian_posDef
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    (∇² problem.objective x).PosDef := by
  simpa [hessian_eq problem x] using problem.posDef

private theorem gradient_det_ne_zero
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    (fderiv ℝ (∇ problem.objective) x).det ≠ 0 :=
  hessian_det_ne_zero_of_posDef problem.objective x (hessian_posDef problem x)

theorem newtonDirection_eq_sub_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    (problem.A⁻¹).toEuclideanLin (∇ problem.objective x) = x - problem.minimizer := by
  rw [problem.gradient_eq]
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hdet : problem.A.det ≠ 0 := ne_of_gt problem.posDef.det_pos
  change toLin b b (problem.A⁻¹) (toLin b b problem.A (x - problem.minimizer)) =
      x - problem.minimizer
  rw [← toLin_mul_apply b b b (problem.A⁻¹) problem.A (x - problem.minimizer)]
  simp [toLin_one, b, hdet]

/-- Example 1.8.7: the canonical Newton step for the quadratic stationarity system `∇ f = 0`
lands at the minimizer in one iteration. -/
theorem newtonStep_eq_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    NewtonSystem.step (∇ problem.objective) ⟨x, gradient_det_ne_zero problem x⟩ =
      problem.minimizer := by
  calc
    NewtonSystem.step (∇ problem.objective) ⟨x, gradient_det_ne_zero problem x⟩
        = x - ((∇² problem.objective x)⁻¹).toEuclideanLin (∇ problem.objective x) := by
            simpa [gradient_det_ne_zero] using
              newtonSystem_step_eq_matrixFormula problem.objective x (hessian_posDef problem x)
    _ = x - (problem.A⁻¹).toEuclideanLin (∇ problem.objective x) := by
      rw [hessian_eq problem x]
    _ = problem.minimizer := by
      rw [problem.newtonDirection_eq_sub_minimizer x]
      simp

/-- Example 1.8.7 companion: the Newton update reaches the canonical minimizer in one step. -/
theorem newtonUpdate_eq_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    x - (problem.A⁻¹).toEuclideanLin (∇ problem.objective x) = problem.minimizer := by
  calc
    x - (problem.A⁻¹).toEuclideanLin (∇ problem.objective x)
        = NewtonSystem.step (∇ problem.objective) ⟨x, gradient_det_ne_zero problem x⟩ := by
            symm
            calc
              NewtonSystem.step (∇ problem.objective) ⟨x, gradient_det_ne_zero problem x⟩
                  = x - ((∇² problem.objective x)⁻¹).toEuclideanLin (∇ problem.objective x) := by
                      simpa [gradient_det_ne_zero] using
                        newtonSystem_step_eq_matrixFormula problem.objective x
                          (hessian_posDef problem x)
              _ = x - (problem.A⁻¹).toEuclideanLin (∇ problem.objective x) := by
                rw [hessian_eq problem x]
    _ = problem.minimizer := problem.newtonStep_eq_minimizer x

end UnconstrainedQuadraticMinimizationProblem

end
