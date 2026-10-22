/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_7_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 5.0.5 lies in the Chapter 1 local Newton-convergence domain specialized to `ℝⁿ`.

Source/core/bridge triage:
* source-facing: the Euclidean Newton theorem stated with the Hessian matrix lower bound
  `μ I ≤ ∇² f(xStar)`
* core/canonical: `localQuadraticNewtonOrbit` and
  `newtonOptimizationIterates_mem_ball_and_quadratic_error_bound`
* bridge/view: the Euclidean matrix-to-operator positivity bridge used to feed the Chapter 1
  owner theorem

Primary domain:
* local quadratic convergence of Newton's method for smooth unconstrained optimization on
  Euclidean space

Sampled owner-style declarations:
* `NewtonSystem.step`
* `NewtonSystem.orbit`
* `localQuadraticNewtonOrbit`
* `newtonOptimizationIterates_mem_ball_and_quadratic_error_bound`

Owner abstraction:
* the Chapter 1 local Newton orbit `localQuadraticNewtonOrbit` together with its owner theorem
  `newtonOptimizationIterates_mem_ball_and_quadratic_error_bound`

Primitive data:
* `f`, `xStar`, `x0`, `μ`, and `M`
* `f ∈ C22[M]`, `∇ f xStar = 0`, positivity of `μ`
* the Euclidean Hessian matrix lower bound
  `(∇² f xStar - μ • (1 : Mat)).PosSemidef`
* the initial closed-ball hypothesis `‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M`

Derived API:
* the operator-positivity hypothesis required by the Chapter 1 owner theorem
* iteratewise Hessian nondegeneracy on the canonical operator owner `hessian`
* the closed-ball invariance and quadratic one-step error estimate for the canonical local
  Newton orbit

This file therefore keeps only the Euclidean/source-facing bridge and reuses the established
Chapter 1 Newton owner layer directly instead of rebuilding a parallel step/orbit package.
-/

private theorem hessianMatrix_lower_isPositive
    {f : E → ℝ} {x : E} {μ : ℝ}
    (h : (∇² f x - μ • (1 : Mat)).PosSemidef) :
    (hessian f x - μ • (1 : E →L[ℝ] E)).IsPositive := by
  have hpos :
      (∇² f x - μ • (1 : Mat)).toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr h
  have hsub :
      (∇² f x - μ • (1 : Mat)).toEuclideanLin =
        (∇² f x).toEuclideanLin - μ • (1 : E →L[ℝ] E) := by
    ext v i
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [hsub] at hpos
  rw [hessianMatrix_toEuclideanLin] at hpos
  simpa [hessian] using hpos

/-- Theorem 5.0.5: if `f : ℝⁿ → ℝ` is twice continuously differentiable, `x*` is a critical
point, `∇² f(x*) - μ I` is positive semidefinite, and the Hessian is `M`-Lipschitz, then the
canonical local Newton orbit started in the closed ball of radius `2 μ / (3 M)` around `x*`
stays in that ball, has nonsingular Hessian at every iterate, and satisfies the standard
quadratic one-step error estimate. -/
theorem newton_method_has_local_quadratic_convergence
    (f : E → ℝ) (xStar x0 : E) {μ : ℝ} {M : NNRealˣ}
    (hf : f ∈ C22[M])
    (hcrit : ∇ f xStar = 0)
    (hμ : 0 < μ)
    (hessian_lower : (∇² f xStar - μ • (1 : Mat)).PosSemidef)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    let traj :=
      localQuadraticNewtonOrbit hμ hf hcrit
        (hessianMatrix_lower_isPositive hessian_lower) hx0
    (∀ k, ‖traj k - xStar‖ ≤ localQuadraticNewtonRadius μ M) ∧
      (∀ k, (hessian f (traj k)).det ≠ 0) ∧
      ∀ k,
        ‖traj (k + 1) - xStar‖ ≤
          ((M : ℝ) * ‖traj k - xStar‖ ^ (2 : ℕ)) /
            (2 * (μ - (M : ℝ) * ‖traj k - xStar‖)) := by
  let hHstar : (hessian f xStar - μ • (1 : E →L[ℝ] E)).IsPositive :=
    hessianMatrix_lower_isPositive hessian_lower
  let traj := localQuadraticNewtonOrbit hμ hf hcrit hHstar hx0
  rcases
      newtonOptimizationIterates_mem_ball_and_quadratic_error_bound hμ hf hcrit hHstar hx0 with
    ⟨hball, hdet, hquad⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [traj] using hball
  · intro k
    simpa [traj, hessian] using hdet k
  · simpa [traj] using hquad

end
