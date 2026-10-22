/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/- This item lies in the modified Gauss--Newton / Newton quadratic-entry domain.

Sampled owner declarations:
* `ModifiedGaussNewtonProblem` in `Definition_4_4_16`, the chapter owner bundling the objective,
  strong-convexity, Hessian-Lipschitz, minimizer, and starting-point data;
* `modifiedNewton_hasQuadraticConvergenceFrom_zero_of_characteristicQuantity_lt_one` and
  `modifiedNewton_firstQuadraticConvergenceIndex_le_sqrt_characteristicQuantity` in
  `Proposition_4_4_10`, the core Chapter 4 owner theorems for the small-characteristic and
  large-characteristic quadratic-entry regimes of the underlying modified Newton orbit;
* `IsLeast {k | HasQuadraticConvergenceFrom method problem.xStar k}` in `Text_4_2_24`, the
  canonical package for the first index from which an orbit converges quadratically;
* `ModifiedGaussNewtonProblem.characteristicQuantity` in `Definition_4_4_16`, the bridge from the
  bundled problem data to the scalar parameter used by the owner theorem.

Source/core/bridge triage:
* source-facing: the modified Gauss--Newton stationarity reformulation attached to
  `problem : ModifiedGaussNewtonProblem E`;
* core/canonical: the modified-Newton owner theorems
  `modifiedNewton_hasQuadraticConvergenceFrom_zero_of_characteristicQuantity_lt_one` and
  `modifiedNewton_firstQuadraticConvergenceIndex_le_sqrt_characteristicQuantity`;
* bridge/view: the coercion from `problem` to its objective together with
  `problem.characteristicQuantity`.

Primitive data:
* the bundled owner object `problem`;
* the Newton orbit `method` of the stationarity reformulation;
* the first quadratic-convergence index witness `hN2`.

Derived API:
* the strong-convexity, Hessian-Lipschitz, and minimizer hypotheses supplied by the fields of
  `problem`;
* the scalar bridge `problem.characteristicQuantity`;
* the Chapter 4 modified-Newton entry-index estimate.

The public surface should therefore be a thin bridge from the bundled modified Gauss--Newton
problem to the Chapter 4 modified-Newton owner theorem, rather than a second theorem specialized
to the concrete model `EuclideanSpace ℝ (Fin n)`.
-/

section

set_option linter.style.longLine false

-- Proof sketch: apply the Chapter 4 modified-Newton owner theorems to the objective carried by
-- `problem`. The bundled owner fields supply the strong-convexity, Hessian-Lipschitz, and
-- minimizer hypotheses, and the textbook parameter `ζ` is exactly
-- `problem.characteristicQuantity`. For `ζ < 1`, reuse the upstream small-characteristic owner
-- theorem to get quadratic convergence from index `0`; for `ζ ≥ 1`, reuse the upstream entry-index
-- estimate and then dominate `6.25 * sqrt ζ` by the textbook scalar surface `1 + 6 ζ²`.
/-- Proposition 4.4.11: if `problem` is a modified Gauss--Newton problem, `method` is the
associated modified Newton orbit started at `problem.x0`, and `N₂` is the first
quadratic-convergence index of `method` toward `problem.xStar`, then `(N₂ : ℝ)` is bounded by
`1 + 6 * problem.characteristicQuantity ^ (2 : ℕ)`. -/
theorem modifiedGaussNewton_scheme_firstQuadraticConvergenceIndex_le_one_add_six_mul_characteristicQuantity_sq
    (problem : ModifiedGaussNewtonProblem E)
    (method : NewtonSystem.Method (∇ problem) problem.x0)
    {N2 : ℕ}
    (hN2 : IsLeast {k : ℕ | HasQuadraticConvergenceFrom method problem.xStar k} N2) :
    (N2 : ℝ) ≤ 1 + 6 * problem.characteristicQuantity ^ (2 : ℕ) := by
  by_cases hξ : problem.characteristicQuantity < 1
  · have hquad0 :
        HasQuadraticConvergenceFrom method problem.xStar 0 :=
      modifiedNewton_hasQuadraticConvergenceFrom_zero_of_characteristicQuantity_lt_one
        problem.sigma_pos
        problem.objective_strongConvex
        problem.objective_mem
        problem.xStar_isMin
        method
        (by simpa using hξ)
    have hN2_zero : N2 = 0 := Nat.eq_zero_of_le_zero (hN2.2 hquad0)
    rw [hN2_zero]
    have hrhs : (0 : ℝ) ≤ 1 + 6 * problem.characteristicQuantity ^ (2 : ℕ) := by
      positivity
    simpa using hrhs
  · have hξ' : 1 ≤ problem.characteristicQuantity := by
      linarith
    have hbound :=
      modifiedNewton_firstQuadraticConvergenceIndex_le_sqrt_characteristicQuantity
        problem.sigma_pos
        problem.objective_strongConvex
        problem.objective_mem
        problem.xStar_isMin
        method
        (by simpa using hξ')
        hN2
    have hscalar :
        (25 / 4 : ℝ) * Real.sqrt problem.characteristicQuantity ≤
          1 + 6 * problem.characteristicQuantity ^ (2 : ℕ) := by
      have hsqrt_le :
          Real.sqrt problem.characteristicQuantity ≤ problem.characteristicQuantity := by
        rw [Real.sqrt_le_iff]
        constructor
        · linarith
        · nlinarith [hξ']
      calc
        (25 / 4 : ℝ) * Real.sqrt problem.characteristicQuantity ≤
            (25 / 4 : ℝ) * problem.characteristicQuantity := by
          gcongr
        _ ≤ 1 + 6 * problem.characteristicQuantity ^ (2 : ℕ) := by
          nlinarith [hξ']
    exact hbound.trans hscalar

end
