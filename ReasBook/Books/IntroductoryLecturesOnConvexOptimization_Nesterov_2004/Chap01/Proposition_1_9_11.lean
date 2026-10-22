/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_9_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_8_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_5_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open Matrix

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace UnconstrainedQuadraticMinimizationProblem

/- Proposition 1.9.11 stays in the owner domain of
`UnconstrainedQuadraticMinimizationProblem`.

Sampled chapter declarations:
* `minimizer_isMinOn`
* `objective_eq_objective_minimizer_add_quadratic_error`
* `quadraticObjective_gradient_eq`
* `isMinOn_gradient_eq_zero`

Owner abstraction:
* source-facing: the quadratic owner `problem`
* core/canonical: its minimizer, completed-square identity, and general quadratic-gradient formula
* bridge/view: the centered expression `x - problem.minimizer`

Primitive data:
* `problem.α`, `problem.a`, `problem.A`, `problem.posDef`

Derived API:
* the global-minimizer fact and completed-square identity recalled below from
  `Lemma_1_8_8`
* the minimum-value, stationary-point, and uniqueness formulas proved here from those owners
-/

/- Proposition 1.9.11 first reuses the existing owner theorem that `problem.minimizer` is a
global minimizer. -/
recall minimizer_isMinOn
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    IsMinOn problem Set.univ problem.minimizer

/- The completed-square identity is already owned upstream by `Lemma_1.8.8`. -/
recall objective_eq_objective_minimizer_add_quadratic_error
    (problem : UnconstrainedQuadraticMinimizationProblem n) (y : E) :
    problem.objective y =
      problem.objective problem.minimizer +
        (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin (y - problem.minimizer))
          (y - problem.minimizer)

private theorem linear_coefficient_eq_neg_apply_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.a = -problem.A.toEuclideanLin problem.minimizer := by
  simpa using (congrArg Neg.neg
    (apply_matrix_to_minimizer_eq_neg_linear_coefficient problem)).symm

private theorem eq_minimizer_of_isMinOn
    (problem : UnconstrainedQuadraticMinimizationProblem n) {x : E}
    (hx : IsMinOn problem Set.univ x) :
    x = problem.minimizer := by
  have hx' := isMinOn_univ_iff.mp hx
  have hmin' := isMinOn_univ_iff.mp (minimizer_isMinOn problem)
  have hvalue : problem.objective x = problem.objective problem.minimizer := by
    exact le_antisymm (hx' problem.minimizer) (hmin' x)
  have hquad :
      inner ℝ (problem.A.toEuclideanLin (x - problem.minimizer))
        (x - problem.minimizer) = 0 := by
    have hobjective := objective_eq_objective_minimizer_add_quadratic_error problem x
    nlinarith [hobjective, hvalue]
  have hsub : x - problem.minimizer = 0 := by
    by_contra hne
    have hcoord_ne : (x - problem.minimizer).ofLp ≠ 0 := by
      intro hcoord
      apply hne
      exact congrArg (WithLp.toLp 2) hcoord
    have hcoord :
        inner ℝ (problem.A.toEuclideanLin (x - problem.minimizer))
          (x - problem.minimizer) =
          dotProduct (x - problem.minimizer).ofLp
            (problem.A *ᵥ (x - problem.minimizer).ofLp) := by
      simpa only [Matrix.ofLp_toLpLin] using
        (EuclideanSpace.inner_eq_star_dotProduct
          (problem.A.toEuclideanLin (x - problem.minimizer)) (x - problem.minimizer))
    have hpos :
        0 <
          inner ℝ (problem.A.toEuclideanLin (x - problem.minimizer))
            (x - problem.minimizer) := by
      rw [hcoord]
      exact problem.posDef.dotProduct_mulVec_pos hcoord_ne
    linarith
  exact sub_eq_zero.mp hsub

/-- Evaluating the objective at its minimizer gives the minimum value formula. -/
-- Proof sketch: specialize the completed-square identity at `x = x*`, where the quadratic error
-- term vanishes.
theorem objective_value_at_minimizer
    (problem : UnconstrainedQuadraticMinimizationProblem n) :
    problem.objective problem.minimizer =
      problem.α -
        (1 / 2 : ℝ) *
          inner ℝ (problem.A.toEuclideanLin problem.minimizer) problem.minimizer :=
  by
  rw [UnconstrainedQuadraticMinimizationProblem.objective, quadraticObjective,
    linear_coefficient_eq_neg_apply_minimizer problem]
  simp
  ring

/-- The gradient of the objective is `A (x - x*)` when `x* = -A⁻¹ a`. -/
-- Proof sketch: differentiate the affine and quadratic parts to get `a + A x`, then substitute
-- `a = -A x*` from the definition of the minimizer.
theorem gradient_eq
    (problem : UnconstrainedQuadraticMinimizationProblem n) (x : E) :
    ∇ problem.objective x = problem.A.toEuclideanLin (x - problem.minimizer) := by
  have hsymm : problem.A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using problem.posDef.1
  have hgrad :=
    congrFun (quadraticObjective_gradient_eq problem.α problem.a problem.A hsymm) x
  calc
    ∇ problem.objective x = problem.a + problem.A.toEuclideanLin x := by
      simpa [UnconstrainedQuadraticMinimizationProblem.objective] using hgrad
    _ = -problem.A.toEuclideanLin problem.minimizer + problem.A.toEuclideanLin x := by
      rw [linear_coefficient_eq_neg_apply_minimizer problem]
    _ = problem.A.toEuclideanLin x - problem.A.toEuclideanLin problem.minimizer := by
      simp [sub_eq_add_neg, add_comm]
    _ = problem.A.toEuclideanLin (x - problem.minimizer) := by
      rw [LinearMap.map_sub]

/-- Any stationary point of the quadratic objective is the canonical minimizer. -/
-- Proof sketch: the gradient formula identifies stationarity with vanishing centered quadratic
-- error. The completed-square identity then shows that `x` has the same objective value as the
-- canonical minimizer `x*`, so `x` is itself a global minimizer; uniqueness below forces
-- `x = x*`.
theorem eq_minimizer_of_gradient_eq_zero
    (problem : UnconstrainedQuadraticMinimizationProblem n) {x : E}
    (hx : ∇ problem.objective x = 0) :
    x = problem.minimizer := by
  have hA : problem.A.toEuclideanLin (x - problem.minimizer) = 0 := by
    simpa [problem.gradient_eq x] using hx
  have hxmin : IsMinOn problem Set.univ x := by
    rw [isMinOn_univ_iff]
    intro y
    calc
      problem.objective x = problem.objective problem.minimizer := by
        calc
          problem.objective x
              = problem.objective problem.minimizer +
                  (1 / 2 : ℝ) * inner ℝ (problem.A.toEuclideanLin (x - problem.minimizer))
                      (x - problem.minimizer) := by
                  simpa using
                    objective_eq_objective_minimizer_add_quadratic_error problem x
          _ = problem.objective problem.minimizer := by
                simp [hA]
      _ ≤ problem.objective y := by
        exact (isMinOn_univ_iff.mp (minimizer_isMinOn problem)) y
  exact eq_minimizer_of_isMinOn problem hxmin

/-- Any global minimizer of an unconstrained quadratic minimization problem is the canonical
point `problem.minimizer = -A⁻¹ a`. -/
-- Proof sketch: a global minimizer on `Set.univ` is stationary by the ambient owner theorem
-- `isMinOn_gradient_eq_zero`, and the owner-side stationary-point theorem above identifies the
-- only stationary point with `problem.minimizer`.
theorem minimizer_unique (problem : UnconstrainedQuadraticMinimizationProblem n) {x : E}
    (hx : IsMinOn problem Set.univ x) :
    x = problem.minimizer := by
  exact problem.eq_minimizer_of_gradient_eq_zero (isMinOn_gradient_eq_zero hx)

end UnconstrainedQuadraticMinimizationProblem
