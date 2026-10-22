/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_2

section Chapter08Theorem8219

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

/-- Under strict convexity of the objective on the feasible set, any two feasible global
minimizers of a constrained optimization problem coincide. -/
theorem IsGlobalMinimizer.eq_of_strictConvexObjective
    {problem : ConstrainedOptimizationProblem n m E I} {x y : Point}
    (hx : problem.IsGlobalMinimizer x) (hy : problem.IsGlobalMinimizer y)
    (h_strict : StrictConvexOn ℝ problem.feasibleSet problem.objective) :
    x = y :=
  h_strict.eq_of_isMinOn hx.isMinOn hy.isMinOn hx.feasible hy.feasible

end ConstrainedOptimizationProblem

/-- Chapter08 Theorem 8.2.19: if the objective of a constrained optimization problem is strictly
convex on its feasible set and a feasible global minimizer exists, then that minimizer is unique. -/
theorem existsUnique_globalMinimizer_of_strictConvexObjective
    (problem : ConstrainedOptimizationProblem n m E I)
    (h_strict : StrictConvexOn ℝ problem.feasibleSet problem.objective)
    (h_exists : ∃ x : Point, problem.IsGlobalMinimizer x) :
    ∃! x : Point, problem.IsGlobalMinimizer x := by
  rcases h_exists with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hy.eq_of_strictConvexObjective hx h_strict

end Chapter08Theorem8219
