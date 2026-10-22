/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_5

section Chapter08Exercise81

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

-- Semantic recall: `IsMinOn.of_isLocalMinOn_of_convexOn` is the canonical local-to-global convex
-- minimizer theorem, and Chapter 8 already owns the constrained-problem API and the affine
-- feasible-set convexity bridge.

/-- If each equality constraint of `problem` is linear and each inequality constraint is concave,
then `problem.feasibleSet` is convex. -/
theorem convex_feasibleSet_of_eq_linear_of_ineq_concave
    (problem : ConstrainedOptimizationProblem n m E I)
    (h_eq : ∀ i ∈ E, ∃ c : Point →ₗ[ℝ] ℝ, problem.constraint i = c)
    (h_ineq : ∀ i ∈ I, ConcaveOn ℝ Set.univ (problem.constraint i)) :
    Convex ℝ problem.feasibleSet := by
  refine ConstrainedOptimizationProblem.convex_feasibleSet_of_eq_affine_of_ineq_concave
    problem ?_ h_ineq
  intro i hi
  rcases h_eq i hi with ⟨c, hc⟩
  refine ⟨c.toAffineMap, ?_⟩
  simpa using hc.trans (LinearMap.coe_toAffineMap c).symm

/-- Chapter08 Exercise 8.1: assume `problem.objective` is convex on `Set.univ`, each equality
constraint of `problem` is linear, and each inequality constraint is concave. If `xStar` is a
local minimizer of `problem.objective` on `problem.feasibleSet`, then `xStar` is a global
minimizer of the constrained problem, formalized as
`IsMinOn problem.objective problem.feasibleSet xStar`. -/
theorem isMinOn_of_isLocalMinOn_of_convexObjective_of_eq_linear_of_ineq_concave
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (h_objective : ConvexOn ℝ Set.univ problem.objective)
    (h_eq : ∀ i ∈ E, ∃ c : Point →ₗ[ℝ] ℝ, problem.constraint i = c)
    (h_ineq : ∀ i ∈ I, ConcaveOn ℝ Set.univ (problem.constraint i))
    (hxStar : xStar ∈ problem)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar) :
    IsMinOn problem.objective problem.feasibleSet xStar := by
  exact IsMinOn.of_isLocalMinOn_of_convexOn hxStar h_localMin <|
    h_objective.subset (by simp) <|
      convex_feasibleSet_of_eq_linear_of_ineq_concave problem h_eq h_ineq

end Chapter08Exercise81
