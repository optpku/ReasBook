/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Lemma_8_2_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_14

noncomputable section

section Chapter08Corollary8215

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

-- Domain sampling pass:
-- * primary domain: constrained local minima via first-order feasible-direction conditions
-- * inspected project owners/bridges:
--   `ConstrainedOptimizationProblem.HasActiveConstraintGradientsAt` from `Definition_8_2_2`
--   `ConstrainedOptimizationProblem.linearizedFeasibleDirectionSet` from `Definition_8_2_2`
--   `sequentialFeasibleDirections xStar problem.feasibleSet = posTangentConeAt _ _` from
--   `Definition_8_2_3`
--   `sequentialFeasibleDirections_subset_linearizedFeasibleDirectionSet` from `Lemma_8_2_4`
--   `isStrictLocalMinOn_of_positive_pairing_on_sequentialFeasibleDirections` from
--   `Theorem_8_2_14`
-- * owner abstraction chosen here: the existing Chapter 8 constrained-problem owner together
--   with the source-facing linearized-feasible-direction set; this corollary is only the bridge
--   from the sequential theorem to the stronger linearized hypothesis
-- * companion API added here: the canonical `IsLocalMinOn` consequence, matching the Chapter 8
--   theorem/corollary pattern for strict local minima

/-- Chapter08 Corollary 8.2.15: let `xStar ∈ X` be a feasible point of a constrained optimization
problem. If the objective and every active constraint function are differentiable at `xStar`, and
every nonzero linearized feasible direction `d ∈ LFD(xStar, X)` has strictly positive directional
derivative `fderiv ℝ problem.objective xStar d`, then `xStar` is a strict local minimizer of the
constrained problem on `X = problem.feasibleSet`. -/
theorem isStrictLocalMinOn_of_positive_pairing_on_linearizedFeasibleDirectionSet
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasActiveConstraintGradientsAt xStar)
    (h_positive :
      ∀ d ∈ problem.linearizedFeasibleDirectionSet xStar,
        d ≠ 0 → 0 < fderiv ℝ problem.objective xStar d) :
    IsStrictLocalMinOn problem.objective problem.feasibleSet xStar := by
  refine
    isStrictLocalMinOn_of_positive_pairing_on_sequentialFeasibleDirections
      problem xStar hxStar h_objective ?_
  intro d hd hd_nonzero
  exact
    h_positive d
      ((sequentialFeasibleDirections_subset_linearizedFeasibleDirectionSet
          problem xStar hxStar h_constraints) hd)
      hd_nonzero

/-- Companion bridge: Corollary 8.2.15 also yields the canonical constrained local-minimum
predicate `IsLocalMinOn`. -/
theorem isLocalMinOn_of_positive_pairing_on_linearizedFeasibleDirectionSet
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasActiveConstraintGradientsAt xStar)
    (h_positive :
      ∀ d ∈ problem.linearizedFeasibleDirectionSet xStar,
        d ≠ 0 → 0 < fderiv ℝ problem.objective xStar d) :
    IsLocalMinOn problem.objective problem.feasibleSet xStar :=
  (isStrictLocalMinOn_of_positive_pairing_on_linearizedFeasibleDirectionSet
      problem xStar hxStar h_objective h_constraints h_positive).isLocalMinOn

end Chapter08Corollary8215
