/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Lemma_10_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Theorem_10_2_5

open Filter
open StandardPenaltyProblem

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling:
-- * primary domain: Chapter 10 simple-penalty methods for mixed equality/inequality constrained
--   problems in `ℝ^n`
-- * inspected project declarations:
--   `StandardPenaltyProblem.feasibleSet` and
--   `StandardPenaltyProblem.mem_iff_constraintViolation_eq_zero` in
--   `Definition_10_1_extra_1` as the owner API for the original constrained problem,
--   `simplePenaltyViolationSublevelSet` in `Lemma_10_2_2` as the source-facing owner for the
--   attained violation sublevel sets,
--   `SimplePenaltyFunctionMethod.terminatedAt` in `Algorithm_10_2_3` as the stagewise stopping
--   owner,
--   `StandardPenaltyProblem.minimalViolationSet` and
--   `simplePenaltyFunctionMethod_accumulationPoint_isMinOn_minimalViolationSet` in
--   `Theorem_10_2_5` as the nontermination-side owner API
-- * best owner abstraction: `method.problem.feasibleSet` for "solves the original problem",
--   together with `simplePenaltyViolationSublevelSet` for the attained-violation finite branch
-- * primitive data vs. derived API:
--   primitive method data are the constrained problem, tolerance, iterates, and stage
--   subproblem minimizers already bundled by `SimplePenaltyFunctionMethod`;
--   attained-sublevel optimality is derived API, and original-problem feasibility/optimality
--   should reuse `method.problem.feasibleSet` rather than a parallel zero-sublevel wrapper

namespace SimplePenaltyFunctionMethod

/-- Every stage solution `x(σ_k)` minimizes the original objective on the attained violation
sublevel set `‖c⁽-⁾(x)‖ ≤ ‖c⁽-⁾(x(σ_k))‖`. This is the Chapter 10 owner-level consequence of
`Lemma_10_2_2` for the method's stage-`k` subproblem. -/
theorem subproblemSolution_isMinOnObjectiveOnAttainedViolationSublevelSet
    (method : SimplePenaltyFunctionMethod n m) {k : ℕ} (hk : 1 ≤ k)
    (hreached : method.reached k) :
    IsMinOn
      method.problem.objective
      (simplePenaltyViolationSublevelSet
        (c⁽-⁾[method.problem])
        ‖c⁽-⁾[method.problem] (method.subproblemSolution k)‖)
      (method.subproblemSolution k) :=
  let hσ : 0 ≤ method.penaltyParameter k := le_of_lt (method.penaltyParameterPos k hk hreached)
  let hα : 0 ≤ method.penaltyExponent := le_of_lt method.penaltyExponentPos
  isMinOnObjectiveOnSimplePenaltyViolationSublevelSet_of_isMinOn_simplePenaltyObjective
    method.problem hσ hα (method.subproblemSolution k)
    (method.subproblemSolution_isMinimizer hk hreached)

/-- The stage-`k` solution belongs to its attained violation sublevel set. -/
theorem subproblemSolution_mem_attainedViolationSublevelSet
    (method : SimplePenaltyFunctionMethod n m) (k : ℕ) :
    method.subproblemSolution k ∈
      simplePenaltyViolationSublevelSet
        (c⁽-⁾[method.problem])
        ‖c⁽-⁾[method.problem] (method.subproblemSolution k)‖ := by
  exact
    (mem_simplePenaltyViolationSublevelSet_iff
      (c⁽-⁾[method.problem])
      ‖c⁽-⁾[method.problem] (method.subproblemSolution k)‖
      (method.subproblemSolution k)).2 le_rfl

/-- If the method does not terminate finitely, then each step update satisfies
`x_(k + 1) = x(σ_k)` for every stage `k ≥ 1`. -/
theorem iterate_succ_eq_subproblemSolution_of_doesNotTerminateFinitely
    (method : SimplePenaltyFunctionMethod n m)
    (hNoTerminate : method.doesNotTerminateFinitely)
    {k : ℕ} (hk : 1 ≤ k) :
    method.iterate (k + 1) = method.subproblemSolution k := by
  have hreached : method.reached k :=
    method.reached_of_doesNotTerminateFinitely hNoTerminate k hk
  exact method.iterate_update_eq hk hreached
    (method.not_terminatedAt_of_doesNotTerminateFinitely hNoTerminate hk)

/-- If the original problem has a feasible point and the method does not terminate finitely, then
the Chapter 10 minimal-violation set agrees with the original feasible set. -/
theorem minimalViolationSet_eq_feasibleSet_of_nonempty_feasibleSet_of_doesNotTerminateFinitely
    (method : SimplePenaltyFunctionMethod n m)
    (hfeasible : Set.Nonempty method.problem.feasibleSet)
    (hNoTerminate : method.doesNotTerminateFinitely) :
    method.problem.minimalViolationSet = method.problem.feasibleSet := by
  sorry

/-- If the original problem is feasible and the method does not terminate finitely, then any
accumulation point of the generated iterate sequence, encoded by a convergent subsequence
`x_(φ k + 1)`, solves the original problem. This is the source-facing bridge from
`simplePenaltyFunctionMethod_accumulationPoint_isMinOn_minimalViolationSet` to
`method.problem.feasibleSet`. -/
theorem accumulationPoint_solvesOriginalProblem_of_doesNotTerminateFinitely
    (method : SimplePenaltyFunctionMethod n m)
    (hfeasible : Set.Nonempty method.problem.feasibleSet)
    (hNoTerminate : method.doesNotTerminateFinitely)
    {xStar : Point} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hxStar : Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar)) :
    xStar ∈ method.problem.feasibleSet ∧
      IsMinOn method.problem.objective method.problem.feasibleSet xStar := by
  sorry

end SimplePenaltyFunctionMethod

/-- Chapter10 Corollary 10.2.6: if the original constrained problem has a feasible point, then
Algorithm 10.2.3 either finitely terminates at a stage solution that also minimizes
`method.problem.objective` on its attained violation sublevel set, or every accumulation point
of the generated iterate sequence, encoded by a convergent subsequence `x_(φ k + 1)`, solves the
original problem, represented here by membership in `method.problem.feasibleSet` together with
`IsMinOn` on that feasible set. -/
theorem simplePenaltyFunctionMethod_finiteTermination_or_accumulationPoint_solvesOriginalProblem
    (method : SimplePenaltyFunctionMethod n m)
    (hfeasible : Set.Nonempty method.problem.feasibleSet) :
    (∃ k : ℕ,
      1 ≤ k ∧
        method.reached k ∧
          method.terminatedAt k ∧
          method.subproblemSolution k ∈
            simplePenaltyViolationSublevelSet
              (c⁽-⁾[method.problem])
              ‖c⁽-⁾[method.problem] (method.subproblemSolution k)‖ ∧
          IsMinOn
            method.problem.objective
            (simplePenaltyViolationSublevelSet
              (c⁽-⁾[method.problem])
              ‖c⁽-⁾[method.problem] (method.subproblemSolution k)‖)
            (method.subproblemSolution k))
    ∨
      ∀ {xStar : Point} {φ : ℕ → ℕ},
        StrictMono φ →
        Tendsto (fun k : ℕ ↦ method.iterate (φ k + 1)) atTop (nhds xStar) →
        xStar ∈ method.problem.feasibleSet ∧
          IsMinOn method.problem.objective method.problem.feasibleSet xStar := by
  sorry

end
