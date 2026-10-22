/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped EuclideanOrthant

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-
Source/core/bridge triage for Proposition 1.10.8:
- source-facing: weak duality `f_* ≤ f*` for the owner `LagrangianProblem`;
- core/canonical owner: `problem : LagrangianProblem Q m` with its derived notions
  `feasibleSet`, `primalOptimalValue`, `dualFunction`, and
  `dualOptimalValue`;
- bridge/view: the pointwise weak-duality estimate
  `problem.dualFunction l ≤ problem.primalOptimalValue` for `l ∈ nonnegativeOrthant m`.

Primitive data:
- `problem.objective`
- `problem.constraints`

Derived API:
- `SetConstrainedMinimizationProblem.optimalValue`
- `problem.feasibleSet`
- `problem.primalOptimalValue`
- `problem.lagrangian`
- `problem.dualFunction`
- `ℝ₊^m`
- `problem.dualFeasibleSet`
- `problem.dualOptimalValue`

The pointwise weak-duality estimate is mathematically atomic owner API, and its hypothesis is
only nonnegativity of the multiplier. The stronger dual-domain membership built into
`problem.dualFeasibleSet` is not needed for that inequality and therefore stays out of the
companion theorem statement.
-/

/-- Helper for Proposition 1.10.8: a nonnegative multiplier makes the Lagrangian no larger than
the objective at every primal-feasible point. -/
lemma lagrangian_le_objective_of_mem_feasibleSet
    (problem : LagrangianProblem Q m) {x : Q} {l : Λ}
    (hx : x ∈ problem.feasibleSet) (hl : l ∈ ℝ₊^m) :
    problem.lagrangian x l ≤ problem x := by
  -- Rewrite primal feasibility and multiplier nonnegativity coordinatewise.
  have hx_le : ∀ j : Fin m, problem.constraints j x ≤ 0 := by
    simpa using problem.mem_feasibleSet_iff.mp hx
  have hl_nonneg : ∀ j : Fin m, 0 ≤ l j := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hl
  -- Show that every summand in the inner product term is nonpositive.
  rw [LagrangianProblem.lagrangian, PiLp.inner_apply]
  have hsum_nonpos :
      ∑ j, inner ℝ (l j) (problem.constraintVector x j) ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro j _
    have hscalar :
        inner ℝ (l j) (problem.constraintVector x j) =
          l j * problem.constraintVector x j := by
      have hinner :
          inner ℝ (l j) (problem.constraintVector x j) =
            problem.constraintVector x j * (starRingEnd ℝ) (l j) :=
        RCLike.inner_apply (l j) (problem.constraintVector x j)
      simpa [mul_comm] using hinner
    rw [hscalar, problem.constraintVector_apply]
    exact mul_nonpos_of_nonneg_of_nonpos (hl_nonneg j) (hx_le j)
  linarith

/-- Helper for Proposition 1.10.8: the dual function is bounded above by the Lagrangian at every
point. -/
lemma dualFunction_le_lagrangian
    (problem : LagrangianProblem Q m) (l : Λ) (x : Q) :
    problem.dualFunction l ≤ (problem.lagrangian x l : EReal) := by
  -- Evaluate the unconstrained Lagrangian subproblem at the ambient point `x`.
  simpa [LagrangianProblem.dualFunction] using
    (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
      (problem := SetConstrainedMinimizationProblem.unconstrained
        (fun y ↦ problem.lagrangian y l))
      (x := x)
      (by simp))

/-- Weak duality at a fixed nonnegative multiplier: the dual value at `l` is bounded above by the
primal optimal value. -/
-- Proof sketch: for each feasible point `x`, the constraint terms satisfy
-- `lᵢ * problem.constraints i x ≤ 0`, so `problem.lagrangian x l ≤ problem x`. View
-- `problem.dualFunction l` as the owner optimal value of the unconstrained Lagrangian subproblem
-- and `problem.primalOptimalValue` as the owner optimal value of the primal constrained problem;
-- then compare both owner values at each feasible `x`.
theorem dualFunction_le_primalOptimalValue
    (problem : LagrangianProblem Q m) (l : Λ)
    (hl : l ∈ ℝ₊^m) :
    problem.dualFunction l ≤ problem.primalOptimalValue := by
  -- Rewrite the primal value as the infimum of the feasible objective values.
  rw [problem.primalOptimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨x, hx, rfl⟩
  -- Compare `ψ(l)` to the feasible objective through the Lagrangian at `x`.
  calc
    problem.dualFunction l ≤ (problem.lagrangian x l : EReal) :=
      problem.dualFunction_le_lagrangian l x
    _ ≤ (problem x : EReal) := by
      exact_mod_cast problem.lagrangian_le_objective_of_mem_feasibleSet hx hl

/-- Proposition 1.10.8: weak duality bounds the dual optimal value of a Lagrangian problem by
its primal optimal value. -/
-- Proof sketch: apply
-- `dualFunction_le_primalOptimalValue` to each
-- `l ∈ problem.dualFeasibleSet`, using `problem.mem_dualFeasibleSet_iff` to extract the
-- nonnegativity hypothesis, and then pass to the supremum over the dual-feasible set.
theorem dualOptimalValue_le_primalOptimalValue
    (problem : LagrangianProblem Q m) :
    problem.dualOptimalValue ≤ problem.primalOptimalValue := by
  -- Bound every dual-feasible image point by the fixed-multiplier weak-duality estimate.
  rw [LagrangianProblem.dualOptimalValue]
  refine sSup_le ?_
  rintro _ ⟨l, hl, rfl⟩
  have hl_nonneg : l ∈ ℝ₊^m := by
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
      (problem.mem_dualFeasibleSet_iff.mp hl).2
  exact problem.dualFunction_le_primalOptimalValue l hl_nonneg

end LagrangianProblem
