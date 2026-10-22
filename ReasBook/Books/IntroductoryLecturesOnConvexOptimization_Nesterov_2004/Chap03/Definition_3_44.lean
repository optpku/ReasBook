/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators EuclideanOrthant

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/-
Definition 3.44 lies in the finite-constraint Lagrangian-duality domain.

Sampled owner-style declarations in this domain:
* `LagrangianProblem.lagrangian`, `dualFunction`, `dualFeasibleSet`, and `dualOptimalValue` in
  `Chap01/Definition_1_10_2`, the Chapter 1 owner API for the textbook Lagrangian, dual
  function, and dual optimal value;
* `SetConstrainedMinimizationProblem.unconstrained` and
  `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image` in `Chap01/Definition_1_3_3`
  and `Chap01/Definition_1_3_7`, the canonical ambient minimization owner used to define
  `problem.dualFunction`;
* `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` in
  `Chap01/Definition_1_10_2`, the owner for the nonnegative multiplier orthant.

Best owner abstraction:
* source-facing: the textbook Lagrangian-duality formulas of Definition 3.44;
* core/canonical: `problem : LagrangianProblem Q m`;
* bridge/view: the explicit sum, infimum, and orthant-supremum expansions below.

Primitive data:
* `problem.objective`
* `problem.constraints`

Derived API:
* `problem.constraintVector`
* `problem.lagrangian`
* `problem.dualFunction`
* `problem.dualDomain`
* `problem.dualFeasibleSet`
* `problem.dualOptimalValue`

The owner declarations already live upstream in Chapter 1, so this file should recall those
owners directly and keep only the source-facing expansion formulas as companions. -/
/-
Definition 3.44: the textbook Lagrangian is the canonical owner `problem.lagrangian`. -/
recall lagrangian (problem : LagrangianProblem Q m) (x : Q) (l : Λ) : ℝ

/-
Definition 3.44: the textbook dual function is the canonical owner `problem.dualFunction`. -/
recall dualFunction (problem : LagrangianProblem Q m) (l : Λ) : EReal

/-
Definition 3.44: the textbook dual optimal value is the canonical owner
`problem.dualOptimalValue`. -/
recall dualOptimalValue (problem : LagrangianProblem Q m) : EReal

/-- Helper for Definition 3.44: the inner product with the constraint vector expands as the
coordinatewise weighted sum of the scalar constraint values. -/
lemma inner_constraintVector_eq_sum
    (problem : LagrangianProblem Q m) (x : Q) (l : Λ) :
    inner ℝ l (problem.constraintVector x) =
      ∑ j : Fin m, l j * problem.constraints j x := by
  -- Rewrite the Euclidean inner product as the coordinatewise finite sum.
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  -- Replace the constraint-vector coordinate by the underlying scalar constraint value.
  simpa [problem.constraintVector_apply] using
    (RCLike.inner_apply' (l j) (problem.constraints j x))

/-- The Lagrangian evaluates to the objective plus the weighted sum of the constraint values. -/
-- Proof sketch: unfold `LagrangianProblem.lagrangian`, rewrite the inner product on
-- `EuclideanSpace ℝ (Fin m)` as a finite sum, and then identify the coordinates of
-- `problem.constraintVector x` with the constraint functions `problem.constraints j x`.
theorem lagrangian_eq_objective_add_sum
    (problem : LagrangianProblem Q m) (x : Q) (l : Λ) :
    problem.lagrangian x l =
      problem.objective x + ∑ j : Fin m, l j * problem.constraints j x := by
  -- Unfold the owner Lagrangian and rewrite its inner-product term by the coordinate formula.
  rw [LagrangianProblem.lagrangian, problem.coe_apply, inner_constraintVector_eq_sum]

/-- The project records the textbook dual function as the extended-real infimum of the
Lagrangian over the decision set. -/
-- Proof sketch: this is the defining equation of `problem.dualFunction`, obtained by unfolding
-- the owner definition of the dual function.
theorem dualFunction_eq_sInf_range_lagrangian
    (problem : LagrangianProblem Q m) (l : Λ) :
    problem.dualFunction l =
      sInf (Set.range fun x : Q ↦ (problem.lagrangian x l : EReal)) := by
  simpa [LagrangianProblem.dualFunction, SetConstrainedMinimizationProblem.unconstrained] using
    (SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image
      (SetConstrainedMinimizationProblem.unconstrained fun x : Q ↦ problem.lagrangian x l))

/-- Helper for Definition 3.44: multipliers outside the dual domain contribute the value `⊥` to
the dual function. -/
lemma dualFunction_eq_bot_of_not_mem_dualDomain
    (problem : LagrangianProblem Q m) {l : Λ} (hl : l ∉ problem.dualDomain) :
    problem.dualFunction l = ⊥ := by
  -- Outside `dualDomain`, the defining inequality `⊥ < ψ(l)` fails, so the value must be `⊥`.
  exact le_bot_iff.mp <| le_of_not_gt <| by
    simpa [problem.mem_dualDomain_iff] using hl

/-- Helper for Definition 3.44: every dual value attained on the nonnegative orthant is either
`⊥` or already attained on the dual-feasible set. -/
lemma dualFunction_image_nonnegativeOrthant_subset_insert_bot_dualFeasibleSet
    (problem : LagrangianProblem Q m) :
    problem.dualFunction '' ℝ₊^m ⊆
      insert ⊥ (problem.dualFunction '' problem.dualFeasibleSet) := by
  intro y hy
  rcases hy with ⟨l, hl_nonneg, rfl⟩
  by_cases hdom : l ∈ problem.dualDomain
  · -- In the dual domain, nonnegativity is exactly dual feasibility.
    right
    refine ⟨l, ?_, rfl⟩
    rw [problem.mem_dualFeasibleSet_iff]
    refine ⟨hdom, ?_⟩
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hl_nonneg
  · -- Outside the dual domain, the image point collapses to `⊥`.
    left
    exact problem.dualFunction_eq_bot_of_not_mem_dualDomain hdom

/-- The dual optimal value is the supremum of the dual function over the nonnegative orthant. -/
-- Proof sketch: compare the source-level supremum over `ℝ_+^m` with the owner's supremum over
-- `problem.dualFeasibleSet = problem.dualDomain ∩ nonnegativeOrthant m`; multipliers outside
-- `problem.dualDomain` contribute the value `⊥`, so they do not change the supremum.
theorem dualOptimalValue_eq_sSup_image_nonnegativeOrthant
    (problem : LagrangianProblem Q m) :
    problem.dualOptimalValue = sSup (problem.dualFunction '' ℝ₊^m) := by
  -- Compare the owner's feasible-image supremum with the textbook orthant-image supremum.
  rw [LagrangianProblem.dualOptimalValue]
  apply le_antisymm
  · -- The owner's dual-feasible set is contained in the full nonnegative orthant.
    refine sSup_le_sSup ?_
    intro y hy
    rcases hy with ⟨l, hl, rfl⟩
    refine ⟨l, ?_, rfl⟩
    simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using
      (problem.mem_dualFeasibleSet_iff.mp hl).2
  · -- The extra orthant multipliers contribute only `⊥`, which does not change the supremum.
    exact sSup_le_sSup_of_subset_insert_bot <|
      problem.dualFunction_image_nonnegativeOrthant_subset_insert_bot_dualFeasibleSet

end LagrangianProblem
