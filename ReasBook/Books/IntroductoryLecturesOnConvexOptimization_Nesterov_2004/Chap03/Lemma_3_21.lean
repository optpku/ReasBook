/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

section

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/- Lemma 3.21 lies in the chapter's finite-dimensional Lagrangian-duality domain.

Primary domain:
- inequality-constrained Lagrangian duality with complementary slackness

Sampled owner-style declarations:
- `LagrangianProblem.lagrangian`, `LagrangianProblem.lagrangianMinimizers`,
  `LagrangianProblem.constraintVector`, and `LagrangianProblem.feasibleSet` in
  `Chap01/Definition_1_10_2`
- `LagrangianProblem.dualFunction_le_affine_support_of_mem_lagrangianMinimizers` in
  `Chap01/Proposition_1_10_7`
- `LagrangianProblem.dualOptimalValue_le_primalOptimalValue` in `Chap01/Proposition_1_10_8`
- downstream recall `objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer` in
  `Chap03/Lemma_3_1_21`

Best owner abstraction:
- `problem : LagrangianProblem Q m`

Primitive data:
- the owner `problem`
- the points `xStar`, `xBar`
- the multiplier `lambdaStar`

Derived API:
- the owner Lagrangian-minimizer fiber `problem.lagrangianMinimizers lambdaStar`
- the Lagrangian `problem.lagrangian`
- the coordinate constraint family `problem.constraints`

Source/core/bridge triage:
- source-facing: the textbook objective-gap inequality obtained from a Lagrangian minimizer and
  complementary slackness
- core/canonical: the Chapter 1 owner `LagrangianProblem`
- bridge/view: the downstream recall-only restatement in `Lemma_3_1_21`

The source prose includes nonnegativity of the multiplier and feasibility of the comparison point,
but those hypotheses are redundant for this particular inequality once one works directly with the
owner Lagrangian-minimizer condition and complementary slackness. The refined owner statement
therefore drops those unused guards instead of preserving them as cosmetic API noise.
-/

/-- Lemma 3.21: if `xStar` minimizes the Lagrangian associated to `lambdaStar` and
complementary slackness holds at `xStar`, then the objective gap at `xBar` dominates the
multiplier-weighted constraint violation. -/
-- Proof sketch: apply the minimizing property of the Lagrangian at `xStar` to `xBar`, rewrite
-- the complementary-slackness term at `xStar` to zero, and rearrange the remaining Lagrangian
-- term at `xBar`.
lemma objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer
    (problem : LagrangianProblem Q m) {xStar xBar : Q} {lambdaStar : Λ}
    (h_lagrangian_min : xStar ∈ problem.lagrangianMinimizers lambdaStar)
    (h_complementary_slackness :
      ∀ i : Fin m, lambdaStar i * problem.constraints i xStar = 0)
    :
    problem xBar - problem xStar ≥
      ∑ i, (-(problem.constraints i xBar)) * lambdaStar i := by
  have hinner_eq (x : Q) :
      inner ℝ lambdaStar (problem.constraintVector x) =
        ∑ i, lambdaStar i * problem.constraints i x := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa using (RCLike.inner_apply' (lambdaStar i) (problem.constraints i x))
  have hlag : problem xStar ≤ problem xBar + ∑ i, problem.constraints i xBar * lambdaStar i := by
    have hlag' : problem.lagrangian xStar lambdaStar ≤ problem.lagrangian xBar lambdaStar := by
      exact (problem.mem_lagrangianMinimizers_iff.mp h_lagrangian_min) (by simp)
    simpa [LagrangianProblem.lagrangian, hinner_eq,
      h_complementary_slackness, add_comm, add_left_comm, add_assoc, mul_comm] using hlag'
  have hsum :
      ∑ i, (-(problem.constraints i xBar)) * lambdaStar i =
        -(∑ i, problem.constraints i xBar * lambdaStar i) := by
    simp [Finset.sum_neg_distrib, mul_comm]
  rw [hsum]
  linarith

end
