/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_21

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.21 lies in the chapter's finite-dimensional Lagrangian-duality domain.

Primary domain:
- inequality-constrained Lagrangian duality with complementary slackness

Sampled owner-style declarations:
- `LagrangianProblem.lagrangian` and `LagrangianProblem.lagrangianMinimizers` in
  `Chap01/Definition_1_10_2`
- `LagrangianProblem.dualOptimalValue_le_primalOptimalValue` in
  `Chap01/Proposition_1_10_8`
- `objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer` in
  `Chap03/Lemma_3_21`

Best owner abstraction:
- the existing Chapter 3 theorem
  `objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer`, stated using the
  owner `problem : LagrangianProblem Q m` together with the derived API
  `problem.lagrangianMinimizers`

Primitive data:
- the Lagrangian owner `problem : LagrangianProblem Q m`
- the points `xStar`, `xBar`
- the multiplier vector `lambdaStar`

Derived API:
- the owner Lagrangian-minimizer fiber `problem.lagrangianMinimizers lambdaStar`
- complementary slackness at `xStar`

Source/core/bridge triage:
- source-facing: the textbook objective-gap inequality derived from a Lagrangian minimizer and
  complementary slackness
- core/canonical: the Chapter 1 owner `LagrangianProblem` and its `IsMinOn` Lagrangian-minimizer
  interface
- bridge/view: the previous local theorem name, which duplicated `Lemma_3_21` without adding new
  mathematics

The former file introduced a second public theorem name with exactly the same interface as the
existing chapter theorem in `Lemma_3_21`. This refinement keeps Lemma 3.1.21 as direct canonical
recall/use instead of a parallel wrapper theorem.
-/
recall objective_gap_ge_weighted_constraint_violation_of_lagrangian_minimizer
