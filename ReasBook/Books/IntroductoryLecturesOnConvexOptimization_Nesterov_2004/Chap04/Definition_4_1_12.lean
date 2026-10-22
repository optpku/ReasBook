/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_11

-- Declarations for this item will be appended below by the statement pipeline.

/- This item stays in the Chapter 4 cubic-regularized quadratic-subproblem domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the cubic model
  `v`;
* `cubicRegularizedQuadraticObjective_apply` in `Theorem_4_1_11`, the theorem expanding that owner
  to the displayed formula;
* `IsMinOn` in mathlib, the canonical predicate for global minimizers on a set;
* `isMinOn_univ_iff` in mathlib, the bridge from `IsMinOn ... Set.univ ...` to the textbook
  pointwise inequality form.

Best owner abstraction:
* source-facing: `cubicRegularizedQuadraticObjective g H M`;
* core/canonical: `IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ hStar`;
* bridge/view: `isMinOn_univ_iff`.
-/

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (hStar : E)

/- Definition 4.1.12: the cubic-regularized quadratic model
`v(h) = ⟪g, h⟫ + (1 / 2) ⟪H h, h⟫ + (M / 6) ‖h‖^3`
is the existing owner `cubicRegularizedQuadraticObjective`. -/
recall cubicRegularizedQuadraticObjective

/- The owner theorem `cubicRegularizedQuadraticObjective_apply` expands the model to the textbook
formula for `v(h)`. -/
recall cubicRegularizedQuadraticObjective_apply

/- The canonical minimizer owner is `IsMinOn`; the auxiliary minimization problem is its
whole-space specialization to the cubic model. -/
recall IsMinOn

set_option linter.hashCommand false in
#check IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ hStar

/- The textbook inequality form of global minimality over `ℝⁿ` is exactly `isMinOn_univ_iff`. -/
recall isMinOn_univ_iff

set_option linter.hashCommand false in
#check
  (show IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ hStar ↔
      ∀ h : E,
        cubicRegularizedQuadraticObjective g H M hStar ≤
          cubicRegularizedQuadraticObjective g H M h from
    isMinOn_univ_iff)

end
