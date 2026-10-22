/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 1.6.2 is a source-facing recall in the gradient-method step-size domain.

Layer targeted by this refinement:
* source-facing recall of the owner schedule type already used by `gradientMethod`

Primary domain:
* preselected scalar schedules for first-order methods

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`, whose primitive input already includes
  `stepSize : ℕ → ℝ`
* `SatisfiesExactLineSearchAlong` in `Definition_1_6_3.lean`, which treats a schedule as owner
  data and adds optimization properties only as predicates
* `DampedNewton.Method.stepSize` in `Algorithm_1_7_2.lean`, which likewise stores the schedule
  directly as `ℕ → ℝ`
* the constant-step bridge `gradientMethod_const_eq_iterate` in `Algorithm_1_6_1.lean`, which
  uses the literal schedule `fun _ ↦ α` rather than a separate wrapper owner

Source/core/bridge triage:
* source-facing: the prescribed step-size rule `k ↦ hₖ`
* core/canonical: the schedule type `ℕ → ℝ`
* bridge/view: direct literal schedules such as `fun _ ↦ h` or `fun k ↦ h / Real.sqrt (k + 1)`

Owner abstraction:
* the preselected schedule type `ℕ → ℝ`

Primitive data:
* only the scalar rule `k ↦ hₖ`

Derived API:
* positivity and stronger analytic side conditions on a schedule
* textbook examples, which should remain direct literal schedules rather than separate public
  owners

This file therefore keeps the main entry as the canonical type expression itself and shows the
textbook constant and inverse-square-root schedules directly by literal functions. It introduces
no separate public wrapper for either example. -/

#check (ℕ → ℝ)

variable (h : ℝ)

#check ((fun _ ↦ h) : ℕ → ℝ)
#check ((fun k ↦ h / Real.sqrt (k + 1)) : ℕ → ℝ)

end
