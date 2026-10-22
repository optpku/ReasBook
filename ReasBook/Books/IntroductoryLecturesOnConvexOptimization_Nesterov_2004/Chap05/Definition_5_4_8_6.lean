/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_5

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 5.4.8.6 lies in the Chapter 5 strict-epigraph logarithmic-barrier domain.

Sampled owner declarations:
* `epigraphLogBarrier` from `Theorem_5_3_5`, the chapter owner for raw-pair epigraph
  logarithmic barriers;
* `epigraphLogBarrier_apply` from `Theorem_5_3_5`, the canonical evaluation bridge for that
  owner;
* `strictConstrainedEpigraph` from `Theorem_5_3_5`, the matching strict-epigraph domain owner;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the closed-epigraph owner whose interior
  is the source domain for this barrier.

Best owner abstraction:
* core/canonical: `epigraphLogBarrier (fun x : ℝ ↦ -Real.log x)`.

Primitive data:
* the base function `x ↦ -Real.log x`.

Derived API:
* the source-facing barrier `F₁`;
* its textbook coordinate formula, obtained from `epigraphLogBarrier_apply`.

Source/core/bridge triage:
* source-facing: the textbook barrier `F₁`;
* core/canonical: `epigraphLogBarrier`;
* bridge/view: the specialized evaluation of that owner at `(x, t)`.

This item adds no new owner beyond the chapter epigraph-barrier API, so the parallel local alias
`separableLogBarrierF1` is deleted. Downstream files should use
`epigraphLogBarrier (fun x : ℝ ↦ -Real.log x)` directly.
-/

/- Definition 5.4.8.6 recalls the canonical epigraph logarithmic barrier specialized to
`x ↦ -log x`. -/
#check (epigraphLogBarrier (fun x : ℝ ↦ -Real.log x) : ℝ × ℝ → ℝ)

/-- The textbook coordinate formula for Definition 5.4.8.6 is the specialized evaluation of the
canonical epigraph logarithmic barrier owner. -/
theorem epigraphLogBarrier_negLog_apply (x t : ℝ) :
    epigraphLogBarrier (fun y : ℝ ↦ -Real.log y) (x, t) =
      -Real.log x - Real.log (Real.log x + t) := by
  rw [epigraphLogBarrier_apply]
  simp [sub_eq_add_neg, add_comm]
