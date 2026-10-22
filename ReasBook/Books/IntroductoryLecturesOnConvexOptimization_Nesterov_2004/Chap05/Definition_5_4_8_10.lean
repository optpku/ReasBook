/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.8.10 lies in the Chapter 5 entropy-epigraph / barrier-slice domain.

Sampled owner declarations:
* `entropyEpigraphConeBarrier` and `entropyEpigraphConeBarrier_apply` from `Theorem_5_4_7_6`, the
  upstream Chapter 5 owner/view for the entropy-epigraph cone barrier;
* `separableLogBarrierF6` from `Definition_5_4_8_16`, the nearby chapter pattern of realizing a
  planar source-facing barrier directly as an affine slice of an earlier owner;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the lower-level chapter owner used internally by
  `entropyEpigraphConeBarrier`.

Best owner abstraction:
* source-facing: the textbook barrier `F₃`;
* core/canonical: `entropyEpigraphConeBarrier`;
* bridge/view: the affine slice `(x, t) ↦ ((x, 1), t)` and the evaluation theorem below.

Primitive data:
* the upstream entropy-epigraph cone barrier owner;
* the affine slice fixing the second cone coordinate to `1`.

Derived API:
* the source-facing barrier `separableLogBarrierF3`;
* its coordinate formula `separableLogBarrierF3_apply`.

The previous version rebuilt `F₃` as a separate sum of logarithmic barrier factors. The chapter
already owns the same barrier geometry through `entropyEpigraphConeBarrier`, so this refinement
keeps only the source-facing planar specialization and its textbook evaluation formula. -/

/-- Definition 5.4.8.10: the function `F₃` on `ℝ²` given by
`F₃(x, t) = - log x - log (t - x log x)`. -/
def separableLogBarrierF3 : ℝ × ℝ → ℝ :=
  fun p ↦ entropyEpigraphConeBarrier ((p.1, 1), p.2)

-- Proof sketch: `separableLogBarrierF3` is the affine slice `x₂ = 1` of
-- `entropyEpigraphConeBarrier`. Evaluate the owner and simplify `log (x / 1)` and `log 1`.
/-- Evaluating `separableLogBarrierF3` at `(x, t)` recovers the textbook formula
`F₃(x, t) = - log x - log (t - x log x)`. -/
theorem separableLogBarrierF3_apply (x t : ℝ) :
    separableLogBarrierF3 (x, t) = -Real.log x - Real.log (t - x * Real.log x) := by
  rw [separableLogBarrierF3, entropyEpigraphConeBarrier_apply, Real.log_one]
  ring_nf
