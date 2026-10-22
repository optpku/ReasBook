/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.8.12 lies in the Chapter 5 logarithmic-sublevel-barrier domain.

Sampled owner declarations:
* `sublevelLogBarrier` and `sublevelLogBarrier_apply` from `Theorem_5_1_4`, the chapter owner for
  barriers of the form `x ↦ -log (β - f x)`;
* `power_cone_barrier` from `Theorem_5_4_7_3`, the higher-level Chapter 5 owner for the same
  power-gap geometry, later reused through the nonnegative slice `((t, 1), x)`;
* `separableLogBarrierF3` from `Definition_5_4_8_10`, the nearby source-facing barrier already
  refined to canonical Chapter 5 owners rather than a raw logarithmic body;
* `hypographBarrierPsi` from `Definition_5_4_7_20`, the generic chapter pattern for keeping a
  source-facing barrier name while reusing the canonical logarithmic-sublevel owner.

Best owner abstraction:
* source-facing: the textbook barrier `F₄`;
* core/canonical: the sum of two `sublevelLogBarrier` factors attached to the gap maps
  `(x, t) ↦ -t` and `(x, t) ↦ x^2 - t^(2 / p)`;
* bridge/view: the coordinate evaluation theorem below, and under the stronger slice condition
  `0 ≤ t`, the later power-cone comparison in `Theorem_5_4_8_5`.

Primitive data:
* the positivity gap map `(x, t) ↦ -t`;
* the epigraph gap map `(x, t) ↦ x^2 - t^(2 / p)`.

Derived API:
* the source-facing barrier `separableLogBarrierF4`;
* its coordinate formula `separableLogBarrierF4_apply`.

This refinement keeps the textbook owner `F₄`, but removes the duplicate raw logarithmic body in
favor of the chapter owner `sublevelLogBarrier`. The upstream power-cone owner is kept as a
bridge only: promoting it to the main definition here would force an extra `0 ≤ t` hypothesis in
the coordinate comparison, so it would shift the source-facing semantics. -/

/-- Definition 5.4.8.12: the function `F₄` on `ℝ²` given by
`F₄(x, t) = - log t - log (t^(2 / p) - x^2)`. -/
def separableLogBarrierF4 (p : ℝ) : ℝ × ℝ → ℝ :=
  sublevelLogBarrier (fun q : ℝ × ℝ ↦ -q.2) 0 +
    sublevelLogBarrier (fun q : ℝ × ℝ ↦ q.1 ^ (2 : ℕ) - Real.rpow q.2 (2 / p)) 0

-- Proof sketch: evaluate the two canonical `sublevelLogBarrier` factors at `(x, t)`. The first
-- becomes `-log t`, and the second becomes `-log (t^(2 / p) - x^2)`.
/-- Evaluating `separableLogBarrierF4 p` at `(x, t)` reproduces the textbook formula
`F₄(x, t) = - log t - log (t^(2 / p) - x^2)`. -/
theorem separableLogBarrierF4_apply (p x t : ℝ) :
    separableLogBarrierF4 p (x, t) =
      -Real.log t - Real.log (Real.rpow t (2 / p) - x ^ (2 : ℕ)) := by
  simp [separableLogBarrierF4, sublevelLogBarrier, sub_eq_add_neg, add_comm]
