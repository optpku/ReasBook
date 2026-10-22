/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.8.14 lies in the Chapter 5 power-cone / barrier-slice domain.

Sampled owner declarations:
* `power_cone_plus_barrier` and `power_cone_plus_barrier_apply` from `Theorem_5_4_7_4`, the
  chapter owner for the one-sided power-cone logarithmic barrier;
* `powerConeGeometricMean` from `Definition_5_4_7_1`, the weighted geometric mean whose unit
  slice gives the same power-gap term `t^p`;
* `separableLogBarrierF6` from `Definition_5_4_8_16`, the neighboring chapter pattern of keeping
  a planar source-facing barrier name while defining it as an affine slice of
  `power_cone_plus_barrier`;
* `separableLogBarrierF4` from `Definition_5_4_8_12`, the adjacent planar barrier still using
  lower-level `sublevelLogBarrier` factors because there is no equally exact upstream owner at
  the same slice level without changing the source semantics.

Best owner abstraction:
* source-facing: the textbook barrier `F₅`;
* core/canonical: `power_cone_plus_barrier p`;
* bridge/view: the affine slice `((t, 1), x)` and the coordinate evaluation theorem below.

Primitive data:
* the upstream owner `power_cone_plus_barrier p`;
* the affine slice fixing the second cone coordinate to `1`.

Derived API:
* the source-facing barrier `separableLogBarrierF5`;
* its coordinate formula `separableLogBarrierF5_apply`.

The previous version kept a lower-level sum of `sublevelLogBarrier` factors as primitive data.
That geometry is already owned upstream by `power_cone_plus_barrier`, and the neighboring `F₆`
file already uses the same slice-based pattern. This refinement keeps the textbook owner `F₅`,
but presents it directly as the affine slice of the existing power-cone barrier owner. -/

/-- Definition 5.4.8.14: the function `F₅` on `ℝ²` given by
`F₅(x, t) = - log t - log (t^p - x)`. -/
def separableLogBarrierF5 (p : ℝ) : ℝ × ℝ → ℝ :=
  fun q ↦ power_cone_plus_barrier p ((q.2, 1), q.1)

-- Proof sketch: `separableLogBarrierF5` is the affine slice `((t, 1), x)` of
-- `power_cone_plus_barrier p`. Evaluate the owner and simplify `log 1 = 0` and
-- `1 ^ (1 - p) = 1`.
/-- Evaluating `separableLogBarrierF5 p` at `(x, t)` reproduces the textbook formula
`F₅(x, t) = - log t - log (t^p - x)`. -/
theorem separableLogBarrierF5_apply (p x t : ℝ) :
    separableLogBarrierF5 p (x, t) = -Real.log t - Real.log (Real.rpow t p - x) := by
  rw [separableLogBarrierF5, power_cone_plus_barrier_apply]
  simp [sub_eq_add_neg, add_comm]
