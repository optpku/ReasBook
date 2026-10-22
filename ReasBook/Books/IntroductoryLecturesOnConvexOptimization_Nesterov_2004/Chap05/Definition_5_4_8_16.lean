/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.8.16 lies in the Chapter 5 power-cone / epigraph-barrier domain.

Sampled owner declarations:
* `power_cone_plus_barrier` and `power_cone_plus_barrier_apply` from `Theorem_5_4_7_4`, the
  chapter owner for the one-sided power-cone logarithmic barrier;
* `powerConeGeometricMean` from `Definition_5_4_7_1`, the weighted geometric mean
  `x^α t^(1 - α)` appearing in the same barrier geometry;
* `separableLogBarrierF5` from `Definition_5_4_8_14`, the neighboring Chapter 5 pattern of
  keeping a source-facing planar barrier name while defining it through an existing owner.

Best owner abstraction:
* source-facing: the textbook planar barrier `F₆`;
* core/canonical: `power_cone_plus_barrier α`;
* bridge/view: the affine slice `((x, t), 1)` with `α = p / (p + 1)`.

Primitive data:
* the parameter-to-exponent map `p ↦ p / (p + 1)`;
* the affine slice fixing the power-cone coordinate `z = 1`.

Derived API:
* the source-facing barrier `separableLogBarrierF6`;
* its coordinate formula `separableLogBarrierF6_apply`.

The previous file stored the full logarithmic formula as primitive data and added a one-off alias
for the exponent. The chapter already owns the same barrier geometry through
`power_cone_plus_barrier`, so this refinement keeps only the source-facing planar specialization
and its evaluation theorem. -/

/-- Definition 5.4.8.16: the function `F₆` on `ℝ²` given by
`F₆(x, t) = - log x - log t - log (x^α t^(1 - α) - 1)`, where `α = p / (p + 1)`. -/
def separableLogBarrierF6 (p : ℝ) : ℝ × ℝ → ℝ :=
  fun q ↦ power_cone_plus_barrier (p / (p + 1)) (q, 1)

-- Proof sketch: `separableLogBarrierF6` is the affine slice `z = 1` of
-- `power_cone_plus_barrier (p / (p + 1))`. Evaluating the owner and reordering the three
-- logarithmic summands gives the textbook planar formula.
/-- Evaluating `separableLogBarrierF6 p` at `(x, t)` reproduces the textbook formula
`F₆(x, t) = - log x - log t - log (x^α t^(1 - α) - 1)` with `α = p / (p + 1)`. -/
theorem separableLogBarrierF6_apply (p x t : ℝ) :
    separableLogBarrierF6 p (x, t) =
      -Real.log x - Real.log t -
        Real.log
          (Real.rpow x (p / (p + 1)) * Real.rpow t (1 - p / (p + 1)) - 1) := by
  simpa [separableLogBarrierF6, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    power_cone_plus_barrier_apply (p / (p + 1)) x t 1
