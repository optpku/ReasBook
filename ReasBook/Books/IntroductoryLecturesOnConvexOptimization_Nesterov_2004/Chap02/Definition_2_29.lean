/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "e₁" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-
Primary domain: elementary Euclidean convex geometry in `ℝ²`, centered around the textbook disk
`Q₁`.

Relevant owner-style declarations sampled before refining:
* `Metric.closedBall`, the canonical owner for closed Euclidean balls;
* `Metric.mem_closedBall`, the owner membership criterion for `closedBall`;
* `dist_eq_norm`, the canonical bridge from metric distance to the Euclidean norm;
* `convex_closedBall`, the standard derived convexity API used downstream.

Best owner abstraction:
* `Q₁ : Set (EuclideanSpace ℝ (Fin 2))`, as the source-facing disk itself.

Primitive data:
* the center `e₁ = (1, 0)`;
* radius `1`.

Derived API:
* the norm-form membership criterion `mem_Q₁_iff`.

Source/core/bridge triage:
* source-facing: the textbook disk `Q₁`;
* core/canonical: `Metric.closedBall e₁ 1`;
* bridge/view: `mem_Q₁_iff`.

This file therefore keeps the source-facing owner `Q₁` and reuses the canonical closed-ball API
directly, without a redundant self-equality wrapper around the definition.
-/

/-- Definition 2.29: `Q₁` is the closed Euclidean unit disk in `ℝ²` centered at `e₁ = (1, 0)`.
-/
def Q₁ : Set E :=
  Metric.closedBall e₁ (1 : ℝ)

/-- Membership in `Q₁` is equivalent to the textbook norm inequality `‖x - e₁‖ ≤ 1`. -/
-- Proof sketch: unfold `Q₁`, rewrite membership in the closed ball using
-- `Metric.mem_closedBall`, and then identify the metric distance with the Euclidean norm via
-- `dist_eq_norm`.
theorem mem_Q₁_iff (x : E) :
    x ∈ Q₁ ↔ ‖x - e₁‖ ≤ (1 : ℝ) := by
  simp [Q₁, Metric.mem_closedBall, dist_eq_norm]

attribute [simp] mem_Q₁_iff
