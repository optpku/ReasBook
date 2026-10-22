/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {R : Type u} [Zero R]
variable {m : ℕ}

/- Definition 4.4.1 lies in the merit-scalarization domain.

Sampled owner-style declarations:
- `norm_eq_zero` in mathlib, the canonical zero-detection theorem for norm-based scalarizers;
- `EuclideanSpace.real_norm_sq_eq` in mathlib, the canonical `ℝ^m` sum-of-squares formula;
- `IsSharpMeritFunction` in `Definition_4_4_9`, the chapter owner extending the same
  merit-function core;
- ordinary function composition for the scalarization `x ↦ φ (F x)`.

Best owner abstractions:
- source-facing: the intrinsic merit-function property of a residual scalarizer `φ : R → ℝ`;
- core/canonical: the reusable owner `IsMeritFunction` on a residual type carrying `0`;
- bridge/view: the Euclidean specialization `u ↦ ‖u‖₂²` on `ℝ^m`, expressed directly by the
  canonical squared norm.

Primitive data:
- a scalarizer `φ : R → ℝ` on a residual type with a distinguished origin.

Derived API:
- the Euclidean model example `u ↦ ‖u‖₂²`;
- downstream residual scalarizations such as `x ↦ φ (F x)`, built by ordinary composition from
  this owner.

This file therefore keeps the public owner intrinsic and lets the finite-coordinate `ℝ^m`
presentation appear only in the Euclidean specialization and downstream composition bridges,
without introducing a second public owner for the squared norm.
-/

/-- Definition 4.4.1: a merit function on a residual type with distinguished origin `0` is a
nonnegative scalarization that vanishes exactly at the origin, so it can be used in merit
reformulations `x ↦ φ (F x)`. -/
class IsMeritFunction (φ : R → ℝ) : Prop where
  /-- A merit function is everywhere nonnegative. -/
  nonneg (u : R) : 0 ≤ φ u
  /-- A merit function vanishes exactly at the origin. -/
  eq_zero_iff (u : R) : φ u = 0 ↔ u = 0

/-- The canonical squared Euclidean norm on `ℝ^m` is a merit function. -/
theorem euclideanNormSq_isMeritFunction (m : ℕ) :
    IsMeritFunction (fun u : EuclideanSpace ℝ (Fin m) ↦ ‖u‖ ^ (2 : ℕ)) := by
  refine
    { nonneg := fun u ↦ by simpa [pow_two] using sq_nonneg ‖u‖
      eq_zero_iff := fun u ↦ by
        exact sq_eq_zero_iff.trans norm_eq_zero }

/-- The canonical squared Euclidean norm provides the textbook merit-function instance on
`ℝ^m`. -/
instance (m : ℕ) : IsMeritFunction (fun u : EuclideanSpace ℝ (Fin m) ↦ ‖u‖ ^ (2 : ℕ)) :=
  euclideanNormSq_isMeritFunction m

end
