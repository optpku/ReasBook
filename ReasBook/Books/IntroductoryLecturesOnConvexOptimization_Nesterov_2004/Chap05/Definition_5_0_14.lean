/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped DikinEllipsoidNotation

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.0.14 lies in the Hessian-local-norm / Dikin-ellipsoid domain.

Sampled owner declarations:
* `hessianLocalNorm` in `Definition_5_1_1`, the chapter owner for the Hessian local norm;
* `hessianLocalNorm_def` in `Definition_5_1_1`, the canonical owner expansion;
* `openDikinEllipsoid` and the notation `W⁰[f; x](r)` in `Definition_5_0_13`, the chapter owner
  for the Dikin-radius neighborhood;
* `mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq` in `Definition_5_0_13`, the owner-level
  quadratic membership bridge.

Source/core/bridge triage:
* source-facing: the textbook radius-`1 / M_f` open Dikin neighborhood condition;
* core/canonical: `openDikinEllipsoid f x r`;
* bridge/view: the specialized quadratic membership theorem below.

Primitive data:
* a function `f`;
* a center `x`;
* a self-concordance parameter `Mf`;
* a point `y`.

Derived API:
* the special radius `r = 1 / M_f`;
* the source-facing Dikin neighborhood `W⁰[f; x](1 / (Mf : ℝ))`;
* the corresponding quadratic inequality `⟪∇² f(x) (y - x), y - x⟫ < 1 / M_f^2`.

This item stays source-facing by specializing the chapter owner `openDikinEllipsoid` to the
textbook radius `1 / M_f`, while keeping the generic Dikin-ellipsoid owner in
`Definition_5_0_13`. -/

variable (f : E → ℝ) (x : E) (Mf : NNReal)

/- Definition 5.0.14 specializes the chapter owner to the textbook inverse-parameter Dikin
neighborhood `W⁰[f; x](1 / M_f)`. -/
#check W⁰[f; x](1 / (Mf : ℝ))

variable {f x Mf}

/-- Membership in the textbook inverse-parameter Dikin neighborhood is equivalent to the strict
inverse-square Hessian quadratic bound. -/
theorem mem_openDikinEllipsoid_inv_constant_iff_hessian_quadratic_lt_inv_sq
    (f : E → ℝ) (x y : E) (Mf : NNReal)
    (hquad_nonneg : 0 ≤ inner ℝ (y - x) (hessian f x (y - x))) :
    y ∈ W⁰[f; x](1 / (Mf : ℝ)) ↔
      inner ℝ (y - x) (hessian f x (y - x)) < 1 / (Mf : ℝ) ^ (2 : ℕ) := by
  simpa [one_div] using
    (mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq
      f x y hquad_nonneg (by positivity : 0 ≤ 1 / (Mf : ℝ)))
