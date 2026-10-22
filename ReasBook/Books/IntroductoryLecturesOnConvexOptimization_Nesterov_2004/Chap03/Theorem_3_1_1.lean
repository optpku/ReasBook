/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped WithTopConvexAnalysis

section

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/-
Primary domain: convex analysis for `WithTop ℝ`-valued functions via their finite-value part.

Owner abstractions sampled before refining:
* chapter `dom f` and `withTopRealPart f` in `Definition_3_3`, the canonical owner bridge for
  `WithTop ℝ`-valued convex functions;
* mathlib `ConvexOn`, the canonical convexity owner;
* chapter `convexOn_iff_affine_ray_inequality` in `Theorem_3_2`, the owner affine-ray criterion on
  a convex set.

Best owner abstraction:
* `ConvexOn ℝ (dom f) (withTopRealPart f)`.

Primitive data:
* the function `f : X → WithTop ℝ`.

Derived API:
* convexity of `dom f`;
* the affine-ray lower bound on `withTopRealPart f` over `dom f`.

Source/core/bridge triage:
* source-facing: the textbook affine-ray criterion for an extended-real-valued function;
* core/canonical: `ConvexOn ℝ (dom f) (withTopRealPart f)`;
* bridge/view: the specialization of `convexOn_iff_affine_ray_inequality` to the effective domain.

This file therefore keeps only the source-facing `WithTop` specialization and reuses the earlier
chapter owner surface instead of rebuilding the effective domain as `{x | f x < ⊤}` or the finite
real part as `fun x ↦ (f x).untopD 0`.
-/

/-- Theorem 3.1.1: an `ℝ ∪ {+∞}`-valued function on `ℝⁿ` is convex on its effective domain if and
only if its effective domain is convex and every forward affine extrapolation point
`y + β • (y - x)` that remains in that domain satisfies the secant-line lower bound determined by
`x` and `y`. The statement is generalized from the textbook `ℝⁿ` setting to an arbitrary real
module. -/
-- Proof sketch: apply the owner-level bridge
-- `convexOn_iff_affine_ray_inequality` to the canonical owner
-- `ConvexOn ℝ (dom f) (withTopRealPart f)`, and separate the domain-convexity component.
theorem convexOn_effectiveDomain_iff_affine_ray_inequality
    (f : X → WithTop ℝ) :
    ConvexOn ℝ (dom f) (withTopRealPart f) ↔
      Convex ℝ (dom f) ∧
      ∀ ⦃x y : X⦄, x ∈ dom f → y ∈ dom f →
        ∀ ⦃β : ℝ⦄, 0 ≤ β →
          y + β • (y - x) ∈ dom f →
            withTopRealPart f (y + β • (y - x)) ≥
              withTopRealPart f y + β * (withTopRealPart f y - withTopRealPart f x) := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    exact (convexOn_iff_affine_ray_inequality (dom f) (withTopRealPart f) hf.1).mp hf
  · rintro ⟨hdom, hray⟩
    exact (convexOn_iff_affine_ray_inequality (dom f) (withTopRealPart f) hdom).mpr hray

end
