/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped ConvexAnalysis

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

/- Theorem 3.1.1.1 lies in the chapter's `EReal`-valued convex-analysis domain.

Relevant owner-style declarations sampled before refinement:
- chapter `dom f` and `extendedRealRealPart f` in `Definition_3_1_1_3`, the canonical owner bridge
  from an `EReal`-valued function to its finite real part on the effective domain;
- mathlib `ConvexOn`, the canonical convexity owner;
- chapter `convexOn_iff_affine_ray_inequality` in `Theorem_3_2`, the owner affine-ray criterion
  on a convex set.

Best owner abstraction:
- `ConvexOn ℝ (dom f) (extendedRealRealPart f)`.

Primitive data:
- the function `f : X → EReal`.

Derived API:
- convexity of `dom f`;
- the affine-ray lower bound for `extendedRealRealPart f` on `dom f`.

Source/core/bridge triage:
- source-facing: the textbook affine-ray criterion for an extended-real-valued function;
- core/canonical: `ConvexOn ℝ (dom f) (extendedRealRealPart f)`;
- bridge/view: the specialization of `convexOn_iff_affine_ray_inequality` to the effective domain.

This file therefore keeps only the source-facing `EReal` specialization and reuses the earlier
chapter owner surface directly, instead of rebuilding a parallel convexity owner for the
finite-real-part model.
-/

/-- Theorem 3.1.1.1: an extended-real-valued function on a real additive module is convex exactly
when its effective domain is convex and every forward affine extrapolation point `y + β • (y - x)`
in that domain satisfies the supporting-line inequality determined by the secant through `x` and
`y`. Specializing `X` to `EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` statement. -/
-- Proof sketch: apply the owner-level bridge
-- `convexOn_iff_affine_ray_inequality` from `Theorem_3_2` to the canonical owner
-- `ConvexOn ℝ (dom f) (extendedRealRealPart f)`, then split off the domain-convexity component.
theorem isConvexExtendedRealFunction_iff_affine_ray_inequality
    (f : X → EReal) :
    ConvexOn ℝ (dom f) (extendedRealRealPart f) ↔
      Convex ℝ (dom f) ∧
      ∀ ⦃x y : X⦄, x ∈ dom f → y ∈ dom f →
        ∀ ⦃β : ℝ⦄, 0 ≤ β →
          y + β • (y - x) ∈ dom f →
            extendedRealRealPart f (y + β • (y - x)) ≥
              extendedRealRealPart f y +
                β * (extendedRealRealPart f y - extendedRealRealPart f x) := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    exact (convexOn_iff_affine_ray_inequality (dom f) (extendedRealRealPart f) hf.1).mp hf
  · rintro ⟨hdom, hray⟩
    exact (convexOn_iff_affine_ray_inequality (dom f) (extendedRealRealPart f) hdom).mpr hray

end
