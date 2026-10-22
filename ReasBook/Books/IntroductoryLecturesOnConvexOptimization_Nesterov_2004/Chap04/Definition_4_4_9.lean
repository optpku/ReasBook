/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 4.4.9 lies in the merit-scalarization / convex-Lipschitz residual domain.

Primary domain:
* sharp residual scalarizations used in merit reformulations of nonlinear equations

Sampled owner-style declarations:
* `IsMeritFunction` in `Definition_4_4_1`, the chapter owner for residual scalarizers that are
  nonnegative and vanish exactly at the origin
* `convexOn_univ_norm` in mathlib, the canonical convexity owner for the norm on a real normed
  space
* `lipschitzWith_one_norm'` in mathlib, the canonical `1`-Lipschitz owner for the norm
* `norm_eq_zero` in mathlib, the canonical zero-detection theorem for the norm

Best owner abstraction:
* source-facing: the sharp merit-function property of a residual scalarizer
* core/canonical: `IsMeritFunction` together with the canonical mathlib owners `ConvexOn`,
  `LipschitzWith`, and `‖·‖`
* bridge/view: the textbook specialization to `ℝ^m = EuclideanSpace ℝ (Fin m)`

Primitive data:
* a scalarizer `φ : E → ℝ` on a real normed residual space

Derived API:
* the canonical norm example
* the Euclidean `ℝ^m` specialization used downstream in the chapter

This refinement keeps the source-facing owner `IsSharpMeritFunction`, but moves it from the
coordinate model `ℝ^m` to the intrinsic real normed-space layer. The Euclidean residual space
then becomes a direct specialization rather than primitive owner data.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Definition 4.4.9: a sharp merit function on a real normed residual space is a merit
function that is convex, `1`-Lipschitz, and has a sharp minimum at the origin with some constant
in `(0, 1]`. -/
class IsSharpMeritFunction (φ : E → ℝ) : Prop extends IsMeritFunction φ where
  /-- A sharp merit function is convex on the whole residual space. -/
  convex : ConvexOn ℝ Set.univ φ
  /-- A sharp merit function is `1`-Lipschitz. -/
  lipschitz_one : LipschitzWith 1 φ
  /-- A sharp merit function dominates the ambient norm by some factor in `(0, 1]`. -/
  sharp_origin : ∃ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) 1 ∧ ∀ u : E, γ * ‖u‖ ≤ φ u

/-- The norm on a real normed residual space is a sharp merit function. -/
-- Proof sketch: `convexOn_univ_norm` and the canonical distance-right `LipschitzWith` owner
-- give convexity and
-- `1`-Lipschitz continuity, while the sharp lower bound holds with `γ = 1`.
theorem norm_isSharpMeritFunction :
    IsSharpMeritFunction (norm : E → ℝ) := by
  refine
    { toIsMeritFunction :=
        { nonneg := norm_nonneg
          eq_zero_iff := fun u ↦ norm_eq_zero }
      convex := convexOn_univ_norm
      lipschitz_one := by
        simpa [dist_eq_norm] using (LipschitzWith.dist_right (0 : E))
      sharp_origin := ⟨1, by simp, fun u ↦ by simp⟩ }

/-- The norm supplies the canonical sharp-merit-function instance on every real normed residual
space, including the textbook specialization `ℝ^m`. -/
instance : IsSharpMeritFunction (norm : E → ℝ) :=
  norm_isSharpMeritFunction
