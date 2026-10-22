/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 5.4.6.1 lies in the chapter's cone-ordered second-derivative domain for
vector-valued `C³` maps.

Sampled owner declarations:
* `ConvexCone ℝ E₂`, the canonical owner for the ambient cone order;
* `ContDiffOn ℝ 3 ξ (interior Q₁)`, the canonical `C³` owner on the interior domain;
* `iteratedFDerivWithin ℝ 2 ξ (interior Q₁) x (fun _ ↦ h)`, the canonical second within-domain
  directional derivative expression;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the later owner in the same subsection that
  builds on this same derivative-level data.

Source/core/bridge triage:
* source-facing: `IsThreeTimesContDiffConcaveOnWith Q₁ K ξ`;
* core/canonical: mathlib's `ConvexCone`, `ContDiffOn`, and `iteratedFDerivWithin`;
* bridge/view: the class projections together with the inherited closedness instance for `K`.

Primitive data:
* the domain `Q₁`;
* the cone `K`;
* the map `ξ`;
* closedness and convexity of `Q₁`;
* closedness of `K`;
* `C³` regularity of `ξ` on `interior Q₁`;
* the cone-order second-derivative condition on `interior Q₁`.

Derived API:
* the field projections of `IsThreeTimesContDiffConcaveOnWith`;
* the canonical `Fact` instance supplying closedness of the cone owner `K`.

This keeps Definition 5.4.6.1 as the source-facing owner while deleting the exact-interface local
wrapper around `iteratedFDerivWithin`. Closedness of the cone is carried through the canonical
`ConvexCone` owner instead of remaining a parallel primitive projection. -/

/-- Definition 5.4.6.1: a map `ξ : Q₁ → E₂` is three times continuously differentiable and
concave with respect to the closed convex cone `K` when `Q₁` is a closed convex set, `K` is
closed, `ξ` is `C^3` on `interior Q₁`, and `-D²ξ(x)[h,h]` belongs to `K` for every
`x ∈ interior Q₁` and every direction `h`. -/
class IsThreeTimesContDiffConcaveOnWith
    (Q₁ : Set E₁) (K : ConvexCone ℝ E₂) (ξ : E₁ → E₂) : Prop
    extends Fact (IsClosed (K : Set E₂)) where
  /-- The domain set `Q₁` is closed. -/
  isClosed_domain : IsClosed Q₁
  /-- The domain set `Q₁` is convex. -/
  convex_domain : Convex ℝ Q₁
  /-- The map `ξ` is three-times continuously differentiable on `interior Q₁`. -/
  contDiffOn : ContDiffOn ℝ 3 ξ (interior Q₁)
  /-- The negated second within-domain directional derivative of `ξ` belongs to `K` at every
  interior point of `Q₁`. -/
  neg_second_directional_derivative_mem {x : E₁} (hx : x ∈ interior Q₁) (h : E₁) :
      -iteratedFDerivWithin ℝ 2 ξ (interior Q₁) x (fun _ ↦ h) ∈ K

attribute [instance] IsThreeTimesContDiffConcaveOnWith.toFact

end
