/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Text 4.2.20 lies in the cubic-regularization / initial-sublevel-radius domain.

Sampled owner declarations:
* project `cubicallyRegularizedObjective` in `Definition_4_2_16`, the owner of the cubic
  perturbation;
* project `le_cubicallyRegularizedObjective_of_nonneg` in `Definition_4_2_16`, the derived
  monotonicity lemma for nonnegative cubic regularization;
* project `norm_sub_le_of_le_of_initialSublevelDistanceSet_isGreatest` in `Definition_4_2_16`,
  the canonical radius-bound bridge from the source-facing sublevel inequality and an
  `IsGreatest` hypothesis;
* mathlib `IsGreatest`, the canonical owner of the attained-maximum hypothesis.

Source/core/bridge triage:
* source-facing: Text 4.2.20's conclusion that a point with
  `cubicallyRegularizedObjective f δ x₀ x ≤ f x₀` lies within the textbook radius `D`;
* core/canonical: `cubicallyRegularizedObjective f δ x₀`, the canonical sublevel set
  `𝓛[f]((f x₀))`, and `IsGreatest`;
* bridge/view: `initialSublevelDistanceSet f x₀` and the imported owner lemmas relating it to the
  sublevel inequality.

Primitive data:
* the ambient normed additive group `E`;
* the objective `f`, base point `x₀`, and regularization parameter `δ`;
* the attained-maximum radius witness `IsGreatest (initialSublevelDistanceSet f x₀) D`.

Derived API:
* cubic domination of `f` by `cubicallyRegularizedObjective` for `δ ≥ 0`, yielding the
  source-facing sublevel inequality `f x ≤ f x₀`;
* the radius bound coming from the canonical initial-sublevel distance-set owner.

The target statement therefore stays source-facing, but the helper facts are reused from the owner
file and the ambient space is generalized from the concrete model `EuclideanSpace ℝ (Fin n)` to
the intrinsic `NormedAddCommGroup` level already used by the owner API. -/

/-- Text 4.2.20: for a nonnegative cubic regularization parameter, if the cubically regularized
objective at `x` is at most `f x₀`, then `x` belongs to the initial sublevel set
`{y | f y ≤ f x₀}`, hence `‖x - x₀‖` is bounded by any textbook radius `D` that is an attained
maximum of the distances to `x₀` on that sublevel set. -/
theorem norm_sub_le_of_cubicallyRegularizedObjective_le_of_initialSublevelDistanceSet_isGreatest
    (f : E → ℝ) (x0 x : E) {δ : ℝ} (hδ : 0 ≤ δ)
    {D : ℝ}
    (hD : IsGreatest (initialSublevelDistanceSet f x0) D)
    (hx : cubicallyRegularizedObjective f δ x0 x ≤ f x0) :
    ‖x - x0‖ ≤ D := by
  exact
    norm_sub_le_of_le_of_initialSublevelDistanceSet_isGreatest hD
      ((le_cubicallyRegularizedObjective_of_nonneg f x0 x hδ).trans hx)

end
