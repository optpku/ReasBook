/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_7

noncomputable section

open scoped Gradient

universe u v

/- Lemma 6.2.2 lies in the chapter's smoothed primal objective / tangent-plane domain.

Sampled owner declarations:
- `smoothedPrimalObjectiveMaximand`, `smoothedPrimalObjective`, and
  `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the chapter
  owners for the regularized dual maximand, the smoothed objective, and its
  canonical argmax set;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Chap06/Definition_6_30`, the
  thin bridge from argmax membership to the underlying feasible-maximizer
  conditions;
- `smoothedPrimalObjective_linearization_le_selected_dual_value` in
  `Chap06/Lemma_6_7`, the immediate source-facing chapter theorem that packages
  the supporting-nesterovHyperplane step for `hatf` together with the selected dual
  maximizer;
- `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in
  `Chap02/Definition_2_2`, the project owner for the first-order supporting
  inequality on a convex feasible set;
- `smoothedPrimalObjective_argmax_unique_and_hasGradientWithinAt` in
  `Chap06/Proposition_6_24`, which confirms that the canonical Chapter 6
  gradient surface is expressed through `smoothedPrimalObjective`,
  `smoothedPrimalObjectiveArgmax`, and `A.flip`.

Best owner abstraction:
- source-facing: the one-point linearization bound at a selected dual argmax;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`,
  `ConvexOn`, `HasGradientWithinAt`, and `A.flip`;
- bridge/view: a chosen point `u` in the canonical argmax owner together with
  the displayed gradient formula.

Primitive data:
- the dual-valued linear map `A`;
- the feasible sets `Q₁` and `Q₂`;
- the functions `hatf`, `hatφ`, and `d₂`;
- the smoothing parameter `μ₂`;
- the selected dual point `u`;
- convexity of `hatf` on `Q₁`;
- the canonical within-set gradient witness for `hatf` at the base point;
- the owner-level within-set gradient witness for the smoothed primal objective
  at the base point;
- membership of `u` in the canonical argmax set at `xhat`;
- pointwise nonnegativity of `d₂` at the selected dual point `u`.

Derived API:
- the value of the smoothed objective at the selected argmax;
- the supporting-nesterovHyperplane inequality for `hatf`;
- on `UniqueDiffWithinAt` sets, the displayed `gradientWithin` equality for the
  smoothed objective.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: the owner declarations from `Definition_6_30` and
  `Definition_2_2`;
- bridge/view: the pointwise selected maximizer `u`.

The previous version introduced duplicate local owners
`smoothedObjectiveIntegrand`, `primalDualSmoothedObjective`, and
`IsSmoothedMaximizerSelectionOn`. Those were exact re-encodings of the Chapter 6
owners in `Definition_6_30`, so this file now states the source-facing lemma
directly against the canonical API.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

-- Proof sketch: apply `smoothedPrimalObjective_linearization_le_selected_dual_value`
-- at the selected dual point `u` and rewrite the affine pairing term
-- using the transpose identity
-- `⟪(InnerProductSpace.toDual ℝ E₁).symm (A.flip u), v⟫ = A v u`.
/-- Lemma 6.2.2: if `u` lies in the canonical argmax set of the
regularized dual representation of the smoothed primal objective, then the
affine linearization at `xhat` written with the explicit vector
`∇ \hat f(xhat) + A^* u` is bounded above by the selected dual value. -/
theorem smoothedPrimalObjective_linearization_le_selected_dual_value_of_explicit_gradient
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} (hhatf_conv : ConvexOn ℝ Q₁ hatf)
    (hμ₂ : 0 ≤ μ₂) {u : E₂} {x xhat : E₁} (hx : x ∈ Q₁) (hxhat : xhat ∈ Q₁)
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat)
    (hhatf_grad :
      HasGradientWithinAt hatf (gradientWithin hatf Q₁ xhat) Q₁ xhat)
    (hd₂_nonneg : 0 ≤ d₂ u) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
      inner ℝ
        (gradientWithin hatf Q₁ xhat +
          (InnerProductSpace.toDual ℝ E₁).symm (A.flip u))
        (x - xhat) ≤
      hatf x + A x u - hatφ u := by
  have hlinear :=
    smoothedPrimalObjective_linearization_le_selected_dual_value
      A hhatf_conv hμ₂ hx hxhat hu hhatf_grad hd₂_nonneg
  have hpair :
      inner ℝ
          ((InnerProductSpace.toDual ℝ E₁).symm (A.flip u))
          (x - xhat) =
        A (x - xhat) u := by
    rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.flip_apply]
  rw [inner_add_left, hpair]
  simpa [add_assoc] using hlinear

-- Proof sketch: recover the canonical `gradientWithin` value from the explicit
-- within-set gradient witness using `HasFDerivWithinAt.fderivWithin` on the
-- `UniqueDiffWithinAt` set `Q₁` at `xhat`.
/-- On a `UniqueDiffWithinAt` feasible set, the owner-level gradient witness
used in Lemma 6.2.2 rewrites the canonical `gradientWithin` of the smoothed
primal objective to `∇ \hat f(xhat) + A^* u`. -/
theorem smoothedPrimalObjective_gradientWithin_eq_gradientWithin_add_selected_dual
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {u : E₂} {xhat : E₁}
    (hfμ₂_grad :
      HasGradientWithinAt (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂)
        (gradientWithin hatf Q₁ xhat +
          (InnerProductSpace.toDual ℝ E₁).symm (A.flip u)) Q₁ xhat)
    (hQ₁_unique : UniqueDiffWithinAt ℝ Q₁ xhat) :
    gradientWithin (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂) Q₁ xhat =
      gradientWithin hatf Q₁ xhat +
        (InnerProductSpace.toDual ℝ E₁).symm (A.flip u) := by
  simpa [gradientWithin] using
    congrArg ((InnerProductSpace.toDual ℝ E₁).symm)
      (hfμ₂_grad.hasFDerivWithinAt.fderivWithin hQ₁_unique)

-- Proof sketch: rewrite the canonical `gradientWithin` of the smoothed
-- objective using the explicit within-set gradient witness, then apply the
-- source-facing explicit-gradient theorem above.
/-- Companion bridge theorem for Lemma 6.2.2: on a `UniqueDiffWithinAt`
feasible set, an explicit within-set gradient witness for the smoothed primal
objective rewrites the canonical `gradientWithin` linearization to the
source-facing explicit-gradient form. -/
theorem
    smoothedPrimalObjective_gradientWithin_linearization_le_selected_dual_value_of_uniqueDiff
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} (hhatf_conv : ConvexOn ℝ Q₁ hatf)
    (hμ₂ : 0 ≤ μ₂) {u : E₂} {x xhat : E₁} (hx : x ∈ Q₁) (hxhat : xhat ∈ Q₁)
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat)
    (hhatf_grad :
      HasGradientWithinAt hatf (gradientWithin hatf Q₁ xhat) Q₁ xhat)
    (hfμ₂_grad :
      HasGradientWithinAt (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂)
        (gradientWithin hatf Q₁ xhat +
          (InnerProductSpace.toDual ℝ E₁).symm (A.flip u)) Q₁ xhat)
    (hQ₁_unique : UniqueDiffWithinAt ℝ Q₁ xhat)
    (hd₂_nonneg : 0 ≤ d₂ u) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
      inner ℝ
        (gradientWithin (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂) Q₁ xhat)
        (x - xhat) ≤
      hatf x + A x u - hatφ u := by
  rw [smoothedPrimalObjective_gradientWithin_eq_gradientWithin_add_selected_dual
    A hfμ₂_grad hQ₁_unique]
  exact
    smoothedPrimalObjective_linearization_le_selected_dual_value_of_explicit_gradient
      A hhatf_conv hμ₂ hx hxhat hu hhatf_grad hd₂_nonneg

end
