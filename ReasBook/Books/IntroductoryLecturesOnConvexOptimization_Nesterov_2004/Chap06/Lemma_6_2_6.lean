/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Lemma 6.2.6 lies in Chapter 6's attained dual-objective / linearization domain.

Mandatory domain-style sampling before refinement:
- `smoothedDualObjectiveMinimand` and `smoothedDualObjective` in `Chap06/Proposition_6_25`, the
  canonical Chapter 6 owner surface for the zero-smoothing dual slice used here;
- `smoothedDualObjective_argmin_unique_and_hasGradientWithinAt` in `Chap06/Proposition_6_25`, the
  local gradient owner for attained smoothed-dual slices;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the more general
  chapter owner for the same dual value construction.

Best owner abstraction:
- source-facing: the linearization lower bound at a fixed dual point `uHat`, expressed through a
  primal argmin witness for the corresponding zero-smoothing slice;
- core/canonical: `smoothedDualObjective A Q₁ hatf hatφ 0 0` and
  `argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 uHat)`;
- bridge/view: the displayed real-valued lower bound in the theorem below.

This file should not define or recall a second public owner for the unsmoothed dual value. The
refinement below therefore uses the chapter's zero-smoothing `smoothedDualObjective` surface
directly.
-/

/-- Helper for Lemma 6.2.6: the zero-smoothing dual objective at `uHat` equals the attained
primal-slice value at the selected minimizer `xHat`. -/
private theorem dual_objective_value_at_selected_argmin
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {uHat : E₂} {xHat : E₁}
    (hxHat : xHat ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 uHat)) :
    extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0) uHat =
      -hatφ uHat + A xHat uHat + hatf xHat := by
  -- Unpack the argmin witness into feasibility and exact minimality on the fixed `uHat` slice.
  rcases mem_constrainedArgmin_iff.mp hxHat with ⟨hxHat_mem, hxHat_min⟩
  have hsInf_eq :
      sInf (smoothedDualObjectiveMinimand A hatf 0 0 uHat '' Q₁) =
        smoothedDualObjectiveMinimand A hatf 0 0 uHat xHat := by
    -- The selected minimizer realizes the infimum of the feasible image set.
    have hglb :
        IsGLB
          (smoothedDualObjectiveMinimand A hatf 0 0 uHat '' Q₁)
          (smoothedDualObjectiveMinimand A hatf 0 0 uHat xHat) :=
      hxHat_min.isGLB hxHat_mem
    have hnonempty :
        (smoothedDualObjectiveMinimand A hatf 0 0 uHat '' Q₁).Nonempty := by
      exact ⟨_, ⟨xHat, hxHat_mem, rfl⟩⟩
    simpa using hglb.csInf_eq hnonempty
  -- Expand the dual objective and replace its infimum term by the attained primal-slice value.
  rw [extendedRealRealPart_eq_toReal, smoothedDualObjective_apply, hsInf_eq,
    smoothedDualObjectiveMinimand_apply]
  simpa [add_assoc] using (EReal.toReal_coe (-hatφ uHat + A xHat uHat + hatf xHat))

/-- Helper for Lemma 6.2.6: the linearization pairing of the dual objective at `uHat` rewrites to
the source-side affine term `A xHat u - A xHat uHat` minus the `\hat φ` gradient pairing. -/
private theorem dual_objective_gradient_pairing_eq
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {u uHat : E₂} {xHat : E₁}
    (hdual_grad :
      HasGradientAt
        (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
        (-∇ hatφ uHat + (InnerProductSpace.toDual ℝ E₂).symm (A xHat)) uHat) :
    inner ℝ (∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) uHat)
        (u - uHat) =
      -inner ℝ (∇ hatφ uHat) (u - uHat) + (A xHat u - A xHat uHat) := by
  -- Replace the canonical gradient by the explicit vector field supplied by `hdual_grad`.
  rw [hdual_grad.gradient, inner_add_left, inner_neg_left, InnerProductSpace.toDual_symm_apply]
  -- Linearity of `A xHat` converts the displacement pairing into the source-side affine increment.
  simp [map_sub]

/-- Helper for Lemma 6.2.6: convexity of `\hat φ` gives its lower tangent-plane inequality at the
base point `uHat`. -/
private theorem hatphi_lower_tangent_at_base
    {Q₂ : Set E₂} {hatφ : E₂ → ℝ} {u uHat : E₂}
    (hhatφ_convex : ConvexOn ℝ Q₂ hatφ)
    (hu : u ∈ Q₂) (huHat : uHat ∈ Q₂)
    (hhatφ_grad : HasGradientAt hatφ (∇ hatφ uHat) uHat) :
    hatφ u ≥ hatφ uHat + inner ℝ (∇ hatφ uHat) (u - uHat) := by
  -- Turn the ambient gradient witness into the within-set gradient required by the convex API.
  have hhatφ_grad_within : HasGradientWithinAt hatφ (∇ hatφ uHat) Q₂ uHat := by
    simpa using hhatφ_grad.hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
  -- Apply the standard supporting-nesterovHyperplane inequality on the convex feasible set `Q₂`.
  exact hhatφ_convex.lower_tangent_plane_of_hasGradientWithinAt
    uHat huHat (∇ hatφ uHat) hhatφ_grad_within u hu

/-- Lemma 6.2.6: for `u, \hat u ∈ Q₂`, if `xHat` solves the fixed-`\hat u` zero-smoothing primal
slice, then the affine linearization of the dual objective at `\hat u` dominates
`-\hat φ(u) + A xHat u + \hat f(xHat)`. -/
-- Proof sketch: expand the zero-smoothing smoothed-dual owner at `uHat`, use the argmin witness
-- `hxHat` for the attained primal slice, identify the dual gradient from `hdual_grad`, and apply
-- the first-order convexity inequality for `hatφ` on `Q₂`.
theorem dualObjective_linearization_lower_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    (hhatφ_convex : ConvexOn ℝ Q₂ hatφ)
    {u uHat : E₂} {xHat : E₁}
    (hxHat : xHat ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 uHat))
    (hu : u ∈ Q₂) (huHat : uHat ∈ Q₂)
    (hhatφ_grad : HasGradientAt hatφ (∇ hatφ uHat) uHat)
    (hdual_grad :
      HasGradientAt
        (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
        (-∇ hatφ uHat + (InnerProductSpace.toDual ℝ E₂).symm (A xHat)) uHat) :
    extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0) uHat +
      inner ℝ (∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) uHat)
        (u - uHat) ≥
        -hatφ u + A xHat u + hatf xHat := by
  -- Evaluate the dual objective at `uHat` through the selected minimizer `xHat`.
  have hvalue :
      extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0) uHat =
        -hatφ uHat + A xHat uHat + hatf xHat :=
    dual_objective_value_at_selected_argmin A hxHat
  -- Rewrite the gradient pairing into the source-side affine increment at `xHat`.
  have hpair :
      inner ℝ (∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) uHat)
          (u - uHat) =
        -inner ℝ (∇ hatφ uHat) (u - uHat) + (A xHat u - A xHat uHat) :=
    dual_objective_gradient_pairing_eq A hdual_grad
  -- Convexity of `hatφ` provides the lower support inequality needed for the final comparison.
  have htangent :
      hatφ u ≥ hatφ uHat + inner ℝ (∇ hatφ uHat) (u - uHat) :=
    hatphi_lower_tangent_at_base hhatφ_convex hu huHat hhatφ_grad
  linarith

end
