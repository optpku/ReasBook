/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

noncomputable section

universe u v

/- Lemma 6.7 lies in the chapter's smoothed primal objective / tangent-plane domain.

Sampled owner declarations:
- `smoothedPrimalObjectiveArgmax`, `smoothedPrimalObjectiveMaximand`, and
  `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the chapter owners for the selected dual
  maximizer, the regularized dual maximand, and its supremum objective;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Chap06/Definition_6_30`, the thin bridge from the
  argmax owner to the underlying feasible-maximizer conditions;
- `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Chap02/Definition_2_2`, the
  project owner for the first-order supporting inequality on a convex feasible set;
- mathlib `HasGradientWithinAt` / `gradientWithin`, the canonical within-set gradient layer.

Best owner abstraction:
- source-facing: Lemma 6.7's one-point linearization bound at a selected dual maximizer;
- core/canonical: `smoothedPrimalObjectiveArgmax`, `smoothedPrimalObjective`, `ConvexOn`, and
  `HasGradientWithinAt`;
- bridge/view: `mem_smoothedPrimalObjectiveArgmax_iff`, unpacking the argmax owner to feasibility
  and `IsMaxOn`.

Primitive data:
- `A`, `Q₁`, `Q₂`, `hatf`, `hatφ`, `d₂`, `μ₂`, `x`, `xhat`, and `u`;
- convexity of `hatf` on `Q₁`, which already packages convexity of `Q₁`;
- the source-facing argmax membership hypothesis at `xhat`;
- the within-set gradient witness for `hatf` at `xhat`;
- the sign hypotheses `0 ≤ μ₂` and `0 ≤ d₂ u`.

Derived API:
- the canonical smoothed objective value at `xhat`;
- the tangent-plane inequality for `hatf` at `xhat`;
- the bridge from argmax membership to the underlying `IsMaxOn` witness;
- the resulting affine upper bound against the selected dual value.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: the owner declarations from `Definition_6_30`;
- bridge/view: the pointwise maximizer witness `u`.

The previous version rebuilt local owners `smoothedObjectiveIntegrand` and
`primalDualSmoothedObjective`. Those were exact duplicates of the chapter owners in
`Definition_6_30`, so this file now states the source-facing lemma directly against the canonical
API.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Helper for Lemma 6.7: an element of the canonical smoothed primal argmax set realizes the
greatest value of the dual maximand image over `Q₂`. -/
private theorem isGreatest_smoothedPrimalObjectiveMaximand_image_of_mem_argmax
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₂ : Set E₂} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {xhat : E₁} {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat) :
    IsGreatest
      (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ xhat '' Q₂)
      (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ xhat u) := by
  -- Unpack the owner-level argmax membership into feasibility and pointwise maximality.
  rcases (mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ₂ xhat u).mp hu with
    ⟨hu_mem, hu_max⟩
  -- Promote the feasible maximizer to an `IsGreatest` witness for the image set.
  refine ⟨⟨u, hu_mem, rfl⟩, ?_⟩
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  exact (isMaxOn_iff.mp hu_max) v hv

/-- Helper for Lemma 6.7: evaluating the smoothed primal objective at a selected maximizer
replaces the supremum by the corresponding dual maximand value. -/
private theorem smoothedPrimalObjective_eq_hatf_add_selected_maximand_of_mem_argmax
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₂ : Set E₂} {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {xhat : E₁} {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat =
      hatf xhat + (A xhat u - hatφ u - μ₂ * d₂ u) := by
  -- Rewrite the supremum term with the exact attained value supplied by the chosen maximizer.
  rw [smoothedPrimalObjective_apply]
  rw [(isGreatest_smoothedPrimalObjectiveMaximand_image_of_mem_argmax A hu).csSup_eq]
  simp [smoothedPrimalObjectiveMaximand]

/-- Helper for Lemma 6.7: the affine dual term along the primal displacement splits by linearity
of `A`. -/
private theorem selected_dual_affine_term_sub
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (x xhat : E₁) (u : E₂) :
    A (x - xhat) u = A x u - A xhat u := by
  -- Rewrite the primal displacement through the linear map, then evaluate the resulting dual
  -- functional at `u`.
  rw [A.map_sub]
  rfl

/-- Helper for Lemma 6.7: subtracting a nonnegative penalty can only decrease the selected dual
value. -/
private theorem selected_dual_value_sub_penalty_le
    {dualTerm penalty μ₂ : ℝ}
    (hμ₂ : 0 ≤ μ₂) (hpenalty : 0 ≤ penalty) :
    dualTerm - μ₂ * penalty ≤ dualTerm := by
  -- The smoothing penalty is nonnegative, so the penalized value is bounded above by the
  -- unpenalized one.
  have hmul : 0 ≤ μ₂ * penalty := mul_nonneg hμ₂ hpenalty
  linarith

-- Proof sketch: expand `smoothedPrimalObjective` at `xhat`, unpack the argmax membership `hu`
-- with `mem_smoothedPrimalObjectiveArgmax_iff` to bound the supremum term by the selected dual
-- value, apply the supporting-nesterovHyperplane inequality for the
-- convex function `hatf` at `xhat`, rewrite the affine pairing term as `A x u`, and drop the
-- nonpositive term `-μ₂ * d₂ u` using `μ₂ ≥ 0` and `d₂ u ≥ 0`.
variable [CompleteSpace E₁]

/-- Lemma 6.7: if `u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat`, then the affine
linearization of the smoothed primal objective at `xhat ∈ Q₁`, with the smooth contribution
written as `∇ \hat f(xhat)`, is bounded above by `\hat f(x) + ⟪A x, u⟫ - \hat φ(u)` for every
`x ∈ Q₁`. -/
theorem smoothedPrimalObjective_linearization_le_selected_dual_value
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂} {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    (hhatf_conv : ConvexOn ℝ Q₁ hatf) (hμ₂ : 0 ≤ μ₂)
    {x xhat : E₁} (hx : x ∈ Q₁) (hxhat : xhat ∈ Q₁) {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat)
    (hhatf_grad : HasGradientWithinAt hatf (gradientWithin hatf Q₁ xhat) Q₁ xhat)
    (hd₂_nonneg : 0 ≤ d₂ u) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
      inner ℝ (gradientWithin hatf Q₁ xhat) (x - xhat) +
      A (x - xhat) u ≤
      hatf x + A x u - hatφ u := by
  -- Rewrite the smoothed objective at `xhat` by evaluating the supremum at the chosen maximizer.
  have hobjective :
      smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat =
        hatf xhat + (A xhat u - hatφ u - μ₂ * d₂ u) :=
    smoothedPrimalObjective_eq_hatf_add_selected_maximand_of_mem_argmax A hu
  -- Convexity of `hatf` yields the supporting tangent-plane lower bound at the base point `xhat`.
  have hsupport :
      hatf xhat + inner ℝ (gradientWithin hatf Q₁ xhat) (x - xhat) ≤ hatf x := by
    have hsupport' :=
      hhatf_conv.lower_tangent_plane_of_hasGradientWithinAt xhat hxhat
        (gradientWithin hatf Q₁ xhat) hhatf_grad x hx
    linarith
  -- Linearity of `A` combines the exact objective value at `xhat` with the affine displacement
  -- term into the selected dual value at `x`.
  have hrepack :
      smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
          inner ℝ (gradientWithin hatf Q₁ xhat) (x - xhat) +
          A (x - xhat) u =
        (hatf xhat + inner ℝ (gradientWithin hatf Q₁ xhat) (x - xhat)) +
          (A x u - hatφ u - μ₂ * d₂ u) := by
    rw [hobjective, selected_dual_affine_term_sub A x xhat u]
    ring
  -- The prox penalty is nonnegative, so dropping it only increases the right-hand side.
  have hpenalty :
      A x u - hatφ u - μ₂ * d₂ u ≤ A x u - hatφ u :=
    selected_dual_value_sub_penalty_le
      (dualTerm := A x u - hatφ u) (penalty := d₂ u) hμ₂ hd₂_nonneg
  calc
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
        inner ℝ (gradientWithin hatf Q₁ xhat) (x - xhat) +
        A (x - xhat) u =
      (hatf xhat + inner ℝ (gradientWithin hatf Q₁ xhat) (x - xhat)) +
        (A x u - hatφ u - μ₂ * d₂ u) := hrepack
    _ ≤ hatf x + (A x u - hatφ u) := add_le_add hsupport hpenalty
    _ = hatf x + A x u - hatφ u := by ring

end
