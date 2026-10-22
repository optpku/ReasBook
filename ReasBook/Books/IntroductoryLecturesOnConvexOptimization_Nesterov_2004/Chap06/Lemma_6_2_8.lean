/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Order.Filter.Extr
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

-- LeanSearch recall for the smooth lower-model step only surfaced the generic within-set
-- gradient API, so this item keeps the direct `HasGradientWithinAt` / `gradientWithin` route.

/-
Lemma 6.2.8 lies in Chapter 6's smoothed-primal-objective / excessive-gap domain.

Sampled owner declarations:
- `smoothedPrimalObjective` and `smoothedPrimalObjective_apply` in `Chap06/Definition_6_30`, the
  chapter owner for the value `f_{μ₂}`;
- `smoothedPrimalObjective_linearization_le_selected_dual_value` in `Chap06/Lemma_6_7`, the
  earlier chapter theorem already phrased on that owner surface;
- `smoothedPrimalObjective_at_x0_le_dual_value_at_V` in `Chap06/Lemma_6_13`, the downstream file
  that had been bridging this expanded theorem back to the owner declaration.

Best owner abstraction:
- source-facing: the one-point excessive-gap inequality at `barx = x₀(u₀)` and `baru = V(u₀)`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: the quadratic-model maximality of `V u₀` together with the identities and the
  penalty-corrected upper model for `-\hat φ` at `u₀`.

Primitive data:
- the primal-dual data `A`, `Q₂`, `hatf`, `hatφ`, `d₂`;
- the selections `x₀`, `V`, the base point `u₀`, and the Lipschitz constant `L₂φ`;
- the convexity, differentiability, Lipschitz, and penalty-corrected model hypotheses at `u₀`.

Derived API:
- the expanded formula
  `hatf (x₀ u₀) + sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ (L₂φ : ℝ) (x₀ u₀) '' Q₂)`;
- the owner `smoothedPrimalObjective A Q₂ hatf hatφ d₂ (L₂φ : ℝ) (x₀ u₀)`.

This file should state the theorem directly on the chapter owner surface instead of keeping a
parallel hand-expanded `hatf + sSup (...)` statement.
-/

-- Proof sketch: apply the quadratic lower model of `φ` coming from the Lipschitz gradient
-- hypothesis at `u₀`, use that `V u₀` maximizes this model on `Q₂`, then substitute the identities
-- expressing `φ u₀` and `∇ φ(u₀)` through `x₀ u₀`. The assumed penalty-corrected upper bound for
-- `-\hat φ` turns the resulting expression into the maximand defining
-- `f_{L₂(φ)}(x₀(u₀))`.
/-- Helper for Lemma 6.2.8: along a feasible segment, the corrected first-order remainder has
derivative given by the gradient increment paired with the segment direction. -/
private lemma segment_corrected_within_remainder_hasDerivWithinAt
    {Q₂ : Set E₂} {φ : E₂ → ℝ} (hQ₂_convex : Convex ℝ Q₂)
    (hφ_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        HasGradientWithinAt φ (gradientWithin φ Q₂ u) Q₂ u)
    {uBase u : E₂} (huBase : uBase ∈ Q₂) (hu : u ∈ Q₂)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun s : ℝ ↦
        φ (AffineMap.lineMap uBase u s) - φ uBase -
          s * inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase))
      (inner ℝ
        (gradientWithin φ Q₂ (AffineMap.lineMap uBase u t) -
          gradientWithin φ Q₂ uBase)
        (u - uBase))
      (Set.Icc (0 : ℝ) 1)
      t := by
  let seg : ℝ → E₂ := AffineMap.lineMap uBase u
  have hseg_maps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q₂ := hQ₂_convex.mapsTo_lineMap huBase hu
  have hseg_mem : seg t ∈ Q₂ := hseg_maps ht
  have hseg_deriv :
      HasDerivWithinAt
        (fun s : ℝ ↦ φ (seg s))
        (inner ℝ (gradientWithin φ Q₂ (seg t)) (u - uBase))
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- Differentiate `φ` along the feasible chord from `uBase` to `u`.
    simpa [seg] using
      (hφ_hasGradientWithinAt hseg_mem).hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq t
        AffineMap.hasDerivWithinAt_lineMap hseg_maps rfl
  have hlin :
      HasDerivWithinAt
        (fun s : ℝ ↦ s * inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase))
        (inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase))
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- The affine correction contributes the fixed base gradient pairing.
    simpa [one_mul] using
      ((hasDerivAt_id t).mul_const
        (inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase))).hasDerivWithinAt
  have hconst : HasDerivWithinAt (fun _ : ℝ ↦ φ uBase) 0 (Set.Icc (0 : ℝ) 1) t := by
    simpa using (hasDerivAt_const t (φ uBase)).hasDerivWithinAt
  have hmain :
      HasDerivWithinAt
        (fun s : ℝ ↦
          φ (seg s) - φ uBase -
            s * inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase))
        (inner ℝ (gradientWithin φ Q₂ (seg t)) (u - uBase) -
          inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase))
        (Set.Icc (0 : ℝ) 1)
        t := by
    -- Subtract the constant part first, then the linear correction.
    convert (hseg_deriv.sub hconst).sub hlin using 1
    ring
  -- Rewrite the derivative as the inner product with the gradient increment.
  simpa [inner_sub_left] using hmain

/-- Helper for Lemma 6.2.8: on the open segment, the corrected first-order remainder derivative is
bounded by the Lipschitz constant times the segment parameter and the squared chord length. -/
private lemma segment_corrected_within_remainder_deriv_abs_le
    {Q₂ : Set E₂} {φ : E₂ → ℝ} {L₂φ : NNReal} (hQ₂_convex : Convex ℝ Q₂)
    (hφ_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        HasGradientWithinAt φ (gradientWithin φ Q₂ u) Q₂ u)
    (hφ_gradient_lipschitz :
      LipschitzOnWith L₂φ (fun u ↦ gradientWithin φ Q₂ u) Q₂)
    {uBase u : E₂} (huBase : uBase ∈ Q₂) (hu : u ∈ Q₂)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |deriv
        (fun s : ℝ ↦
          φ (AffineMap.lineMap uBase u s) - φ uBase -
            s * inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase))
        t| ≤
      (L₂φ : ℝ) * t * ‖u - uBase‖ ^ (2 : ℕ) := by
  have hderivWithin :=
    segment_corrected_within_remainder_hasDerivWithinAt
      hQ₂_convex hφ_hasGradientWithinAt huBase hu (Set.mem_Icc_of_Ioo ht)
  have hderivAt := hderivWithin.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  rw [hderivAt.deriv]
  have hseg_mem : AffineMap.lineMap uBase u t ∈ Q₂ :=
    (hQ₂_convex.mapsTo_lineMap huBase hu) (Set.mem_Icc_of_Ioo ht)
  have hgrad_bound :
      ‖gradientWithin φ Q₂ (AffineMap.lineMap uBase u t) - gradientWithin φ Q₂ uBase‖ ≤
        (L₂φ : ℝ) * ‖AffineMap.lineMap uBase u t - uBase‖ := by
    simpa [dist_eq_norm] using hφ_gradient_lipschitz.norm_sub_le hseg_mem huBase
  have hseg_norm : ‖AffineMap.lineMap uBase u t - uBase‖ = t * ‖u - uBase‖ := by
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos ht.1, norm_sub_rev] using
      (dist_lineMap_left uBase u t)
  have hinner :
      |inner ℝ
          (gradientWithin φ Q₂ (AffineMap.lineMap uBase u t) -
            gradientWithin φ Q₂ uBase)
          (u - uBase)| ≤
        ‖gradientWithin φ Q₂ (AffineMap.lineMap uBase u t) -
            gradientWithin φ Q₂ uBase‖ * ‖u - uBase‖ := by
    simpa [real_inner_comm] using
      abs_real_inner_le_norm
        (gradientWithin φ Q₂ (AffineMap.lineMap uBase u t) - gradientWithin φ Q₂ uBase)
        (u - uBase)
  -- Combine Cauchy-Schwarz with the feasible-set Lipschitz gradient estimate.
  calc
    |inner ℝ
        (gradientWithin φ Q₂ (AffineMap.lineMap uBase u t) -
          gradientWithin φ Q₂ uBase)
        (u - uBase)| ≤
      ‖gradientWithin φ Q₂ (AffineMap.lineMap uBase u t) -
          gradientWithin φ Q₂ uBase‖ * ‖u - uBase‖ := hinner
    _ ≤ ((L₂φ : ℝ) * ‖AffineMap.lineMap uBase u t - uBase‖) * ‖u - uBase‖ := by
      gcongr
    _ = ((L₂φ : ℝ) * (t * ‖u - uBase‖)) * ‖u - uBase‖ := by
      rw [hseg_norm]
    _ = (L₂φ : ℝ) * t * ‖u - uBase‖ ^ (2 : ℕ) := by
      ring

/-- Helper for Lemma 6.2.8: the Lipschitz-gradient hypothesis on `Q₂` yields the lower quadratic
model for `φ` at any feasible base point. -/
private lemma smooth_within_lower_quadratic_model
    {Q₂ : Set E₂} {φ : E₂ → ℝ} {L₂φ : NNReal} (hQ₂_convex : Convex ℝ Q₂)
    (hφ_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        HasGradientWithinAt φ (gradientWithin φ Q₂ u) Q₂ u)
    (hφ_gradient_lipschitz :
      LipschitzOnWith L₂φ (fun u ↦ gradientWithin φ Q₂ u) Q₂)
    {uBase u : E₂} (huBase : uBase ∈ Q₂) (hu : u ∈ Q₂) :
    φ uBase +
        inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase) -
        ((L₂φ : ℝ) / 2) * ‖u - uBase‖ ^ (2 : ℕ) ≤
      φ u := by
  let remainder : ℝ → ℝ := fun s ↦
    φ (AffineMap.lineMap uBase u s) - φ uBase -
      s * inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase)
  have hcont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    -- Every point of the feasible segment has a within-set derivative for the corrected remainder.
    exact
      (segment_corrected_within_remainder_hasDerivWithinAt
        hQ₂_convex hφ_hasGradientWithinAt huBase hu ht).continuousWithinAt
  have hdiff : DifferentiableOn ℝ remainder (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    -- On the open interval, the within-derivative upgrades to an ordinary derivative.
    exact
      ((segment_corrected_within_remainder_hasDerivWithinAt
          hQ₂_convex hφ_hasGradientWithinAt huBase hu
          (Set.mem_Icc_of_Ioo ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
        |>.differentiableWithinAt
  have hbound :=
    norm_sub_le_integral_of_norm_deriv_le_of_le
      (by norm_num)
      hcont
      hdiff
      (Filter.Eventually.of_forall fun t ht_mem ↦
        segment_corrected_within_remainder_deriv_abs_le
          hQ₂_convex hφ_hasGradientWithinAt hφ_gradient_lipschitz huBase hu ht_mem)
      (by
        simpa [mul_assoc] using
          (show IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 from
            intervalIntegrable_id).const_mul ((L₂φ : ℝ) * ‖u - uBase‖ ^ (2 : ℕ)))
  have hR0 : remainder 0 = 0 := by
    simp [remainder]
  have hR1 :
      remainder 1 =
        φ u - φ uBase - inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase) := by
    simp [remainder]
  rw [hR1, hR0, sub_zero, Real.norm_eq_abs] at hbound
  have hrem :=
    abs_le.mp <|
      calc
        |φ u - φ uBase - inner ℝ (gradientWithin φ Q₂ uBase) (u - uBase)| ≤
            ∫ t in (0 : ℝ)..1, (L₂φ : ℝ) * t * ‖u - uBase‖ ^ (2 : ℕ) := hbound
        _ = ((L₂φ : ℝ) / 2) * ‖u - uBase‖ ^ (2 : ℕ) := by
            calc
              ∫ t in (0 : ℝ)..1, (L₂φ : ℝ) * t * ‖u - uBase‖ ^ (2 : ℕ) =
                  ∫ t in (0 : ℝ)..1, ((L₂φ : ℝ) * ‖u - uBase‖ ^ (2 : ℕ)) * t := by
                    congr with t
                    ring
              _ = ((L₂φ : ℝ) * ‖u - uBase‖ ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
                    rw [intervalIntegral.integral_const_mul]
              _ = ((L₂φ : ℝ) / 2) * ‖u - uBase‖ ^ (2 : ℕ) := by
                    rw [integral_id]
                    norm_num
                    ring
  linarith [hrem.1]

/-- Helper for Lemma 6.2.8: the penalized maximand at `x₀(u₀)` is bounded above by the quadratic
model of `φ` at `u₀`, shifted by `-hatf (x₀ u₀)`. -/
private lemma smoothed_primal_maximand_le_base_quadratic_model
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₂ : Set E₂}
    {φ hatφ : E₂ → ℝ} {hatf : E₁ → ℝ} {d₂ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {u₀ : E₂} {L₂φ : NNReal}
    (hφ_eq :
      φ u₀ = -hatφ u₀ + A (x₀ u₀) u₀ + hatf (x₀ u₀))
    (hgradφ_eq :
      gradientWithin φ Q₂ u₀ =
        (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀)) - gradientWithin hatφ Q₂ u₀)
    (hhatφ_model :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        -hatφ u ≤
          -hatφ u₀ - inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀) +
            (L₂φ : ℝ) * d₂ u -
            ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ))
    {u : E₂} (hu : u ∈ Q₂) :
    smoothedPrimalObjectiveMaximand A hatφ d₂ (L₂φ : ℝ) (x₀ u₀) u ≤
      φ u₀ + inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
        ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ) - hatf (x₀ u₀) := by
  have hA_split :
      A (x₀ u₀) u = A (x₀ u₀) u₀ + A (x₀ u₀) (u - u₀) := by
    calc
      A (x₀ u₀) u = A (x₀ u₀) (u₀ + (u - u₀)) := by simp
      _ = A (x₀ u₀) u₀ + A (x₀ u₀) (u - u₀) := by rw [map_add]
  have hA_inner :
      A (x₀ u₀) (u - u₀) =
        inner ℝ ((InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀))) (u - u₀) := by
    simpa using
      (show
        inner ℝ ((InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀))) (u - u₀) =
          A (x₀ u₀) (u - u₀) from
        InnerProductSpace.toDual_symm_apply).symm
  have hgrad_rewrite :
      inner ℝ ((InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀))) (u - u₀) -
          inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀) =
        inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) := by
    calc
      inner ℝ ((InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀))) (u - u₀) -
          inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀) =
        inner ℝ
          (((InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀))) -
            gradientWithin hatφ Q₂ u₀)
          (u - u₀) := by
            rw [inner_sub_left]
      _ = inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) := by
            rw [← hgradφ_eq]
  have hstep :
      smoothedPrimalObjectiveMaximand A hatφ d₂ (L₂φ : ℝ) (x₀ u₀) u ≤
        -hatφ u₀ + A (x₀ u₀) u₀ +
          (A (x₀ u₀) (u - u₀) -
            inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀)) -
          ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ) := by
    -- Expand the owner maximand and insert the penalty-corrected model for `-hatφ`.
    rw [smoothedPrimalObjectiveMaximand]
    linarith [hhatφ_model hu, hA_split]
  calc
    smoothedPrimalObjectiveMaximand A hatφ d₂ (L₂φ : ℝ) (x₀ u₀) u ≤
        -hatφ u₀ + A (x₀ u₀) u₀ +
          (A (x₀ u₀) (u - u₀) -
            inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀)) -
          ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ) := hstep
    _ = -hatφ u₀ + A (x₀ u₀) u₀ +
          (inner ℝ ((InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀))) (u - u₀) -
            inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀)) -
          ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ) := by
          rw [hA_inner]
    _ = -hatφ u₀ + A (x₀ u₀) u₀ +
          inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
          ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ) := by
          rw [hgrad_rewrite]
    _ = φ u₀ + inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
          ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ) - hatf (x₀ u₀) := by
          linarith [hφ_eq]

/-- Helper for Lemma 6.2.8: the smoothed primal objective at `x₀(u₀)` is bounded by the quadratic
model of `φ` evaluated at the selected maximizer `V(u₀)`. -/
private lemma smoothed_primal_objective_le_quadratic_model_at_V
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₂ : Set E₂}
    {φ hatφ : E₂ → ℝ} {hatf : E₁ → ℝ} {d₂ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {V : E₂ → E₂} {u₀ : E₂} {L₂φ : NNReal}
    (hu₀ : u₀ ∈ Q₂)
    (hV_max :
      IsMaxOn
        (fun u ↦
          φ u₀ +
            inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
              ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ))
        Q₂
        (V u₀))
    (hφ_eq :
      φ u₀ = -hatφ u₀ + A (x₀ u₀) u₀ + hatf (x₀ u₀))
    (hgradφ_eq :
      gradientWithin φ Q₂ u₀ =
        (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀)) - gradientWithin hatφ Q₂ u₀)
    (hhatφ_model :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        -hatφ u ≤
          -hatφ u₀ - inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀) +
            (L₂φ : ℝ) * d₂ u -
            ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ)) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ (L₂φ : ℝ) (x₀ u₀) ≤
      φ u₀ +
        inner ℝ (gradientWithin φ Q₂ u₀) (V u₀ - u₀) -
        ((L₂φ : ℝ) / 2) * ‖V u₀ - u₀‖ ^ (2 : ℕ) := by
  let model : E₂ → ℝ := fun u ↦
    φ u₀ +
      inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
      ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ)
  have hsSup_le :
      sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ (L₂φ : ℝ) (x₀ u₀) '' Q₂) ≤
        model (V u₀) - hatf (x₀ u₀) := by
    refine csSup_le ?_ ?_
    · exact ⟨_, Set.mem_image_of_mem _ hu₀⟩
    · intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      have hmaximand :=
        smoothed_primal_maximand_le_base_quadratic_model
          A hφ_eq hgradφ_eq hhatφ_model hu
      have hmodel_le : model u ≤ model (V u₀) := (isMaxOn_iff.mp hV_max) u hu
      exact hmaximand.trans (sub_le_sub_right hmodel_le (hatf (x₀ u₀)))
  -- Pass the pointwise image bound through the owner supremum formula.
  rw [smoothedPrimalObjective_apply]
  dsimp [model] at hsSup_le ⊢
  linarith

/-- Helper for Lemma 6.2.8: the quadratic model at the selected point `V(u₀)` lies below the true
dual value `φ (V u₀)`. -/
private lemma quadratic_model_at_V_le_dual_value
    {Q₂ : Set E₂} {φ : E₂ → ℝ} {V : E₂ → E₂} {u₀ : E₂} {L₂φ : NNReal}
    (hQ₂_convex : Convex ℝ Q₂)
    (hu₀ : u₀ ∈ Q₂)
    (hφ_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        HasGradientWithinAt φ (gradientWithin φ Q₂ u) Q₂ u)
    (hφ_gradient_lipschitz :
      LipschitzOnWith L₂φ (fun u ↦ gradientWithin φ Q₂ u) Q₂)
    (hVu₀ : V u₀ ∈ Q₂) :
    φ u₀ +
        inner ℝ (gradientWithin φ Q₂ u₀) (V u₀ - u₀) -
        ((L₂φ : ℝ) / 2) * ‖V u₀ - u₀‖ ^ (2 : ℕ) ≤
      φ (V u₀) := by
  simpa using
    smooth_within_lower_quadratic_model hQ₂_convex hφ_hasGradientWithinAt
      hφ_gradient_lipschitz hu₀ hVu₀

/-- Lemma 6.2.8: if `∇ φ` is `L₂(φ)`-Lipschitz on the convex set `Q₂`, if `V(u₀)` maximizes the
quadratic model of `φ` at `u₀`, and if the identities and penalty-corrected upper model from the
preceding setup hold at `u₀`, then the excessive-gap inequality `(6.2.31)` is valid for
`μ₂ = L₂(φ)`, `\bar x = x₀(u₀)`, and `\bar u = V(u₀)`, namely
`f_{L₂(φ)}(x₀(u₀)) ≤ φ(V(u₀))`. -/
theorem smoothed_primal_objective_at_x0_le_dual_value_at_V
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₂ : Set E₂}
    {φ hatφ : E₂ → ℝ} {hatf : E₁ → ℝ} {d₂ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {V : E₂ → E₂} {u₀ : E₂} {L₂φ : NNReal}
    (hQ₂_convex : Convex ℝ Q₂)
    (hu₀ : u₀ ∈ Q₂)
    (hφ_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        HasGradientWithinAt φ (gradientWithin φ Q₂ u) Q₂ u)
    (hφ_gradient_lipschitz :
      LipschitzOnWith L₂φ (fun u ↦ gradientWithin φ Q₂ u) Q₂)
    (hV_max :
      IsMaxOn
        (fun u ↦
          φ u₀ +
            inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
              ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ))
        Q₂
        (V u₀))
    (hVu₀ : V u₀ ∈ Q₂)
    (hφ_eq :
      φ u₀ = -hatφ u₀ + A (x₀ u₀) u₀ + hatf (x₀ u₀))
    (hgradφ_eq :
      gradientWithin φ Q₂ u₀ =
        (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀)) - gradientWithin hatφ Q₂ u₀)
    (hhatφ_model :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        -hatφ u ≤
          -hatφ u₀ - inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀) +
            (L₂φ : ℝ) * d₂ u -
            ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ)) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ (L₂φ : ℝ) (x₀ u₀) ≤
      φ (V u₀) := by
  -- Route correction: follow the source proof through the quadratic model of `φ`, not through a
  -- convex-support argument for `φ`.
  have hobjective_le_model :
      smoothedPrimalObjective A Q₂ hatf hatφ d₂ (L₂φ : ℝ) (x₀ u₀) ≤
        φ u₀ +
          inner ℝ (gradientWithin φ Q₂ u₀) (V u₀ - u₀) -
          ((L₂φ : ℝ) / 2) * ‖V u₀ - u₀‖ ^ (2 : ℕ) :=
    smoothed_primal_objective_le_quadratic_model_at_V
      A hu₀ hV_max hφ_eq hgradφ_eq hhatφ_model
  have hmodel_le_dual :
      φ u₀ +
          inner ℝ (gradientWithin φ Q₂ u₀) (V u₀ - u₀) -
          ((L₂φ : ℝ) / 2) * ‖V u₀ - u₀‖ ^ (2 : ℕ) ≤
        φ (V u₀) :=
    quadratic_model_at_V_le_dual_value hQ₂_convex hu₀
      hφ_hasGradientWithinAt hφ_gradient_lipschitz hVu₀
  -- Chain the owner-level supremum estimate with the smooth lower-model inequality at `V u₀`.
  exact hobjective_le_model.trans hmodel_le_dual
