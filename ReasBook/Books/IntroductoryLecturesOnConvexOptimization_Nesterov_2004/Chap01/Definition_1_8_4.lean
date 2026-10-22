/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_8_3

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Topology Gradient MatrixPosDef

noncomputable section

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMat" => {A : Mat // Matrix.PosDef A}

/- Definition 1.8.4 is source-facing in weighted second-order differential calculus.

Source/core/bridge triage:
- source-facing: the textbook quadratic expansion clause
  `HasWeightedGradientSecondOrderExpansionAt A f g H x`
- core/canonical: the derivative-level pair
  `HasGradientAt f g x ∧ HasFDerivAt (∇ f) ((1 / 2 : ℝ) • (H + H.adjoint)) x`
  on `WeightedSpace A`
- bridge/view: the self-adjoint-average bridge from the textbook quadratic expansion clause to
  the canonical weighted first- and second-order owners

Primary domain:
- second-order differential calculus on finite-dimensional weighted inner-product spaces

Relevant owner-style declarations sampled before refining:
- `Matrix.PosDef.WeightedSpace`
- `HasGradientAt`
- `HasFDerivAt`
- `ContinuousLinearMap.adjoint`
- `IsSelfAdjoint.add_star_self`

Best owner abstraction:
- the weighted-space owner `WeightedSpace A` induced by `A : PosMat`
- the canonical weighted first- and second-order owner pair attached to the weighted self-adjoint
  average of the quadratic witness
  `HasGradientAt f g x ∧ HasFDerivAt (∇ f) ((1 / 2 : ℝ) • (H + H.adjoint)) x`

Primitive data:
- `A : PosMat`
- `f : Matrix.PosDef.WeightedSpace A → ℝ`
- `x : Matrix.PosDef.WeightedSpace A`
- `g : Matrix.PosDef.WeightedSpace A`
- `H : Matrix.PosDef.WeightedSpace A →L[ℝ] Matrix.PosDef.WeightedSpace A`

Derived API:
- the source-facing weighted quadratic expansion clause
  `HasWeightedGradientSecondOrderExpansionAt A f g H x`
- the adjoint-average invariance of that clause
  `HasWeightedGradientSecondOrderExpansionAt.iff_adjointAverage`
- the recovery of the weighted first-order owner from the quadratic expansion
  `HasWeightedGradientSecondOrderExpansionAt.hasGradientAt_of_weighted_second_order`
- the forward bridge from a genuine weighted gradient together with a derivative of the totalized
  gradient to the source-facing quadratic expansion
  `HasWeightedGradientSecondOrderExpansionAt.weighted_second_order_of_hasGradientAt_and_hasFDerivAt_gradient`
- the directional line-restriction consequence recording the quadratic coefficient
  `HasWeightedGradientSecondOrderExpansionAt.line_restriction_has_weighted_second_order_expansion`

The quadratic term `⟪K h, h⟫_[A]` only depends on the weighted self-adjoint part of `K`. The file
therefore keeps the textbook expansion clause as the main source-facing owner and records the
first-order recovery and honest forward/directional companions, while avoiding a false reverse
API for the totalized gradient. -/

local notation "WeightedSpace" => Matrix.PosDef.WeightedSpace

section

variable {A : PosMat}
variable {f : WeightedSpace A → ℝ} {x g : WeightedSpace A}
variable {H : WeightedSpace A →L[ℝ] WeightedSpace A}

/-- The textbook weighted second-order expansion clause with linear witness `g` and quadratic
operator witness `H` at `x`. -/
def HasWeightedGradientSecondOrderExpansionAt
    (A : PosMat) (f : WeightedSpace A → ℝ) (g : WeightedSpace A)
    (H : WeightedSpace A →L[ℝ] WeightedSpace A) (x : WeightedSpace A) : Prop :=
  (fun h ↦
      f (x + h) -
        (f x
          + (⟪g, h⟫_[A] : ℝ)
          + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))) =o[
            𝓝 (0 : WeightedSpace A)]
    fun h ↦ (‖h‖[A] : ℝ) ^ (2 : ℕ)

/- Definition 1.8.4: on the weighted Hilbert space determined by `A`, the source-facing notion is
the weighted quadratic expansion clause `HasWeightedGradientSecondOrderExpansionAt A f g H x`. -/
#check HasWeightedGradientSecondOrderExpansionAt A f g H x

namespace HasWeightedGradientSecondOrderExpansionAt

/-- Helper for Definition 1.8.4: package the totalized weighted gradient as an ordinary weighted
vector field so continuity and derivative hypotheses can be specialized without reopening the
gradient notation. -/
abbrev total_gradient_field (f : WeightedSpace A → ℝ) : WeightedSpace A → WeightedSpace A :=
  fun y : WeightedSpace A ↦ @gradient ℝ (WeightedSpace A) _ _ _ inferInstance f y

/-- Helper for Definition 1.8.4: continuity of the raw weighted gradient on a neighborhood ball
immediately transfers to the packaged total gradient field. -/
lemma total_gradient_field_continuousOn
    {r : ℝ}
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r)) :
    ContinuousOn (total_gradient_field (A := A) f) (Metric.ball x r) := by
  -- Freeze the gradient notation into the packaged vector field before specializing generic
  -- continuity lemmas.
  change
    ContinuousOn
      (fun y : WeightedSpace A ↦ @gradient ℝ (WeightedSpace A) _ _ _ inferInstance f y)
      (Metric.ball x r)
  simpa using hcont_nhds

/-- Helper for Definition 1.8.4: a Fréchet derivative hypothesis for the raw weighted gradient is
the same derivative hypothesis for the packaged total gradient field. -/
lemma total_gradient_field_hasFDerivAt
    (hgrad : HasFDerivAt (∇ f) H x) :
    HasFDerivAt (total_gradient_field (A := A) f) H x := by
  -- The packaged field is definitionally the raw gradient map.
  change HasFDerivAt
    (fun y : WeightedSpace A ↦ @gradient ℝ (WeightedSpace A) _ _ _ inferInstance f y) H x
  simpa using hgrad

/-- Helper for Definition 1.8.4: the weighted quadratic form only sees the weighted self-adjoint
average of the operator witness. -/
lemma quadratic_form_adjointAverage_eq
    (h : WeightedSpace A) :
    (⟪(((1 / 2 : ℝ) • (H + H.adjoint)) h), h⟫_[A] : ℝ) = (⟪H h, h⟫_[A] : ℝ) := by
  -- Expand the adjoint average and identify the adjoint contribution with the original quadratic
  -- term by the weighted adjoint identity.
  have hadj : (⟪H.adjoint h, h⟫_[A] : ℝ) = (⟪H h, h⟫_[A] : ℝ) := by
    simpa [real_inner_comm] using ContinuousLinearMap.adjoint_inner_right (A := H) h h
  calc
    (⟪(((1 / 2 : ℝ) • (H + H.adjoint)) h), h⟫_[A] : ℝ)
        = (1 / 2 : ℝ) * ((⟪(H + H.adjoint) h, h⟫_[A] : ℝ)) := by
          simp
    _ = (1 / 2 : ℝ) * ((⟪H h, h⟫_[A] : ℝ) + (⟪H.adjoint h, h⟫_[A] : ℝ)) := by
          simp [inner_add_left]
    _ = (1 / 2 : ℝ) * ((⟪H h, h⟫_[A] : ℝ) + (⟪H h, h⟫_[A] : ℝ)) := by
          rw [hadj]
    _ = (⟪H h, h⟫_[A] : ℝ) := by
          ring

/-- Helper for Definition 1.8.4: the weighted quadratic term is uniformly bounded by a constant
multiple of `‖h‖[A]^2` near the basepoint. -/
lemma quadraticTermQuadraticBound :
    (fun h : WeightedSpace A ↦ (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) =O[𝓝 (0 : WeightedSpace A)]
      fun h ↦ (‖h‖[A] : ℝ) ^ (2 : ℕ) := by
  -- Control the quadratic term by Cauchy-Schwarz and the operator norm of `H`.
  refine Asymptotics.IsBigO.of_bound ((1 / 2 : ℝ) * ‖H‖) ?_
  filter_upwards [Filter.Eventually.of_forall fun h : WeightedSpace A ↦ ?_] with h
  calc
    ‖(1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)‖ = (1 / 2 : ℝ) * ‖(⟪H h, h⟫_[A] : ℝ)‖ := by
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (1 / 2 : ℝ) * (‖H h‖ * ‖h‖) := by
      gcongr
      simpa using (norm_inner_le_norm (𝕜 := ℝ) (H h) h)
    _ ≤ (1 / 2 : ℝ) * (‖H‖ * ‖h‖ * ‖h‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm H h
    _ = ((1 / 2 : ℝ) * ‖H‖) * (‖h‖ ^ (2 : ℕ)) := by
      ring
    _ = ((1 / 2 : ℝ) * ‖H‖) * ‖(‖h‖[A] : ℝ) ^ (2 : ℕ)‖ := by
      have hpow : 0 ≤ (‖h‖[A] : ℝ) ^ (2 : ℕ) := by
        positivity
      rw [Real.norm_of_nonneg hpow]

/-- Helper for Definition 1.8.4: the weighted quadratic term is little-`o` of the displacement,
so it does not affect the first-order gradient witness. -/
lemma quadraticTermSublinear :
    (fun h : WeightedSpace A ↦ (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) =o[𝓝 (0 : WeightedSpace A)]
      fun h ↦ h := by
  -- Factor the quadratic term through the standard `‖h‖^2 = o(‖h‖)` estimate.
  exact quadraticTermQuadraticBound.trans_isLittleO (by
    simpa using
      (Asymptotics.isLittleO_norm_pow_id (E' := WeightedSpace A) (n := 2) (by norm_num)))

/-- Helper for Definition 1.8.4: a weighted second-order expansion already determines the
weighted gradient witness. -/
lemma hasGradientAt_of_weighted_second_order
    (hExp : HasWeightedGradientSecondOrderExpansionAt A f g H x) :
    HasGradientAt f g x := by
  -- Discard the quadratic correction, which is negligible compared with the linear term.
  have hMain :
      (fun h : WeightedSpace A ↦
        f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))) =o[
          𝓝 (0 : WeightedSpace A)] fun h ↦ h :=
    hExp.trans_isLittleO (by
      simpa using
        (Asymptotics.isLittleO_norm_pow_id (E' := WeightedSpace A) (n := 2) (by norm_num)))
  have hSum := hMain.add (quadraticTermSublinear (A := A) (H := H))
  exact
    (hasGradientAt_iff_isLittleO_nhds_zero
      (𝕜 := ℝ) (F := WeightedSpace A) (f := f) (f' := g) (x := x)).2 <|
      by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSum

/-- Helper for Definition 1.8.4: translating the derivative of the weighted totalized gradient to
the basepoint gives the vector little-`o` remainder in displacement coordinates. -/
lemma gradientDerivativeRemainderAtZero
    (hg : HasGradientAt f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    (fun k : WeightedSpace A ↦ ∇ f (x + k) - g - H k) =o[𝓝 (0 : WeightedSpace A)]
      fun k : WeightedSpace A ↦ k := by
  -- Rewrite the Fréchet derivative remainder into the translated `k ↦ x + k` model.
  have hgrad_field :
      HasFDerivAt (total_gradient_field (A := A) f) H x :=
    HasWeightedGradientSecondOrderExpansionAt.total_gradient_field_hasFDerivAt
      (A := A) (f := f) (x := x) (H := H) hgrad
  have hsmall :
      (fun k : WeightedSpace A ↦ total_gradient_field (A := A) f (x + k) - g - H k) =o[
        𝓝 (0 : WeightedSpace A)] fun k : WeightedSpace A ↦ k := by
    simpa [hg.gradient, total_gradient_field, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using
        (hasFDerivAt_iff_isLittleO_nhds_zero
          (f := total_gradient_field (A := A) f) (f' := H) (x := x)).mp hgrad_field
  simpa [total_gradient_field] using hsmall

/-- Helper for Definition 1.8.4: every point on a short weighted segment from `x` stays inside the
radius-`r` ball where the local gradient-field hypothesis is available. -/
lemma segment_point_mem_ball
    {r : ℝ} (hr : 0 < r) {h : WeightedSpace A} (hh : ‖h‖ < r) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • h ∈ Metric.ball x r := by
  -- The segment parameter stays in `[0,1]`, so the displacement norm contracts by at most `t`.
  have hnorm_le : ‖t • h‖ ≤ ‖h‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg h, ht.1, ht.2]
  have hnorm : ‖t • h‖ < r := lt_of_le_of_lt hnorm_le hh
  have _ : 0 < r := hr
  simpa [Metric.mem_ball, dist_eq_norm] using hnorm

/-- Helper for Definition 1.8.4: along a short weighted segment, the corrected quadratic remainder
has derivative equal to the gradient linearization error paired with the segment direction. -/
lemma segment_quadratic_remainder_hasDerivAt
    {r : ℝ} (hr : 0 < r)
    (hgrad_nhds : ∀ y ∈ Metric.ball x r, HasGradientAt f (∇ f y) y)
    {h : WeightedSpace A} (hh : ‖h‖ < r) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun u : ℝ ↦
        f (x + u • h) - f x - u * (⟪g, h⟫_[A] : ℝ) -
          (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ))
      (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) t := by
  -- Differentiate the affine segment first, then compose it with the local gradient identity.
  have hy : HasGradientAt f (∇ f (x + t • h)) (x + t • h) :=
    hgrad_nhds (x + t • h) (segment_point_mem_ball (A := A) (x := x) hr hh ht)
  have hline : HasDerivAt (fun u : ℝ ↦ x + u • h) h t := by
    simpa [one_smul] using (((hasDerivAt_id t).smul_const h).const_add x)
  have hseg :
      HasDerivAt (fun u : ℝ ↦ f (x + u • h)) ((fderiv ℝ f (x + t • h)) h) t := by
    simpa [Function.comp] using (hy.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  -- Differentiate the affine and quadratic model terms separately.
  have hlin : HasDerivAt (fun u : ℝ ↦ u * (⟪g, h⟫_[A] : ℝ)) (⟪g, h⟫_[A] : ℝ) t := by
    simpa [one_mul] using (hasDerivAt_id t).mul_const (⟪g, h⟫_[A] : ℝ)
  have hsq : HasDerivAt (fun u : ℝ ↦ u ^ (2 : ℕ)) (2 * t) t := by
    simpa [pow_two, two_mul] using (hasDerivAt_id t).mul (hasDerivAt_id t)
  have hquad :
      HasDerivAt
        (fun u : ℝ ↦ (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ))
        (t * (⟪H h, h⟫_[A] : ℝ)) t := by
    have hconst :
        HasDerivAt
          (fun u : ℝ ↦ ((1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) * (u ^ (2 : ℕ)))
          (((1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) * (2 * t)) t :=
      hsq.const_mul ((1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hconst
  have hmain :
      HasDerivAt
        (fun u : ℝ ↦
          f (x + u • h) - f x - u * (⟪g, h⟫_[A] : ℝ) -
            (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ))
        (((fderiv ℝ f (x + t • h)) h) - (⟪g, h⟫_[A] : ℝ) - t * (⟪H h, h⟫_[A] : ℝ)) t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hseg.sub ((hasDerivAt_const t (f x)).add hlin).sub hquad
  -- Rewrite the Fréchet derivative and the quadratic scalar term into weighted-inner form.
  simpa [hy.fderiv_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    inner_sub_left, ContinuousLinearMap.map_smul, inner_smul_left, mul_assoc, mul_left_comm,
    mul_comm] using hmain

/-- Helper for Definition 1.8.4: pairing a continuous weighted vector field with a fixed weighted
direction preserves continuity on the same set. -/
lemma weighted_segment_pair_continuousOn
    {s : Set ℝ} {v : ℝ → WeightedSpace A} (hv : ContinuousOn v s) (h : WeightedSpace A) :
    ContinuousOn (fun t : ℝ ↦ (⟪v t, h⟫_[A] : ℝ)) s := by
  -- Route the weighted pairing through the ambient inner-product continuity API.
  intro t ht
  have hconst : ContinuousAt (fun _ : ℝ ↦ h) t := continuousAt_const
  simpa [Matrix.PosDef.weightedInner] using (hv t ht).inner hconst

/-- Helper for Definition 1.8.4: the affine segment map `t ↦ x + t • h` is continuous on
`[0,1]`. -/
lemma segment_affine_map_continuousOn
    (h : WeightedSpace A) :
    ContinuousOn (fun t : ℝ ↦ x + t • h) (Set.Icc (0 : ℝ) 1) := by
  -- The line segment map is affine in the scalar parameter.
  have hseg : Continuous (fun t : ℝ ↦ x + t • h) := by
    exact
      continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ h))
  exact hseg.continuousOn

/-- Helper for Definition 1.8.4: the affine gradient/Hessian model `t ↦ g + t • H h` is
continuous on `[0,1]`. -/
lemma segment_affine_model_continuousOn
    (h : WeightedSpace A) :
    ContinuousOn (fun t : ℝ ↦ g + t • H h) (Set.Icc (0 : ℝ) 1) := by
  -- The affine model depends continuously on the segment parameter.
  have hmodel : Continuous (fun t : ℝ ↦ g + t • H h) := by
    exact
      continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ H h))
  exact hmodel.continuousOn

/-- Helper for Definition 1.8.4: a continuous local weighted vector field stays continuous after
pullback to a short segment and subtraction of the affine model. -/
lemma segment_model_continuousOn_of_vector_field
    {G : WeightedSpace A → WeightedSpace A}
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn G (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r) :
    ContinuousOn (fun t : ℝ ↦ G (x + t • h) - g - t • H h) (Set.Icc (0 : ℝ) 1) := by
  -- Route correction: prove the pullback continuity for a generic vector field before
  -- specializing to the notation-heavy gradient field `∇ f`.
  have hmaps :
      Set.MapsTo (fun t : ℝ ↦ x + t • h) (Set.Icc (0 : ℝ) 1) (Metric.ball x r) := by
    intro t ht
    exact segment_point_mem_ball (A := A) (x := x) hr hh ht
  have hpull :
      ContinuousOn (fun t : ℝ ↦ G (x + t • h)) (Set.Icc (0 : ℝ) 1) := by
    exact hcont_nhds.comp' (segment_affine_map_continuousOn (A := A) (x := x) h) hmaps
  have hneg_model :
      ContinuousOn (fun t : ℝ ↦ -g - t • H h) (Set.Icc (0 : ℝ) 1) := by
    -- Negating the affine model gives the additive correction term in the segment error field.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (segment_affine_model_continuousOn (A := A) (x := x) (g := g) (H := H) h).neg
  -- Then add the negated affine comparison model to the pulled-back vector field.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hpull.add hneg_model

/-- Helper for Definition 1.8.4: if the weighted gradient is continuous on a neighborhood ball of
`x`, then its pullback along a short affine segment is continuous at each parameter value in
`[0,1]`. -/
lemma segment_vector_field_continuousAt
    {G : WeightedSpace A → WeightedSpace A}
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn G (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun s : ℝ ↦ G (x + s • h)) t := by
  -- Upgrade the local ball continuity at the segment point to an ordinary `ContinuousAt`.
  have hy : x + t • h ∈ Metric.ball x r :=
    segment_point_mem_ball (A := A) (x := x) hr hh ht
  have hG_at : ContinuousAt G (x + t • h) := by
    exact (hcont_nhds (x + t • h) hy).continuousAt (Metric.isOpen_ball.mem_nhds hy)
  -- Then compose with the affine segment map at the parameter `t`.
  have hseg : ContinuousAt (fun s : ℝ ↦ x + s • h) t := by
    exact
      (continuous_const.add
        (continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ h))).continuousAt
  simpa using hG_at.comp t hseg

/-- Helper for Definition 1.8.4: if the weighted gradient is continuous on a neighborhood ball of
`x`, then its pullback along a short affine segment is continuous at each parameter value in
`[0,1]`. -/
lemma segment_raw_gradient_continuousAt
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun s : ℝ ↦ ∇ f (x + s • h)) t := by
  -- Apply the generic segment-continuity lemma directly to the gradient field.
  simpa [total_gradient_field] using
    segment_vector_field_continuousAt
      (A := A) (x := x) (G := total_gradient_field (A := A) f) hr
      (HasWeightedGradientSecondOrderExpansionAt.total_gradient_field_continuousOn
        (A := A) (f := f) (x := x) hcont_nhds)
      hh ht

/-- Helper for Definition 1.8.4: the affine-segment gradient error field is continuous on
`[0,1]` once the gradient is continuous on a neighborhood ball of `x`. -/
lemma segment_gradient_model_continuousOn
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r) :
    ContinuousOn (fun t : ℝ ↦ ∇ f (x + t • h) - g - t • H h) (Set.Icc (0 : ℝ) 1) := by
  -- Route the segment error field through the generic vector-field continuity lemma.
  simpa [total_gradient_field] using
    segment_model_continuousOn_of_vector_field
      (A := A) (x := x) (g := g) (H := H) (G := total_gradient_field (A := A) f) hr
      (HasWeightedGradientSecondOrderExpansionAt.total_gradient_field_continuousOn
        (A := A) (f := f) (x := x) hcont_nhds)
      hh

/-- Helper for Definition 1.8.4: along a short weighted segment, the gradient linearization error
paired with the segment direction is continuous on `[0,1]`. -/
lemma segment_quadratic_integrand_continuous
    {r : ℝ} (hr : 0 < r)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r) :
    ContinuousOn
      (fun t : ℝ ↦ (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ))
      (Set.Icc (0 : ℝ) 1) := by
  -- Pair the continuous segment error field with the fixed direction `h`.
  exact
    weighted_segment_pair_continuousOn
      (segment_gradient_model_continuousOn
        (A := A) (f := f) (x := x) (g := g) (H := H) hr hcont_nhds hh) h

/-- Helper for Definition 1.8.4: the corrected quadratic remainder on a short weighted segment is
the integral of the gradient linearization error along that segment. -/
lemma segment_quadratic_remainder_eq_integral
    {r : ℝ} (hr : 0 < r)
    (hgrad_nhds : ∀ y ∈ Metric.ball x r, HasGradientAt f (∇ f y) y)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    {h : WeightedSpace A} (hh : ‖h‖ < r) :
    f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) =
      ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) := by
  let F : ℝ → ℝ := fun u ↦
    f (x + u • h) - f x - u * (⟪g, h⟫_[A] : ℝ) -
      (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ)
  have hFTC :
      ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) = F 1 - F 0 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := F)
      (f' := fun t : ℝ ↦ (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ))
      (by
        intro t ht
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le zero_le_one] using ht
        simpa [F] using
          segment_quadratic_remainder_hasDerivAt
            (A := A) (f := f) (x := x) (g := g) (H := H) hr hgrad_nhds hh ht')
      ((segment_quadratic_integrand_continuous
        (A := A) (f := f) (x := x) (g := g) (H := H) hr hcont_nhds hh).intervalIntegrable_of_Icc
        zero_le_one)
  have hF0 : F 0 = 0 := by
    simp [F]
  calc
    f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))
        = F 1 := by
          simp [F]
          ring
    _ = F 1 - F 0 := by rw [hF0, sub_zero]
    _ = ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) := by
          symm
          exact hFTC

/-- Helper for Definition 1.8.4: segment scaling by a parameter in `[0,1]` does not increase the
weighted norm. -/
lemma norm_smul_le_of_mem_Icc
    {h : WeightedSpace A} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖t • h‖ ≤ ‖h‖ := by
  calc
    ‖t • h‖ = t * ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
    _ ≤ 1 * ‖h‖ := by
      gcongr
      exact ht.2
    _ = ‖h‖ := by
      ring

/-- Helper for Definition 1.8.4: if a displacement lies in a ball around the origin, then every
scaled segment point `t • h` with `t ∈ [0,1]` stays in the same ball. -/
lemma smul_mem_ball_zero_of_mem_Icc
    {δ : ℝ} {h : WeightedSpace A} (hh : h ∈ Metric.ball (0 : WeightedSpace A) δ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • h ∈ Metric.ball (0 : WeightedSpace A) δ := by
  rw [Metric.mem_ball, dist_eq_norm] at hh
  rw [Metric.mem_ball, dist_eq_norm]
  calc
    ‖t • h‖ = t * ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
    _ ≤ ‖h‖ := by
      nlinarith [norm_nonneg h, ht.1, ht.2]
    _ < δ := hh

/-- Helper for Definition 1.8.4: the derivative remainder of the weighted totalized gradient is
uniformly controlled along scaled segments once the displacement is sufficiently small. -/
lemma scaledSegmentDerivativeRemainderBound
    (hg : HasGradientAt f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    ∀ ε > 0,
      ∀ᶠ h : WeightedSpace A in 𝓝 (0 : WeightedSpace A),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖∇ f (x + t • h) - g - H (t • h)‖ ≤ ε * ‖t • h‖ := by
  -- Transport the derivative remainder bound from `k` to every contracted segment point `t • h`.
  intro ε hε
  have hderiv :=
    HasWeightedGradientSecondOrderExpansionAt.gradientDerivativeRemainderAtZero
      (A := A) (f := f) (x := x) (g := g) (H := H) hg hgrad
  have hsmall :
      ∀ᶠ k : WeightedSpace A in 𝓝 (0 : WeightedSpace A),
        ‖∇ f (x + k) - g - H k‖ ≤ ε * ‖k‖ :=
    hderiv.bound hε
  rcases Metric.eventually_nhds_iff_ball.mp hsmall with ⟨δ, hδ, hδbound⟩
  refine (Metric.eventually_nhds_iff_ball (x := (0 : WeightedSpace A))).2 ?_
  refine ⟨δ, hδ, ?_⟩
  intro h hh t ht
  have hth : t • h ∈ Metric.ball (0 : WeightedSpace A) δ :=
    smul_mem_ball_zero_of_mem_Icc (A := A) hh ht
  exact hδbound (t • h) hth

/-- Helper for Definition 1.8.4: the Fréchet derivative of the weighted totalized gradient gives a
uniform `ε * t * ‖h‖²` bound for the segment integrand once `h` is small. -/
lemma gradient_linearization_on_segment_abs_le
    (hg : HasGradientAt f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    ∀ ε > 0,
      ∀ᶠ h : WeightedSpace A in 𝓝 (0 : WeightedSpace A),
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |(⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ)| ≤ ε * t * ‖h‖ ^ (2 : ℕ) := by
  -- Rewrite the linear map on `t • h` and pair the resulting vector estimate with `h`.
  intro ε hε
  have hvectorBound :=
    scaledSegmentDerivativeRemainderBound
      (A := A) (f := f) (x := x) (g := g) (H := H) hg hgrad ε hε
  rcases Metric.eventually_nhds_iff_ball.mp hvectorBound with ⟨δ, hδ, hδbound⟩
  refine (Metric.eventually_nhds_iff_ball (x := (0 : WeightedSpace A))).2 ?_
  refine ⟨δ, hδ, ?_⟩
  intro h hh t ht
  have hbound : ‖∇ f (x + t • h) - g - t • H h‖ ≤ ε * ‖t • h‖ := by
    simpa [ContinuousLinearMap.map_smul] using hδbound h hh t ht
  have hinner :
      |(⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ)| ≤
        ‖∇ f (x + t • h) - g - t • H h‖ * ‖h‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (∇ f (x + t • h) - g - t • H h) h)
  calc
    |(⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ)| ≤
        ‖∇ f (x + t • h) - g - t • H h‖ * ‖h‖ := hinner
    _ ≤ (ε * ‖t • h‖) * ‖h‖ := by
      gcongr
    _ = ε * t * ‖h‖ ^ (2 : ℕ) := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      ring

/-- Helper for Definition 1.8.4: a genuine local weighted gradient field together with the
Fréchet derivative of that field at the basepoint gives the source-facing weighted quadratic
expansion. -/
lemma weighted_second_order_of_local_gradient_field
    {r : ℝ} (hr : 0 < r)
    (hgrad_nhds : ∀ y ∈ Metric.ball x r,
      @HasGradientAt ℝ (WeightedSpace A) inferInstance inferInstance inferInstance inferInstance
        f (∇ f y) y)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r))
    (hg : @HasGradientAt ℝ (WeightedSpace A) inferInstance inferInstance inferInstance
      inferInstance f g x)
    (hgrad : HasFDerivAt (∇ f) H x) :
    HasWeightedGradientSecondOrderExpansionAt A f g H x := by
  -- Control the corrected remainder by the segment integral, then integrate the `2 * ε * t` majorant.
  rw [HasWeightedGradientSecondOrderExpansionAt, Asymptotics.isLittleO_iff]
  intro ε hε
  have hsegmentBound :=
    gradient_linearization_on_segment_abs_le
      (A := A) (f := f) (x := x) (g := g) (H := H) hg hgrad (2 * ε) (by positivity)
  rcases Metric.eventually_nhds_iff_ball.mp hsegmentBound with ⟨δ, hδ, hδbound⟩
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro h hh
  rw [Metric.mem_ball, dist_eq_norm] at hh
  have hhδ : h ∈ Metric.ball (0 : WeightedSpace A) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hh (min_le_left _ _)
  have hhr : ‖h‖ < r := by
    exact lt_of_lt_of_le hh (min_le_right _ _)
  have hEq :
      f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) =
        ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) := by
    let F : ℝ → ℝ := fun u ↦
      f (x + u • h) - f x - u * (⟪g, h⟫_[A] : ℝ) -
        (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ)
    have hFTC :
        ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) = F 1 - F 0 := by
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := F)
        (f' := fun t : ℝ ↦ (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ))
        (by
          intro t ht
          have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le zero_le_one] using ht
          simpa [F] using
            segment_quadratic_remainder_hasDerivAt
              (A := A) (f := f) (x := x) (g := g) (H := H) hr hgrad_nhds hhr ht')
        ((segment_quadratic_integrand_continuous
          (A := A) (f := f) (x := x) (g := g) (H := H) hr hcont_nhds hhr).intervalIntegrable_of_Icc
          zero_le_one)
    have hF0 : F 0 = 0 := by
      simp [F]
    calc
      f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))
          = F 1 := by
            simp [F]
            ring
      _ = F 1 - F 0 := by rw [hF0, sub_zero]
      _ = ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) := by
            symm
            exact hFTC
  have hmajorant_integrable :
      IntervalIntegrable (fun t : ℝ ↦ (2 * ε) * t * ‖h‖ ^ (2 : ℕ)) MeasureTheory.volume 0 1 := by
    exact ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hnorm_integral :
      ‖∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ)‖ ≤
        ∫ t in 0..1, (2 * ε) * t * ‖h‖ ^ (2 : ℕ) := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hmajorant_integrable
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    simpa [Real.norm_eq_abs] using hδbound h hhδ t ht'
  have hmajorant_eval :
      ∫ t in 0..1, (2 * ε) * t * ‖h‖ ^ (2 : ℕ) = ε * ‖h‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring
  have hbound :
      ‖f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))‖ ≤
        ε * ‖h‖ ^ (2 : ℕ) := by
    rw [hEq]
    calc
      ‖∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ)‖ ≤
          ∫ t in 0..1, (2 * ε) * t * ‖h‖ ^ (2 : ℕ) := hnorm_integral
      _ = ε * ‖h‖ ^ (2 : ℕ) := hmajorant_eval
  simpa [Real.norm_of_nonneg (by positivity)] using hbound

/-- The auxiliary quadratic expansion only depends on the adjoint average of the operator in the
quadratic term. -/
theorem iff_adjointAverage :
    HasWeightedGradientSecondOrderExpansionAt A f g H x ↔
      HasWeightedGradientSecondOrderExpansionAt A f g ((1 / 2 : ℝ) • (H + H.adjoint)) x := by
  let Hsymm : WeightedSpace A →L[ℝ] WeightedSpace A := ((1 / 2 : ℝ) • (H + H.adjoint))
  -- Replace the quadratic term pointwise by its adjoint-average representative.
  have hquad :
      ∀ h : WeightedSpace A, (⟪Hsymm h, h⟫_[A] : ℝ) = (⟪H h, h⟫_[A] : ℝ) := by
    intro h
    simpa [Hsymm] using quadratic_form_adjointAverage_eq (A := A) (H := H) h
  constructor <;> intro hExp
  · convert hExp using 1
    ext h
    simp [HasWeightedGradientSecondOrderExpansionAt, Hsymm, hquad h]
  · convert hExp using 1
    ext h
    simp [HasWeightedGradientSecondOrderExpansionAt, Hsymm, hquad h]

/-- Helper for Definition 1.8.4: along a fixed weighted line, the quadratic norm
`‖t • d‖[A]^2` is bounded by a constant multiple of `t^2`. -/
lemma lineNormSquareQuadraticBound
    (d : WeightedSpace A) :
    (fun t : ℝ ↦ (‖t • d‖[A] : ℝ) ^ (2 : ℕ)) =O[𝓝 (0 : ℝ)] fun t ↦ t ^ (2 : ℕ) := by
  -- Pull the constant direction norm out of the quadratic scaling relation `‖t • d‖ = |t| ‖d‖`.
  refine Asymptotics.IsBigO.of_bound (‖d‖ ^ (2 : ℕ)) ?_
  filter_upwards [Filter.Eventually.of_forall fun t : ℝ ↦ ?_] with t
  calc
    ‖((‖t • d‖[A] : ℝ) ^ (2 : ℕ))‖ = (‖t • d‖[A] : ℝ) ^ (2 : ℕ) := by
      rw [Real.norm_of_nonneg]
      positivity
    _ = (|t| * ‖d‖) ^ (2 : ℕ) := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = ‖d‖ ^ (2 : ℕ) * ‖t ^ (2 : ℕ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
      ring

/-- Helper for Definition 1.8.4: evaluating the weighted quadratic model on a line rewrites the
source remainder into the scalar line-restriction form. -/
lemma line_model_apply
    (d : WeightedSpace A) (t : ℝ) :
    f (x + t • d) -
        (f x
          + t * (⟪g, d⟫_[A] : ℝ)
          + (1 / 2 : ℝ) * t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ)) =
      ((fun h : WeightedSpace A ↦
          f (x + h) -
            (f x
              + (⟪g, h⟫_[A] : ℝ)
              + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)))
        (t • d)) := by
  -- Expand the line parameter through the linear and quadratic pieces of the model.
  simp only
  have hg_line : (⟪g, t • d⟫_[A] : ℝ) = t * (⟪g, d⟫_[A] : ℝ) := by
    simpa [Matrix.PosDef.weightedInner] using (real_inner_smul_right g d t)
  have hH_line : (⟪H (t • d), t • d⟫_[A] : ℝ) = t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ) := by
    calc
      (⟪H (t • d), t • d⟫_[A] : ℝ) = (⟪t • H d, t • d⟫_[A] : ℝ) := by
        rw [ContinuousLinearMap.map_smul]
      _ = t * (⟪t • H d, d⟫_[A] : ℝ) := by
        simpa [Matrix.PosDef.weightedInner] using (real_inner_smul_right (t • H d) d t)
      _ = t * (t * (⟪H d, d⟫_[A] : ℝ)) := by
        congr 1
        simpa [Matrix.PosDef.weightedInner] using (real_inner_smul_left d (H d) t)
      _ = t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ) := by
        ring
  rw [hg_line, hH_line]
  ring

/-- Helper for Definition 1.8.4: restricting the weighted quadratic expansion to a fixed line
records the textbook quadratic coefficient `⟪H d, d⟫_[A]`. -/
lemma line_restriction_has_weighted_second_order_expansion
    (hExp : HasWeightedGradientSecondOrderExpansionAt A f g H x) :
    ∀ d : WeightedSpace A,
      (fun t : ℝ ↦
        f (x + t • d) -
          (f x
            + t * (⟪g, d⟫_[A] : ℝ)
            + (1 / 2 : ℝ) * t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ))) =o[𝓝 (0 : ℝ)]
        fun t ↦ t ^ (2 : ℕ) := by
  intro d
  let line : ℝ → WeightedSpace A := fun t ↦ t • d
  -- Compose the source-facing expansion with the affine line `t ↦ t • d`.
  have hline : Filter.Tendsto line (𝓝 (0 : ℝ)) (𝓝 (0 : WeightedSpace A)) := by
    simpa [line] using
      ((continuous_id.smul (continuous_const : Continuous fun _ : ℝ ↦ d)).tendsto (0 : ℝ))
  have hcomp := hExp.comp_tendsto hline
  -- Then replace the line norm by its scalar quadratic representative `t^2`.
  have hmain := hcomp.trans_isBigO (lineNormSquareQuadraticBound (A := A) d)
  have hrewrite :
      (fun t : ℝ ↦
        f (x + t • d) -
          (f x
            + t * (⟪g, d⟫_[A] : ℝ)
            + (1 / 2 : ℝ) * t ^ (2 : ℕ) * (⟪H d, d⟫_[A] : ℝ))) =ᶠ[𝓝 (0 : ℝ)]
        ((fun h : WeightedSpace A ↦
          f (x + h) -
            (f x
              + (⟪g, h⟫_[A] : ℝ)
              + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))) ∘ line) := by
    -- Rewrite the linear and quadratic terms on the line using bilinearity and linearity of `H`.
    refine Filter.Eventually.of_forall ?_
    intro t
    simpa [Function.comp_apply, line] using line_model_apply (A := A) (f := f) (x := x)
      (g := g) (H := H) d t
  exact hrewrite.trans_isLittleO hmain

/-- Helper for Definition 1.8.4: packaging the honest local-gradient-field hypotheses as a single
implication gives a direct source-facing wrapper theorem. -/
theorem hasWeightedGradientSecondOrderExpansionAt_of_local_gradient_field
    {r : ℝ} (hr : 0 < r)
    (hgrad_nhds : ∀ y ∈ Metric.ball x r,
      @HasGradientAt ℝ (WeightedSpace A) inferInstance inferInstance inferInstance inferInstance
        f (∇ f y) y)
    (hcont_nhds : ContinuousOn (∇ f) (Metric.ball x r)) :
    ((@HasGradientAt ℝ (WeightedSpace A) inferInstance inferInstance inferInstance inferInstance
        f g x) ∧
      HasFDerivAt (∇ f) H x) →
      HasWeightedGradientSecondOrderExpansionAt A f g H x := by
  -- Unpack the derivative pair and feed it to the local-gradient-field expansion theorem.
  rintro ⟨hg, hgrad⟩
  rw [HasWeightedGradientSecondOrderExpansionAt, Asymptotics.isLittleO_iff]
  intro ε hε
  have hsegmentBound :=
    gradient_linearization_on_segment_abs_le
      (A := A) (f := f) (x := x) (g := g) (H := H) hg hgrad (2 * ε) (by positivity)
  rcases Metric.eventually_nhds_iff_ball.mp hsegmentBound with ⟨δ, hδ, hδbound⟩
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨min δ r, lt_min hδ hr, ?_⟩
  intro h hh
  rw [Metric.mem_ball, dist_eq_norm] at hh
  have hhδ : h ∈ Metric.ball (0 : WeightedSpace A) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le hh (min_le_left _ _)
  have hhr : ‖h‖ < r := by
    exact lt_of_lt_of_le hh (min_le_right _ _)
  have hEq :
      f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ)) =
        ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) := by
    let F : ℝ → ℝ := fun u ↦
      f (x + u • h) - f x - u * (⟪g, h⟫_[A] : ℝ) -
        (1 / 2 : ℝ) * u ^ (2 : ℕ) * (⟪H h, h⟫_[A] : ℝ)
    have hFTC :
        ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) = F 1 - F 0 := by
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := F)
        (f' := fun t : ℝ ↦ (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ))
        (by
          intro t ht
          have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
            simpa [Set.uIcc_of_le zero_le_one] using ht
          simpa [F] using
            segment_quadratic_remainder_hasDerivAt
              (A := A) (f := f) (x := x) (g := g) (H := H) hr hgrad_nhds hhr ht')
        ((segment_quadratic_integrand_continuous
          (A := A) (f := f) (x := x) (g := g) (H := H) hr hcont_nhds hhr).intervalIntegrable_of_Icc
          zero_le_one)
    have hF0 : F 0 = 0 := by
      simp [F]
    calc
      f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))
          = F 1 := by
            simp [F]
            ring
      _ = F 1 - F 0 := by rw [hF0, sub_zero]
      _ = ∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ) := by
            symm
            exact hFTC
  have hmajorant_integrable :
      IntervalIntegrable (fun t : ℝ ↦ (2 * ε) * t * ‖h‖ ^ (2 : ℕ)) MeasureTheory.volume 0 1 := by
    exact ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hnorm_integral :
      ‖∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ)‖ ≤
        ∫ t in 0..1, (2 * ε) * t * ‖h‖ ^ (2 : ℕ) := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hmajorant_integrable
    refine Filter.Eventually.of_forall ?_
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    simpa [Real.norm_eq_abs] using hδbound h hhδ t ht'
  have hmajorant_eval :
      ∫ t in 0..1, (2 * ε) * t * ‖h‖ ^ (2 : ℕ) = ε * ‖h‖ ^ (2 : ℕ) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_id]
    ring
  have hbound :
      ‖f (x + h) - (f x + (⟪g, h⟫_[A] : ℝ) + (1 / 2 : ℝ) * (⟪H h, h⟫_[A] : ℝ))‖ ≤
        ε * ‖h‖ ^ (2 : ℕ) := by
    rw [hEq]
    calc
      ‖∫ t in 0..1, (⟪∇ f (x + t • h) - g - t • H h, h⟫_[A] : ℝ)‖ ≤
          ∫ t in 0..1, (2 * ε) * t * ‖h‖ ^ (2 : ℕ) := hnorm_integral
      _ = ε * ‖h‖ ^ (2 : ℕ) := hmajorant_eval
  simpa [Real.norm_of_nonneg (by positivity)] using hbound

end HasWeightedGradientSecondOrderExpansionAt

end

end
