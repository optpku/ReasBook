/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped DikinEllipsoidNotation Gradient HessianLocalNorm NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.2.2 lies in the Chapter 5 self-concordant Newton local-convergence domain.

Sampled owner declarations:
* `selfConcordantNewtonNextPoint` and `selfConcordantNewtonShift` in `Definition_5_2_1`, the
  Chapter 5 owners for the three one-step Newton variants;
* `newtonDecrement` and the notation `λ[f; x | hx]`, the chapter owner for the Newton decrement;
* `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem`, which supplies the determinant
  witness needed by `selfConcordantNewtonNextPoint`;
* `Nesterov.Chap05.Theorem_5_2_2.Support`, the canonical owner for the determinant-based
  transport and residual helpers used below.

Best owner abstraction:
* source-facing: the three source clauses of Theorem 5.2.2 for the standard, damped, and
  intermediate one-step updates;
* core/canonical: `selfConcordantNewtonNextPoint` together with the Newton decrement notation;
* bridge/view: the determinant witness derived from `x ∈ dom`.

This repair keeps the item as the three numbered source-facing clauses of Theorem 5.2.2.
The textbook parameter `M_f` is positive, so each clause is stated on the canonical positive
surface `Mf : NNRealˣ`, matching the nearby Chapter 5 API for the damped and intermediate
variants.
-/

section SourceFaithfulPublicAPI

variable {dom : Set E} {Mf : NNRealˣ} {f : E → ℝ}
variable [IsSelfConcordantOnWith dom (Mf : NNReal) f] [HasPositiveDefiniteHessianOn dom f]

/- Common helper layer extracted from `Theorem_5_2_2.lean` so the source-facing item file only checks the final branch wrappers. -/

/-- Helper for Theorem 5.2.2: nonnegative scalar dilations scale the Hessian local norm at a
point with positive Hessian. -/
theorem hessianLocalNorm_smul_of_nonneg
    {x u : E}
    (hPos : (hessian f x).IsPositive) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[f; x] = τ * ‖u‖[f; x] := by
  -- Expand the local norm once, then pull the nonnegative scalar through the square root.
  have hquad : 0 ≤ inner ℝ u (hessian f x u) := hPos.inner_nonneg_right u
  calc
    ‖τ • u‖[f; x] = Real.sqrt ((τ * τ) * inner ℝ u (hessian f x u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f x u)) * Real.sqrt (τ * τ) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = τ * ‖u‖[f; x] := by
      rw [show τ * τ = τ ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ,
        hessianLocalNorm_def]
      ring

/-- Helper for Theorem 5.2.2: the Newton displacement is the negative step size times the
inverse-Hessian gradient direction. -/
theorem next_point_sub_eq_neg_stepSize_smul_inverse_gradient
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    let α := selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH
    selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH - x =
      -(α • (hessian f x).inverse (∇ f x)) := by
  -- Subtract the base point from the explicit one-step Newton formula.
  dsimp [selfConcordantNewtonStepSize]
  rw [selfConcordantNewtonNextPoint_def]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Theorem 5.2.2: the base local norm of the Newton displacement is the step size
times the determinant-based decrement. -/
theorem next_point_sub_localNorm_eq_stepSize_mul_ndec
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0) :
    let δ := ndec(f, x, (Mf : NNReal), hx, hH)
    let α := selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH
    ‖selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH - x‖[f; x] = α * δ := by
  let δ := ndec(f, x, (Mf : NNReal), hx, hH)
  let α := selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH
  let v : E := (hessian f x).inverse (∇ f x)
  let hPos : (hessian f x).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let hInv : (hessian f x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hα_nonneg : 0 ≤ α := by
    exact le_of_lt (selfConcordantNewtonStepSize_pos f (Mf : NNReal) variant x hx hH)
  have hv_eq : hessian f x v = ∇ f x := hInv.self_apply_inverse (∇ f x)
  have hv_norm : ‖v‖[f; x] = δ := by
    -- The local norm of the inverse-Hessian gradient direction is exactly the Newton decrement.
    rw [hessianLocalNorm_def]
    calc
      Real.sqrt (inner ℝ v (hessian f x v))
          = Real.sqrt (inner ℝ (∇ f x) v) := by rw [hv_eq, real_inner_comm]
      _ = δ := by
        simpa [δ, v] using (NewtonDecrement.ofDetNeZero_def (Mf : NNReal) f hx hH).symm
  -- Rewrite the displacement, then scale the local norm by the positive step size.
  calc
    ‖selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH - x‖[f; x]
        = ‖α • v‖[f; x] := by
            rw [next_point_sub_eq_neg_stepSize_smul_inverse_gradient
              (Mf := Mf) (f := f) variant hx hH]
            rw [hessianLocalNorm_neg]
    _ = α * ‖v‖[f; x] := hessianLocalNorm_smul_of_nonneg (f := f) hPos hα_nonneg
    _ = α * δ := by rw [hv_norm]

/-- Helper for Theorem 5.2.2: the intermediate Newton step size has the simplified textbook
rational form. -/
theorem intermediate_stepSize_eq
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let δ := ndec(f, x, (Mf : NNReal), hx, hH)
    selfConcordantNewtonStepSize f (Mf : NNReal) .intermediate x hx hH =
      (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) := by
  let δ := ndec(f, x, (Mf : NNReal), hx, hH)
  have hδ_nonneg : 0 ≤ δ := NewtonDecrement.ofDetNeZero_nonneg (Mf : NNReal) f hx hH
  have hshift_den_pos : 0 < 1 + (Mf : ℝ) * δ := by
    positivity
  -- Expand the intermediate shift and normalize the resulting rational expression.
  rw [selfConcordantNewtonStepSize]
  simp [selfConcordantNewtonShift]
  field_simp [hshift_den_pos.ne']

/-- Helper for Theorem 5.2.2: the intermediate-step radius is strictly below the reciprocal Dikin
threshold. -/
theorem intermediate_step_localNorm_lt_inv
    {δ : ℝ} (hδ_nonneg : 0 ≤ δ) :
    δ * (1 + (Mf : ℝ) * δ) /
        (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) <
      1 / (Mf : ℝ) := by
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hden_pos :
      0 <
        1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ) := by
    positivity
  -- Compare the scaled numerator directly against the common positive denominator.
  refine (lt_div_iff₀ hMf_pos).2 ?_
  have hscaled_lt :
      (((Mf : ℝ) * δ) * (1 + (Mf : ℝ) * δ)) /
          (1 + (Mf : ℝ) * δ + (Mf : ℝ) ^ (2 : ℕ) * δ ^ (2 : ℕ)) <
        1 := by
    refine (div_lt_iff₀ hden_pos).2 ?_
    nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled_lt

/-- Helper for Theorem 5.2.2: the inverse-Hessian Newton direction has base local norm equal to
the old Newton decrement. -/
theorem inverseNewtonDirectionLocalNorm_eq_ndec
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    let H := hessian f x
    let u := H.inverse (∇ f x)
    ‖u‖[f; x] = ndec(f, x, (Mf : NNReal), hx, hH) := by
  let H : E →L[ℝ] E := hessian f x
  let u : E := H.inverse (∇ f x)
  let xStd := selfConcordantNewtonNextPoint f (Mf : NNReal) .standard x hx hH
  have hdisp :
      xStd - x = -u := by
    simpa [xStd, H, u, selfConcordantNewtonStepSize, selfConcordantNewtonShift] using
      next_point_sub_eq_neg_stepSize_smul_inverse_gradient
        (Mf := Mf) (f := f) .standard hx hH
  have hnorm :
      ‖xStd - x‖[f; x] = ndec(f, x, (Mf : NNReal), hx, hH) := by
    simpa [xStd, selfConcordantNewtonStepSize, selfConcordantNewtonShift] using
      next_point_sub_localNorm_eq_stepSize_mul_ndec
        (Mf := Mf) (f := f) .standard hx hH
  -- Compare the Newton direction to the standard displacement, whose local norm is already known.
  calc
    ‖u‖[f; x] = ‖-u‖[f; x] := by rw [hessianLocalNorm_neg]
    _ = ‖xStd - x‖[f; x] := by rw [hdisp]
    _ = ndec(f, x, (Mf : NNReal), hx, hH) := hnorm

/-- Helper for Theorem 5.2.2: the damped-step convex-combination coefficient simplifies to the
textbook scalar factor. -/
theorem dampedStepCoefficientIdentity
    {α a s : ℝ} (hs_nonneg : 0 ≤ s) (hα : α = 1 / (1 + s)) (ha : a = s / (1 + s)) :
    ((1 - α) / (1 - a) + α * (a / (1 - a))) = s * (1 + 1 / (1 + s)) := by
  have hden_pos : 0 < 1 + s := by
    linarith
  -- Normalize every scalar term over the shared denominator `1 + s`.
  rw [hα, ha]
  field_simp [hden_pos.ne']
  ring

/-- Helper for Theorem 5.2.2: the intermediate-step convex-combination coefficient simplifies to
the explicit textbook scalar factor. -/
theorem intermediateStepCoefficientIdentity
    {α a s : ℝ} (hs_nonneg : 0 ≤ s)
    (hα : α = (1 + s) / (1 + s + s ^ (2 : ℕ)))
    (ha : a = s * (1 + s) / (1 + s + s ^ (2 : ℕ))) :
    ((1 - α) / (1 - a) + α * (a / (1 - a))) =
      s * (1 + s + s / (1 + s + s ^ (2 : ℕ))) := by
  have hden_pos : 0 < 1 + s + s ^ (2 : ℕ) := by
    positivity
  -- Normalize the intermediate coefficient over the common denominator `1 + s + s²`.
  rw [hα, ha]
  field_simp [hden_pos.ne']
  ring

/-- Helper for Theorem 5.2.2: affine lines have the expected derivative. -/
theorem line_hasDerivAt
    (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar parameter while keeping the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 5.2.2: every affine parameter `t ∈ [0, 1]` produces the corresponding
point on the segment from `x` to `y`. -/
theorem segment_point_mem_segment
    {x y : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine interpolation point into the canonical line-map description of the
  -- segment.
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Theorem 5.2.2: each point on the segment from `x` to `y` stays in the convex
self-concordant domain. -/
theorem segment_point_mem
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ dom := by
  -- Rewrite the segment point as a convex combination and use domain convexity.
  have hrewrite : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub]
    rw [show (1 - t : ℝ) • x = x - t • x by rw [sub_smul, one_smul]]
    abel
  have hconv := hself.convex_domain
  have h1t : 0 ≤ 1 - t := by
    linarith
  have hsum : (1 - t) + t = 1 := by
    ring
  rw [hrewrite]
  exact hconv hx hy h1t ht0 hsum

/-- Helper for Theorem 5.2.2: the Hessian is continuous on the self-concordant domain. -/
theorem hessian_continuousOn :
    IsSelfConcordantOnWith dom (Mf : NNReal) f → ContinuousOn (hessian f) dom := by
  intro hself
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ f) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) dom :=
      (hself.contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          hself.isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  -- Differentiate the gradient once more on the open domain to reach the Hessian.
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen
      hself.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn

/-- Helper for Theorem 5.2.2: scalarizing the gradient along an affine segment differentiates to
the corresponding Hessian pairing. -/
theorem scalarized_gradient_line_hasDerivAt
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x d u : E} {t : ℝ} (hxt : x + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) u)
      (inner ℝ (hessian f (x + t • d) d) u) t := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) (x + t • d) := by
    have hcont : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • d) :=
      (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hxt)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)
    exact hcont.differentiableAt one_ne_zero
  have hgrad : DifferentiableAt ℝ (∇ f) (x + t • d) := by
    -- Rewrite the gradient through the Riesz map before differentiating it.
    simpa [gradient, D] using D.differentiableAt.comp (x + t • d) hfderiv
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (x + s • d))
        ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Compose the gradient derivative with the affine-line derivative.
    simpa using (hgrad.hasFDerivAt.comp t (line_hasDerivAt x d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (x + s • d)))
        (φ.comp ((hessian f (x + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional to obtain the one-dimensional derivative.
    simpa [φ] using (φ.hasFDerivAt.comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5.2.2: integrating the Hessian along the segment from `x` to `y`
recovers the gradient increment when paired against any fixed direction. -/
theorem gradient_difference_pairing_eq_average_hessian_step
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x y u : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    let d := y - x
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • d)
    inner ℝ (∇ f y - ∇ f x) u = inner ℝ (G d) u := by
  let d : E := y - x
  let H : ℝ → E →L[ℝ] E := fun τ ↦ hessian f (x + τ • d)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, H τ
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hline_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
    intro τ hτ
    exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ)
  have hH_cont : ContinuousOn H (Set.Icc (0 : ℝ) 1) := by
    -- Restrict the continuous Hessian field to the affine segment joining `x` and `y`.
    simpa [H, d] using
      (hessian_continuousOn (dom := dom) (Mf := Mf) (f := f) hself).comp
        (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
        hline_maps
  have hH_int : IntervalIntegrable H MeasureTheory.volume 0 1 :=
    hH_cont.intervalIntegrable_of_Icc (by norm_num)
  have hH_apply_cont (v : E) : ContinuousOn (fun τ : ℝ ↦ H τ v) (Set.Icc (0 : ℝ) 1) := by
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E v
    simpa [H, ev] using ev.continuous.comp_continuousOn hH_cont
  have hH_apply_int (v : E) :
      IntervalIntegrable (fun τ : ℝ ↦ H τ v) MeasureTheory.volume 0 1 :=
    (hH_apply_cont v).intervalIntegrable_of_Icc (by norm_num)
  let g : ℝ → ℝ := fun τ ↦ inner ℝ (∇ f (x + τ • d)) u
  let θ : ℝ → ℝ := fun τ ↦ inner ℝ (H τ d) u
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    exact
      (scalarized_gradient_line_hasDerivAt (hself := hself)
        (x := x) (d := d) (u := u) (hxt := hline_maps hτ)).continuousAt.continuousWithinAt
  have hθ_int : IntervalIntegrable θ MeasureTheory.volume 0 1 := by
    have hθ_cont : ContinuousOn θ (Set.Icc (0 : ℝ) 1) := by
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
      simpa [θ, H, φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
        φ.continuous.comp_continuousOn (hH_apply_cont d)
    exact hθ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv :
      ∀ τ ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (θ τ) τ := by
    intro τ hτ
    simpa [g, θ, H] using
      scalarized_gradient_line_hasDerivAt (hself := hself)
        (x := x) (d := d) (u := u) (hxt := hline_maps (Set.mem_Icc_of_Ioo hτ))
  have hftc : ∫ τ in (0 : ℝ)..1, θ τ = g 1 - g 0 := by
    simpa using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (show (0 : ℝ) ≤ 1 by norm_num) hg_cont hderiv hθ_int
  have hpair_integral : ∫ τ in (0 : ℝ)..1, θ τ = inner ℝ u (G d) := by
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) u
    calc
      ∫ τ in (0 : ℝ)..1, θ τ = ∫ τ in (0 : ℝ)..1, φ (H τ d) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro τ
        simp [θ, φ, InnerProductSpace.toDual_apply_apply, real_inner_comm]
      _ = φ (∫ τ in (0 : ℝ)..1, H τ d) := by
        exact ContinuousLinearMap.intervalIntegral_comp_comm (L := φ) (hH_apply_int d)
      _ = inner ℝ u (∫ τ in (0 : ℝ)..1, H τ d) := by
        simp [φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ u (G d) := by
        rw [ContinuousLinearMap.intervalIntegral_apply hH_int d]
  -- The scalar fundamental theorem of calculus turns the gradient increment into the segment
  -- average Hessian applied to the displacement.
  calc
    inner ℝ (∇ f y - ∇ f x) u = g 1 - g 0 := by
      rw [inner_sub_left]
      simp [g, d]
    _ = ∫ τ in (0 : ℝ)..1, θ τ := by
      symm
      exact hftc
    _ = inner ℝ u (G d) := hpair_integral
    _ = inner ℝ (G d) u := real_inner_comm _ _

/-- Helper for Theorem 5.2.2: Loewner order is preserved after adding a fixed operator on the
right. -/
theorem hessianDifference_isSymmetricPairing
    {A B : E →L[ℝ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (A - B).IsSymmetric := by
  -- Rewrite the pairing of the difference termwise and use symmetry on each summand.
  have hA' : ∀ s t : E, inner ℝ (A s) t = inner ℝ s (A t) := by
    intro s t
    simpa using hA s t
  have hB' : ∀ s t : E, inner ℝ (B s) t = inner ℝ s (B t) := by
    intro s t
    simpa using hB s t
  intro s t
  calc
    inner ℝ ((A - B) s) t = inner ℝ (A s) t - inner ℝ (B s) t := by
      simp [inner_sub_left]
    _ = inner ℝ s (A t) - inner ℝ s (B t) := by
      rw [hA' s t, hB' s t]
    _ = inner ℝ s ((A - B) t) := by
      simp [inner_sub_right]

/-- Helper for Theorem 5.2.2: Loewner order is preserved after adding a fixed operator on the
right. -/
theorem loewnerAddRight_bridge
    {A B C : E →L[ℝ] E} (h : A ≤ B) :
    A + C ≤ B + C := by
  -- Move to the positivity definition and simplify the common right summand away.
  have h' : (B - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using h
  change ((B + C) - (A + C)).IsPositive
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'

/-- Helper for Theorem 5.2.2: a nonnegative scalar preserves Loewner order on Hessian-type
operators. -/
theorem loewnerSmul_mono_of_nonneg
    {A : E →L[ℝ] E} (hA : 0 ≤ A) {a b : ℝ} (hab : a ≤ b) :
    a • A ≤ b • A := by
  have hA' : A.IsPositive := by
    simpa [ContinuousLinearMap.le_def] using hA
  have hba_nonneg : 0 ≤ b - a := by
    linarith
  -- Scale the positive operator `A` by the nonnegative gap `b - a`.
  rw [ContinuousLinearMap.le_def]
  simpa [sub_smul] using hA'.smul_of_nonneg hba_nonneg

/-- Helper for Theorem 5.2.2: scaling both sides of a Loewner inequality by the same nonnegative
scalar preserves the inequality. -/
theorem loewnerSmul_bridge
    {A B : E →L[ℝ] E} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  have h' : (B - A).IsPositive := by
    simpa [ContinuousLinearMap.le_def] using h
  change (c • B - c • A).IsPositive
  simpa [smul_sub] using h'.smul_of_nonneg hc

/-- Helper for Theorem 5.2.2: once the next point stays in the domain, the new gradient splits
into the transported old gradient plus the averaged-Hessian residual. -/
theorem nextGradient_eq_oldGradient_plus_averageResidual
    (variant : SelfConcordantNewtonVariant) {x : E} (hx : x ∈ dom)
    (hH : (hessian f x).det ≠ 0)
    (hxPlus :
      let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH
      xPlus ∈ dom) :
    let α := selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH
    let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH
    let H := hessian f x
    let u := H.inverse (∇ f x)
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (xPlus - x))
    ∇ f xPlus = (1 - α) • ∇ f x + α • ((H - G) u) := by
  let α := selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH
  let xPlus := selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH
  let H : E →L[ℝ] E := hessian f x
  let u : E := H.inverse (∇ f x)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (xPlus - x))
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  have hxPlus' : xPlus ∈ dom := by
    simpa [xPlus] using hxPlus
  have hu : H u = ∇ f x := by
    -- The Newton direction is defined by the inverse Hessian at `x`.
    let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
    exact hInv.self_apply_inverse (∇ f x)
  have hsub :
      xPlus - x = -(α • u) := by
    -- Rewrite the canonical next point into the standard Newton displacement form.
    simpa [α, xPlus, H, u] using
      next_point_sub_eq_neg_stepSize_smul_inverse_gradient
        (Mf := Mf) (f := f) variant hx hH
  apply (InnerProductSpace.toDual ℝ E).injective
  ext v
  have hpair :
      inner ℝ (∇ f xPlus - ∇ f x) v = inner ℝ (G (xPlus - x)) v := by
    simpa [xPlus, G] using
      gradient_difference_pairing_eq_average_hessian_step
        (dom := dom) (Mf := Mf) (f := f) hself hx hxPlus' (u := v)
  have hpair' :
      inner ℝ (∇ f xPlus) v = inner ℝ (∇ f x - α • (G u)) v := by
    have hpair_eq :
        inner ℝ (∇ f xPlus) v =
          inner ℝ (∇ f x) v + inner ℝ (G (xPlus - x)) v := by
      have hpair_expanded :
          inner ℝ (∇ f xPlus) v - inner ℝ (∇ f x) v = inner ℝ (G (xPlus - x)) v := by
        simpa [inner_sub_left] using hpair
      linarith
    -- Expand the gradient increment and replace the displacement by `-α • u`.
    calc
      inner ℝ (∇ f xPlus) v =
          inner ℝ (∇ f x) v + inner ℝ (G (xPlus - x)) v := hpair_eq
      _ = inner ℝ (∇ f x) v + inner ℝ (G (-(α • u))) v := by
        rw [hsub]
      _ = inner ℝ (∇ f x) v + inner ℝ (-α • (G u)) v := by
        simp
      _ = inner ℝ (∇ f x - α • (G u)) v := by
        simp [sub_eq_add_neg, inner_add_left, inner_smul_left, add_comm, add_left_comm,
          add_assoc]
  -- Identify the scalarized equality with the desired vector identity.
  calc
    inner ℝ (∇ f xPlus) v = inner ℝ (∇ f x - α • (G u)) v := hpair'
    _ = inner ℝ ((1 - α) • ∇ f x + α • ((H - G) u)) v := by
      rw [ContinuousLinearMap.sub_apply, hu]
      simp [sub_eq_add_neg, inner_add_left, inner_smul_left, add_comm, add_left_comm,
        add_assoc]
      ring

/-- Helper for Theorem 5.2.2: dualizing the next-gradient formula gives the endpoint decomposition
used by both positive variants. -/
theorem positiveVariantDualGradientDecomposition
    (variant : SelfConcordantNewtonVariant) {x : E}
    (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hy :
      let y := selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH
      y ∈ dom) :
    let y := selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH
    let H := hessian f x
    let u := H.inverse (∇ f x)
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    let α := selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH
    toDual ℝ E (∇ f y) =
      (1 - α) • toDual ℝ E (∇ f x) + α • toDual ℝ E ((H - G) u) := by
  -- Route correction: normalize the positive-variant gradient update once before attempting the
  -- endpoint-metric assembly.
  dsimp
  have hy' :
      selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH ∈ dom := by
    simpa using hy
  have hgrad :
      ∇ f (selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH) =
        (1 - selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH) • ∇ f x +
          selfConcordantNewtonStepSize f (Mf : NNReal) variant x hx hH •
            ((hessian f x -
                ∫ τ in (0 : ℝ)..1,
                  hessian f
                    (x + τ •
                      (selfConcordantNewtonNextPoint f (Mf : NNReal) variant x hx hH - x)))
              ((hessian f x).inverse (∇ f x))) := by
    simpa [selfConcordantNewtonStepSize, selfConcordantNewtonShift] using
      nextGradient_eq_oldGradient_plus_averageResidual
        (Mf := Mf) (f := f) variant hx hH (hxPlus := hy')
  -- Dualize the normalized gradient identity so the endpoint metric sees one fixed spelling.
  simpa [map_add, map_smul] using congrArg (toDual ℝ E) hgrad

/-- Helper for Theorem 5.2.2: each affine segment point inherits the endpoint-free Hessian
comparison with the base point Hessian. -/
theorem segment_point_hessian_bounds
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let z := x + τ • (y - x)
    ((1 - τ * a) ^ (2 : ℕ)) • hessian f x ≤ hessian f z ∧
      hessian f z ≤ ((1 - τ * a) ^ (2 : ℕ))⁻¹ • hessian f x := by
  dsimp
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let z : E := x + τ • (y - x)
  have hτ_nonneg : 0 ≤ τ := hτ.1
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg f x (y - x)
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hy : y ∈ dom :=
    IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset hself hx hxy
  have hz : z ∈ dom := by
    exact segment_point_mem (hself := hself) hx hy hτ.1 hτ.2
  have hxPos : (hessian f x).IsPositive := hself.hessian_isPositive hx
  have hz_norm : ‖z - x‖[f; x] = τ * r := by
    calc
      ‖z - x‖[f; x] = ‖τ • (y - x)‖[f; x] := by
        have hz_sub : z - x = τ • (y - x) := by
          dsimp [z]
          abel
        rw [hz_sub]
      _ = τ * ‖y - x‖[f; x] := hessianLocalNorm_smul_of_nonneg (f := f) hxPos hτ_nonneg
      _ = τ * r := by rfl
  have hτr_le : τ * r ≤ r := by
    have hmul_le : τ * r ≤ 1 * r := mul_le_mul_of_nonneg_right hτ.2 hr_nonneg
    simpa using hmul_le
  let rmid : ℝ := (r + 1 / (Mf : ℝ)) / 2
  have hr_lt_rmid : r < rmid := by
    dsimp [rmid]
    linarith
  have hrmid_lt : rmid < 1 / (Mf : ℝ) := by
    dsimp [rmid]
    linarith
  have hz_mem_rmid : z ∈ W⁰[f; x](rmid) := by
    rw [mem_openDikinEllipsoid_iff]
    have hz_norm_le_r : ‖z - x‖[f; x] ≤ r := by
      rw [hz_norm]
      simpa using hτr_le
    exact lt_of_le_of_lt hz_norm_le_r hr_lt_rmid
  -- Compare `∇²f(z)` to `∇²f(x)` at the exact segment radius, using `rmid` only to discharge
  -- the strict Dikin-radius side condition.
  simpa [a, hz_norm, mul_assoc, mul_left_comm, mul_comm] using
    IsSelfConcordantOnWith.hessian_loewner_bounds_of_exact_local_radius
      (dom := dom) (Mf := (Mf : NNReal)) (f := f) hself
      (x := x) (y := z) (r := rmid) hx hz hrmid_lt hz_mem_rmid

/-- Helper for Theorem 5.2.2: the segment-average Hessian is symmetric because every pointwise
Hessian along the segment is symmetric. -/
theorem segmentAverageHessian_isSymmetric
    (hself : IsSelfConcordantOnWith dom (Mf : NNReal) f)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    (∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))).IsSymmetric := by
  let d : E := y - x
  let Hτ : ℝ → E →L[ℝ] E := fun τ ↦ hessian f (x + τ • d)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, Hτ τ
  have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
  have hHτ_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
    intro τ hτ
    exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ)
  have hHτ_cont : ContinuousOn Hτ (Set.Icc (0 : ℝ) 1) := by
    -- Restrict the continuous Hessian field to the affine segment joining `x` and `y`.
    simpa [Hτ, d] using
      (hessian_continuousOn (dom := dom) (Mf := Mf) (f := f) hself).comp
        (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
        hHτ_maps
  have hHτ_int : IntervalIntegrable Hτ MeasureTheory.volume 0 1 :=
    hHτ_cont.intervalIntegrable_of_Icc (by norm_num)
  have hHτ_apply_cont (w : E) : ContinuousOn (fun τ : ℝ ↦ Hτ τ w) (Set.Icc (0 : ℝ) 1) := by
    let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E w
    simpa [Hτ, ev] using ev.continuous.comp_continuousOn hHτ_cont
  have hHτ_apply_int (w : E) :
      IntervalIntegrable (fun τ : ℝ ↦ Hτ τ w) MeasureTheory.volume 0 1 :=
    (hHτ_apply_cont w).intervalIntegrable_of_Icc (by norm_num)
  have hpair_integral (v₁ v₂ : E) :
      ∫ τ in (0 : ℝ)..1, inner ℝ v₁ (Hτ τ v₂) = inner ℝ v₁ (G v₂) := by
    let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) v₁
    calc
      ∫ τ in (0 : ℝ)..1, inner ℝ v₁ (Hτ τ v₂)
          = ∫ τ in (0 : ℝ)..1, φ (Hτ τ v₂) := by
              refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro τ
              simp [φ, Hτ, InnerProductSpace.toDual_apply_apply]
      _ = φ (∫ τ in (0 : ℝ)..1, Hτ τ v₂) := by
            exact ContinuousLinearMap.intervalIntegral_comp_comm (L := φ) (hHτ_apply_int v₂)
      _ = inner ℝ v₁ (∫ τ in (0 : ℝ)..1, Hτ τ v₂) := by
            simp [φ, InnerProductSpace.toDual_apply_apply]
      _ = inner ℝ v₁ (G v₂) := by
            rw [ContinuousLinearMap.intervalIntegral_apply hHτ_int v₂]
  change ∀ v₁ v₂ : E, inner ℝ (G v₁) v₂ = inner ℝ v₁ (G v₂)
  intro v₁ v₂
  calc
    inner ℝ (G v₁) v₂ = inner ℝ v₂ (G v₁) := real_inner_comm _ _
    _ = ∫ τ in (0 : ℝ)..1, inner ℝ v₂ (Hτ τ v₁) := (hpair_integral v₂ v₁).symm
    _ = ∫ τ in (0 : ℝ)..1, inner ℝ v₁ (Hτ τ v₂) := by
          refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro τ hτ
          have hτIoc : τ ∈ Set.Ioc (0 : ℝ) 1 := by
            simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hτ
          have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := by
            exact ⟨le_of_lt hτIoc.1, hτIoc.2⟩
          have hz : x + τ • d ∈ dom := hHτ_maps hτ'
          have hzPos : (Hτ τ).IsPositive := by
            simpa [Hτ] using hself.hessian_isPositive hz
          simpa [Hτ, real_inner_comm] using hzPos.isSymmetric v₁ v₂
    _ = inner ℝ v₁ (G v₂) := hpair_integral v₁ v₂

/-- Helper for Theorem 5.2.2: a quadratic family bounded above by `c` yields the discriminant
estimate `a² ≤ b c`. -/
theorem sq_le_mul_of_quadratic_family
    {a b c : ℝ} (hb : 0 ≤ b)
    (hline : ∀ t : ℝ, 2 * t * a - t ^ (2 : ℕ) * b ≤ c) :
    a ^ (2 : ℕ) ≤ b * c := by
  -- Split on the degenerate quadratic coefficient and test the family at the critical point.
  by_cases hb_zero : b = 0
  · by_cases ha_zero : a = 0
    · simp [ha_zero, hb_zero]
    · have ha_eq_zero : a = 0 := by
        by_contra ha_ne
        have htest := hline ((|c| + 1) / a)
        have hcontr : 2 * (|c| + 1) ≤ c := by
          have hrew : 2 * ((|c| + 1) / a) * a ≤ c := by
            simpa [hb_zero] using htest
          field_simp [ha_ne] at hrew
          linarith
        have hc_le_abs : c ≤ |c| := le_abs_self c
        have hbad : |c| + 2 ≤ 0 := by
          nlinarith
        have hpos : 0 < |c| + 2 := by
          nlinarith [abs_nonneg c]
        exact (not_le_of_gt hpos) hbad
      exact (ha_zero ha_eq_zero).elim
  · have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
    have htest := hline (a / b)
    have hrewrite :
        2 * (a / b) * a - (a / b) ^ (2 : ℕ) * b = a ^ (2 : ℕ) / b := by
      field_simp [hb_zero]
      ring
    have hquot : a ^ (2 : ℕ) / b ≤ c := by
      simpa [hrewrite] using htest
    simpa [mul_comm] using (div_le_iff₀ hb_pos).1 hquot

/-- Helper for Theorem 5.2.2: a symmetric operator bounded between `-c ∇²f(x)` and
`c ∇²f(x)` has Hessian-metric operator norm at most `c`. -/
theorem sq_hessianLocalNorm_eq_inner_hessian
    {x u : E} (hPos : (hessian f x).IsPositive) :
    ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (hessian f x u) := by
  -- The positivity of `∇²f(x)` makes the square-root definition exact after squaring.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt (hPos.inner_nonneg_right u)

/-- Helper for Theorem 5.2.2: a symmetric operator bounded between `-c ∇²f(x)` and
`c ∇²f(x)` has Hessian-metric operator norm at most `c`. -/
theorem abs_inner_le_mul_localNorm_of_operator_sandwich
    {x u v : E} (hPos : (hessian f x).IsPositive) (K : E →L[ℝ] E) {c : ℝ}
    (hc : 0 ≤ c) (hK_symm : K.IsSymmetric)
    (hlower : -(c • hessian f x) ≤ K) (hupper : K ≤ c • hessian f x) :
    |inner ℝ v (K u)| ≤ c * ‖v‖[f; x] * ‖u‖[f; x] := by
  let H := hessian f x
  have hH_symm : H.IsSymmetric := hPos.isSymmetric
  have hminus_pos : (c • H - K).IsPositive := by
    rw [← ContinuousLinearMap.le_def]
    exact hupper
  have hplus_pos : (c • H + K).IsPositive := by
    have htmp : (K - -(c • H)).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hlower
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
  have hu_quad_nonneg : 0 ≤ c * inner ℝ u (H u) := by
    exact mul_nonneg hc (hPos.inner_nonneg_right u)
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v (K u) - t ^ (2 : ℕ) * (c * inner ℝ u (H u)) ≤
          c * inner ℝ v (H v) := by
    intro t
    have hsum_nonneg :
        0 ≤
          inner ℝ (v - t • u) ((c • H + K) (v - t • u)) +
            inner ℝ (v + t • u) ((c • H - K) (v + t • u)) := by
      exact add_nonneg (hplus_pos.inner_nonneg_right (v - t • u))
        (hminus_pos.inner_nonneg_right (v + t • u))
    have hHu : inner ℝ u (H v) = inner ℝ v (H u) := by
      simpa [real_inner_comm] using hH_symm v u
    have hKu : inner ℝ u (K v) = inner ℝ v (K u) := by
      simpa [real_inner_comm] using hK_symm v u
    have hsum_formula :
        inner ℝ (v - t • u) ((c • H + K) (v - t • u)) +
            inner ℝ (v + t • u) ((c • H - K) (v + t • u)) =
          2 * c * inner ℝ v (H v) - 4 * t * inner ℝ v (K u) +
            2 * t ^ (2 : ℕ) * (c * inner ℝ u (H u)) := by
      simp [H, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, ContinuousLinearMap.map_add,
        ContinuousLinearMap.map_sub, hHu, hKu, pow_two]
      ring
    rw [hsum_formula] at hsum_nonneg
    nlinarith
  have hsq_raw :
      (inner ℝ v (K u)) ^ (2 : ℕ) ≤
        (c * inner ℝ u (H u)) * (c * inner ℝ v (H v)) := by
    have hsq :=
      sq_le_mul_of_quadratic_family
        (a := inner ℝ v (K u))
        (b := c * inner ℝ u (H u))
        (c := c * inner ℝ v (H v))
        hu_quad_nonneg hline
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsq
  have hu_sq : ‖u‖[f; x] ^ (2 : ℕ) = inner ℝ u (H u) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt (hPos.inner_nonneg_right u)
  have hv_sq : ‖v‖[f; x] ^ (2 : ℕ) = inner ℝ v (H v) := by
    rw [hessianLocalNorm_def]
    simpa [H] using Real.sq_sqrt (hPos.inner_nonneg_right v)
  have hsq_abs :
      |inner ℝ v (K u)| ^ (2 : ℕ) ≤
        (c * ‖v‖[f; x] * ‖u‖[f; x]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v (K u)| ^ (2 : ℕ) = (inner ℝ v (K u)) ^ (2 : ℕ) := by
        rw [sq_abs]
      _ ≤ (c * inner ℝ u (H u)) * (c * inner ℝ v (H v)) := hsq_raw
      _ = c ^ (2 : ℕ) * (‖v‖[f; x] ^ (2 : ℕ) * ‖u‖[f; x] ^ (2 : ℕ)) := by
        rw [hu_sq, hv_sq]
        ring
      _ = (c * ‖v‖[f; x] * ‖u‖[f; x]) ^ (2 : ℕ) := by
        ring
  have hright_nonneg : 0 ≤ c * ‖v‖[f; x] * ‖u‖[f; x] := by
    exact mul_nonneg (mul_nonneg hc (hessianLocalNorm_nonneg f x v))
      (hessianLocalNorm_nonneg f x u)
  exact le_of_sq_le_sq hsq_abs hright_nonneg

/-- Helper for Theorem 5.2.2: pairing a vector with an arbitrary direction is controlled by the
dual local norm at the base point times the local norm of the direction. -/
theorem abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm
    {x v z : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) :
    |inner ℝ v z| ≤
      HessianDualLocalNorm.ofDetNeZero f x
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx) hH
        (toDual ℝ E v) * ‖z‖[f; x] := by
  let H := hessian f x
  let w := H.inverse v
  let hPos : H.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hHw : H w = v := by
    dsimp [w, H]
    exact hInv.self_apply_inverse v
  have hquad : 0 ≤ inner ℝ z (H z) := hPos.inner_nonneg_right z
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ v w := by rw [hHw, real_inner_comm]
  have hline :
      ∀ t : ℝ,
        2 * t * inner ℝ v z - t ^ (2 : ℕ) * inner ℝ z (H z) ≤ inner ℝ v w := by
    intro t
    have hnonneg : 0 ≤ inner ℝ (t • z - w) (H (t • z - w)) := hPos.inner_nonneg_right (t • z - w)
    have hcross :
        inner ℝ w (H z) = inner ℝ v z := by
      calc
        inner ℝ w (H z) = inner ℝ (H w) z := by
          simpa [real_inner_comm] using hPos.isSymmetric z w
        _ = inner ℝ v z := by rw [hHw]
    have hrewrite :
        inner ℝ (t • z - w) (H (t • z - w)) =
          t ^ (2 : ℕ) * inner ℝ z (H z) - 2 * t * inner ℝ v z + inner ℝ v w := by
      have hleft :
          inner ℝ (t • z) (H w) = t * inner ℝ v z := by
        rw [hHw, real_inner_comm, inner_smul_right]
      have hright :
          inner ℝ w (t • H z) = t * inner ℝ v z := by
        rw [inner_smul_right, hcross]
      have hdiag :
          inner ℝ w (H w) = inner ℝ v w := by
        rw [hHw, real_inner_comm]
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      rw [hleft, hright, hdiag]
      have hstar_t : (starRingEnd ℝ) t = t := by simp
      rw [hstar_t]
      ring_nf
    rw [hrewrite] at hnonneg
    nlinarith
  have hsq_raw :
      (inner ℝ v z) ^ (2 : ℕ) ≤ inner ℝ z (H z) * inner ℝ v w := by
    have hsq :=
      sq_le_mul_of_quadratic_family (a := inner ℝ v z) (b := inner ℝ z (H z))
        (c := inner ℝ v w) hquad hline
    simpa [mul_comm] using hsq
  have hdual_sq :
      (HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v)) ^ (2 : ℕ) = inner ℝ v w := by
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    simpa [w, H, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      Real.sq_sqrt hpair_nonneg
  have hlocal_sq : ‖z‖[f; x] ^ (2 : ℕ) = inner ℝ z (H z) := by
    exact sq_hessianLocalNorm_eq_inner_hessian (f := f) hPos
  have hsq_abs :
      |inner ℝ v z| ^ (2 : ℕ) ≤
        (HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v) * ‖z‖[f; x]) ^ (2 : ℕ) := by
    calc
      |inner ℝ v z| ^ (2 : ℕ) = (inner ℝ v z) ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ inner ℝ z (H z) * inner ℝ v w := hsq_raw
      _ =
          (HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v)) ^ (2 : ℕ) *
            ‖z‖[f; x] ^ (2 : ℕ) := by rw [hdual_sq, hlocal_sq, mul_comm]
      _ =
          (HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v) * ‖z‖[f; x]) ^ (2 : ℕ) := by
        ring
  have hdual_nonneg : 0 ≤ HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E v) := by
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  exact le_of_sq_le_sq hsq_abs
    (mul_nonneg hdual_nonneg (hessianLocalNorm_nonneg f x z))

/-- Helper for Theorem 5.2.2: the Chapter 2 dual norm of a separated seminorm is bounded above on
the image of the closed primal unit ball, so `le_csSup` can be applied pointwise. -/
theorem seminorm_dualNorm_bddAbove_innerImage_closedBall
    (p : Seminorm ℝ E) [p.IsNorm] (g : E) :
    BddAbove ((fun y : E ↦ inner ℝ g y) '' p.closedBall 0 1) := by
  obtain ⟨C, hC_pos, hnorm_le⟩ := p.exists_norm_le_mul
  refine ⟨‖g‖ * C, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  have hy_norm : ‖y‖ ≤ C := by
    have hpy : p y ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hy
    calc
      ‖y‖ ≤ C * p y := hnorm_le y
      _ ≤ C * 1 := by
        gcongr
      _ = C := by
        ring
  calc
    inner ℝ g y ≤ ‖g‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖g‖ * C := by
      gcongr

/-- Helper for Theorem 5.2.2: the Chapter 2 dual norm is subadditive after passing through the
Riesz identification. -/
theorem seminorm_dualNorm_add_le
    (p : Seminorm ℝ E) [p.IsNorm] (g h : E) :
    Seminorm.dualNorm p (g + h) ≤ Seminorm.dualNorm p g + Seminorm.dualNorm p h := by
  rw [Seminorm.dualNorm_apply]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⟨0, by simpa [Seminorm.mem_closedBall_zero], by simp⟩⟩
  · rintro z ⟨u, hu, rfl⟩
    have hu_ball : u ∈ p.closedBall 0 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hu
    have hg_le : inner ℝ g u ≤ Seminorm.dualNorm p g := by
      have hmem : inner ℝ g u ∈ ((fun y : E ↦ inner ℝ g y) '' p.closedBall 0 1) :=
        ⟨u, hu_ball, rfl⟩
      exact le_csSup (seminorm_dualNorm_bddAbove_innerImage_closedBall p g) hmem
    have hh_le : inner ℝ h u ≤ Seminorm.dualNorm p h := by
      have hmem : inner ℝ h u ∈ ((fun y : E ↦ inner ℝ h y) '' p.closedBall 0 1) :=
        ⟨u, hu_ball, rfl⟩
      exact le_csSup (seminorm_dualNorm_bddAbove_innerImage_closedBall p h) hmem
    calc
      inner ℝ (g + h) u = inner ℝ g u + inner ℝ h u := by
        rw [inner_add_left]
      _ ≤ Seminorm.dualNorm p g + Seminorm.dualNorm p h := add_le_add hg_le hh_le

/-- Helper for Theorem 5.2.2: the Hessian at a fixed point induces the positive-definite bilinear
form underlying the Hessian dual local norm. -/
theorem hessian_bilin_posDef_of_isPositive_of_isInvertible
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    ((((innerSL ℝ).comp (hessian F x)).toBilinForm).toQuadraticMap).PosDef := by
  rw [QuadraticMap.posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · intro u
    change 0 ≤ inner ℝ (hessian F x u) u
    simpa [real_inner_comm] using hPos.inner_nonneg_right u
  · intro u hu
    change inner ℝ (hessian F x u) u = 0 at hu
    have hHu : hessian F x u = 0 := by
      obtain ⟨m, w, hA⟩ := (ContinuousLinearMap.isPositive_iff_eq_sum_rankOne).mp hPos
      rw [hA] at hu ⊢
      have hsum : ∑ j : Fin m, (inner ℝ (w j) u) ^ (2 : ℕ) = 0 := by
        simpa [Finset.sum_apply, InnerProductSpace.rankOne_apply, sum_inner, real_inner_smul_left,
          pow_two] using hu
      have hw : ∀ i : Fin m, inner ℝ (w i) u = 0 := by
        intro i
        exact sq_eq_zero_iff.mp <|
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ ↦ sq_nonneg (inner ℝ (w j) u))).mp hsum i (by simp)
      simp [Finset.sum_apply, InnerProductSpace.rankOne_apply, hw]
    apply hInv.injective
    simpa using hHu

/-- Helper for Theorem 5.2.2: at a fixed point, the determinant-based Hessian dual local norm is
subadditive on covectors. -/
theorem hessianDualLocalNorm_ofDetNeZero_add_le
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hH : (hessian F x).det ≠ 0) (g₁ g₂ : StrongDual ℝ E) :
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) ≤
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ +
        HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ := by
  let hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  let B : LinearMap.BilinForm ℝ E := ((innerSL ℝ).comp (hessian F x)).toBilinForm
  let hBPos : B.toQuadraticMap.PosDef :=
    hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv
  let p : Seminorm ℝ E := B.primalSeminorm hBPos
  let v₁ : E := (InnerProductSpace.toDual ℝ E).symm g₁
  let v₂ : E := (InnerProductSpace.toDual ℝ E).symm g₂
  have hBPos_eq :
      hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv = hBPos :=
    Subsingleton.elim _ _
  have hsum :
      Seminorm.dualNorm p (v₁ + v₂) ≤ Seminorm.dualNorm p v₁ + Seminorm.dualNorm p v₂ :=
    seminorm_dualNorm_add_le p v₁ v₂
  have hleft :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) =
        Seminorm.dualNorm p (v₁ + v₂) := by
    trans B.dualNorm hBPos ((g₁ + g₂).toLinearMap)
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv)
            ((g₁ + g₂).toLinearMap) =
          B.dualNorm hBPos ((g₁ + g₂).toLinearMap)
      rw [hBPos_eq]
    · symm
      simpa [p, v₁, v₂] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos (v₁ + v₂))
  have hg₁ :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ =
        Seminorm.dualNorm p v₁ := by
    trans B.dualNorm hBPos g₁.toLinearMap
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv) g₁.toLinearMap =
          B.dualNorm hBPos g₁.toLinearMap
      rw [hBPos_eq]
    · symm
      simpa [p, v₁] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos v₁)
  have hg₂ :
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ =
        Seminorm.dualNorm p v₂ := by
    trans B.dualNorm hBPos g₂.toLinearMap
    · simp [HessianDualLocalNorm.ofDetNeZero, dualLocalNorm, B]
      change
        B.dualNorm (hessian_bilin_posDef_of_isPositive_of_isInvertible hPos hInv) g₂.toLinearMap =
          B.dualNorm hBPos g₂.toLinearMap
      rw [hBPos_eq]
    · symm
      simpa [p, v₂] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hBPos v₂)
  calc
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (g₁ + g₂) =
        Seminorm.dualNorm p (v₁ + v₂) := hleft
    _ ≤ Seminorm.dualNorm p v₁ + Seminorm.dualNorm p v₂ := hsum
    _ = HessianDualLocalNorm.ofDetNeZero F x hPos hH g₁ +
          HessianDualLocalNorm.ofDetNeZero F x hPos hH g₂ := by
      rw [← hg₁, ← hg₂]

/-- Helper for Theorem 5.2.2: the fixed-point determinant-based Hessian dual local norm is even
on covectors. -/
theorem hessianDualLocalNorm_ofDetNeZero_neg
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hH : (hessian F x).det ≠ 0) (g : StrongDual ℝ E) :
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (-g) =
      HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
  -- Expanding both sides shows that the minus signs cancel inside the inverse-Hessian pairing.
  rw [HessianDualLocalNorm.ofDetNeZero_def, HessianDualLocalNorm.ofDetNeZero_def]
  simp

/-- Helper for Theorem 5.2.2: the fixed-point determinant-based Hessian dual local norm pulls out
absolute scalar factors from covectors. -/
theorem hessianDualLocalNorm_ofDetNeZero_smul
    {F : E → ℝ} {x : E} (hPos : (hessian F x).IsPositive)
    (hH : (hessian F x).det ≠ 0) (g : StrongDual ℝ E) (a : ℝ) :
    HessianDualLocalNorm.ofDetNeZero F x hPos hH (a • g) =
      |a| * HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
  let hInv : (hessian F x).IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  by_cases ha : 0 ≤ a
  · simpa [HessianDualLocalNorm.ofDetNeZero, smul_eq_mul, abs_of_nonneg ha] using
      dualLocalNorm_smul_nonneg F x hPos hInv g ha
  · have ha_lt : a < 0 := lt_of_not_ge ha
    have hneg_nonneg : 0 ≤ -a := by linarith
    calc
      HessianDualLocalNorm.ofDetNeZero F x hPos hH (a • g) =
          HessianDualLocalNorm.ofDetNeZero F x hPos hH ((-a : ℝ) • (-g)) := by
        simp
      _ = (-a) * HessianDualLocalNorm.ofDetNeZero F x hPos hH (-g) := by
        simpa [HessianDualLocalNorm.ofDetNeZero, smul_eq_mul] using
          dualLocalNorm_smul_nonneg F x hPos hInv (-g) hneg_nonneg
      _ = (-a) * HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
        rw [hessianDualLocalNorm_ofDetNeZero_neg hPos hH]
      _ = |a| * HessianDualLocalNorm.ofDetNeZero F x hPos hH g := by
        rw [abs_of_neg ha_lt]

/-- Helper for Theorem 5.2.2: the endpoint inverse-Hessian witness simultaneously realizes the
endpoint local norm and the squared endpoint dual norm of a covector. -/
theorem endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
    {x : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0) (k : E) :
    let H := hessian f x
    let w := H.inverse k
    ‖w‖[f; x] =
        HessianDualLocalNorm.ofDetNeZero f x
          ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx) hH
          (toDual ℝ E k) ∧
      inner ℝ k w =
        (HessianDualLocalNorm.ofDetNeZero f x
          ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx) hH
          (toDual ℝ E k)) ^ (2 : ℕ) := by
  let H := hessian f x
  let w := H.inverse k
  let hPos : H.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let hInv : H.IsInvertible := hessian_isInvertible_of_det_ne_zero hH
  have hHw : H w = k := by
    dsimp [H, w]
    exact hInv.self_apply_inverse k
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    calc
      0 ≤ inner ℝ w (H w) := hPos.inner_nonneg_right w
      _ = inner ℝ k w := by
        rw [hHw, real_inner_comm]
  refine ⟨?_, ?_⟩
  · rw [hessianLocalNorm_def, HessianDualLocalNorm.ofDetNeZero_def]
    have hinner : inner ℝ w (H w) = inner ℝ k w := by
      rw [hHw, real_inner_comm]
    simpa [H, w, InnerProductSpace.toDual_apply_apply] using congrArg Real.sqrt hinner
  · rw [HessianDualLocalNorm.ofDetNeZero_def]
    simpa [H, w, pow_two, real_inner_comm, InnerProductSpace.toDual_apply_apply] using
      (Real.sq_sqrt hpair_nonneg).symm

/-- Helper for Theorem 5.2.2: a symmetric operator bounded between `-c ∇²f(x)` and `c ∇²f(x)`
has determinant-based Hessian dual local norm at most `c * ‖u‖[f; x]` after acting on `u`. -/
theorem hessianDualLocalNorm_ofDetNeZero_le_of_operator_sandwich
    {x u : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (K : E →L[ℝ] E) {c : ℝ} (hc : 0 ≤ c) (hK_symm : K.IsSymmetric)
    (hlower : -(c • hessian f x) ≤ K) (hupper : K ≤ c • hessian f x) :
    HessianDualLocalNorm.ofDetNeZero f x
      ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx) hH
      (toDual ℝ E (K u)) ≤
        c * ‖u‖[f; x] := by
  let H : E →L[ℝ] E := hessian f x
  let k : E := K u
  let hPos : H.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let δ : ℝ := HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E k)
  let w : E := H.inverse k
  have hw_realize : ‖w‖[f; x] = δ ∧ inner ℝ k w = δ ^ (2 : ℕ) := by
    -- The inverse-Hessian witness at `x` realizes both the base dual norm and its square.
    simpa [H, w, k, δ] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := Mf) (f := f) (x := x) hx hH k
  have hw_norm : ‖w‖[f; x] = δ := hw_realize.1
  have hpair_sq : inner ℝ k w = δ ^ (2 : ℕ) := hw_realize.2
  have hδ_nonneg : 0 ≤ δ := by
    change 0 ≤ HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E k)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    rw [hpair_sq]
    positivity
  have hpair_bound :
      |inner ℝ w k| ≤ c * ‖w‖[f; x] * ‖u‖[f; x] := by
    -- Reduce the dual-norm estimate to the symmetric operator sandwich at the base point.
    simpa [H, k, real_inner_comm] using
      abs_inner_le_mul_localNorm_of_operator_sandwich
        (f := f) (x := x) (u := u) (v := w) hPos K hc hK_symm hlower hupper
  by_cases hδ_zero : δ = 0
  · have hfactor_nonneg : 0 ≤ c * ‖u‖[f; x] := by
      exact mul_nonneg hc (hessianLocalNorm_nonneg f x u)
    change δ ≤ c * ‖u‖[f; x]
    simpa [hδ_zero] using hfactor_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (by simpa [eq_comm] using hδ_zero)
    have hsq_bound : δ ^ (2 : ℕ) ≤ c * (δ * ‖u‖[f; x]) := by
      calc
        δ ^ (2 : ℕ) = inner ℝ k w := by
          symm
          exact hpair_sq
        _ = |inner ℝ k w| := by
          rw [abs_of_nonneg hpair_nonneg]
        _ = |inner ℝ w k| := by
          rw [real_inner_comm]
        _ ≤ c * ‖w‖[f; x] * ‖u‖[f; x] := hpair_bound
        _ = c * (δ * ‖u‖[f; x]) := by
          rw [hw_norm]
          ring
    -- Cancel the positive witness norm `δ` from the squared bound.
    nlinarith

/-- Helper for Theorem 5.2.2: a Loewner upper bound on Hessians yields the corresponding local
norm comparison after taking square roots. -/
theorem hessianLocalNorm_le_mul_of_loewner_upper
    {x y v : E} {c : ℝ} (hc : 0 ≤ c) (hcmp : hessian f y ≤ c • hessian f x) :
    ‖v‖[f; y] ≤ Real.sqrt c * ‖v‖[f; x] := by
  have hgap_pos :
      (c • hessian f x - hessian f y).IsPositive := by
    rw [← ContinuousLinearMap.le_def]
    exact hcmp
  have hinner_le :
      inner ℝ v (hessian f y v) ≤ c * inner ℝ v (hessian f x v) := by
    have hquad_gap :
        0 ≤ inner ℝ v ((c • hessian f x - hessian f y) v) :=
      hgap_pos.inner_nonneg_right v
    simpa [inner_sub_right, inner_smul_right] using hquad_gap
  rw [hessianLocalNorm_def, hessianLocalNorm_def]
  calc
    Real.sqrt (inner ℝ v (hessian f y v))
        ≤ Real.sqrt (c * inner ℝ v (hessian f x v)) := by
          exact Real.sqrt_le_sqrt hinner_le
    _ = Real.sqrt c * Real.sqrt (inner ℝ v (hessian f x v)) := by
          rw [Real.sqrt_mul hc]

/-- Helper for Theorem 5.2.2: a primal local-norm comparison from `x` to `y` reverses to the
same factor on determinant-based Hessian dual local norms. -/
theorem hessianDualLocalNorm_ofDetNeZero_le_of_localNorm_le_common
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) {c : ℝ} (hc : 0 ≤ c)
    (hnorm : ∀ z : E, ‖z‖[f; x] ≤ c * ‖z‖[f; y])
    (hHx : (hessian f x).det ≠ 0) (hHy : (hessian f y).det ≠ 0) (v : E) :
    HessianDualLocalNorm.ofDetNeZero f y
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy)
        hHy (toDual ℝ E v) ≤
      c * HessianDualLocalNorm.ofDetNeZero f x
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx)
        hHx (toDual ℝ E v) := by
  let hPosX : (hessian f x).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let hPosY : (hessian f y).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy
  let δx : ℝ := HessianDualLocalNorm.ofDetNeZero f x hPosX hHx (toDual ℝ E v)
  let δy : ℝ := HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E v)
  let Hy : E →L[ℝ] E := hessian f y
  let w : E := Hy.inverse v
  have hw_realize : ‖w‖[f; y] = δy ∧ inner ℝ v w = δy ^ (2 : ℕ) := by
    simpa [δy, Hy, w] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := Mf) (f := f) (x := y) hy hHy v
  have hw_norm : ‖w‖[f; y] = δy := hw_realize.1
  have hpair_sq : inner ℝ v w = δy ^ (2 : ℕ) := hw_realize.2
  have hδx_nonneg : 0 ≤ δx := by
    change
      0 ≤ HessianDualLocalNorm.ofDetNeZero f x hPosX hHx (toDual ℝ E v)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hδy_nonneg : 0 ≤ δy := by
    change
      0 ≤ HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E v)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hpair_bound : |inner ℝ v w| ≤ δx * ‖w‖[f; x] := by
    simpa [δx] using
      abs_toDual_apply_le_dualLocalNorm_mul_hessianLocalNorm
        (Mf := Mf) (f := f) (x := x) (v := v) (z := w) hx hHx
  have hw_transport : ‖w‖[f; x] ≤ c * δy := by
    simpa [hw_norm] using hnorm w
  have hpair_nonneg : 0 ≤ inner ℝ v w := by
    rw [hpair_sq]
    positivity
  have hsq_bound : δy ^ (2 : ℕ) ≤ δx * (c * δy) := by
    calc
      δy ^ (2 : ℕ) = inner ℝ v w := by symm; exact hpair_sq
      _ = |inner ℝ v w| := by rw [abs_of_nonneg hpair_nonneg]
      _ ≤ δx * ‖w‖[f; x] := hpair_bound
      _ ≤ δx * (c * δy) := by
            exact mul_le_mul_of_nonneg_left hw_transport hδx_nonneg
  by_cases hzero : δy = 0
  · change δy ≤ c * δx
    simpa [hzero] using mul_nonneg hc hδx_nonneg
  · have hδy_pos : 0 < δy := lt_of_le_of_ne hδy_nonneg (by simpa [eq_comm] using hzero)
    have hsq_bound' : δy ^ (2 : ℕ) ≤ c * δx * δy := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsq_bound
    nlinarith

/-- Helper for Theorem 5.2.2: transporting a determinant-based dual local norm from the base point
to an admissible endpoint costs exactly one factor `(1 - M_f ‖y - x‖[f; x])⁻¹`. -/
theorem dualLocalNorm_transport_to_endpoint
    {x y v : E} (hx : x ∈ dom) (hHx : (hessian f x).det ≠ 0)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) (hHy : (hessian f y).det ≠ 0) :
    HessianDualLocalNorm.ofDetNeZero f y
        ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive
          (IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset
            (domain := dom) (Mf := (Mf : NNReal)) (f := f) inferInstance hx hxy))
        hHy (toDual ℝ E v) ≤
      (1 / (1 - (Mf : ℝ) * ‖y - x‖[f; x])) *
        HessianDualLocalNorm.ofDetNeZero f x
          ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx)
          hHx (toDual ℝ E v) := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let hy : y ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hxy
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let c : ℝ := 1 / (1 - a)
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by positivity
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    by_contra hMf_not_pos
    have hMf_eq_zero : (Mf : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hMf_not_pos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [hMf_eq_zero] using hr_lt
    exact not_lt_of_ge (hessianLocalNorm_nonneg f x (y - x)) hr_neg
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hlower :
      ((1 - a) ^ (2 : ℕ)) • hessian f x ≤ hessian f y := by
    -- Specialize the exact segment-point Hessian comparison to the endpoint `τ = 1`.
    simpa [r, a] using
      (segment_point_hessian_bounds (hself := hself) (x := x) (y := y) hx hxy
        (τ := 1) (by constructor <;> norm_num)).1
  have hcmp : hessian f x ≤ (((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) • hessian f y := by
    have hscaled :
        ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) * (1 - a) ^ (2 : ℕ)) • hessian f x ≤
          (((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) • hessian f y := by
      simpa [smul_smul] using
        loewnerSmul_bridge hlower
          (c := (((1 - a) ^ (2 : ℕ))⁻¹ : ℝ)) (by positivity)
    have hone : ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) * (1 - a) ^ (2 : ℕ)) = 1 := by
      field_simp [pow_ne_zero 2 hfactor_pos.ne']
    simpa [hone] using hscaled
  have hsqrt : Real.sqrt ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ)) = c := by
    have hpow : ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ) = c ^ (2 : ℕ)) := by
      dsimp [c]
      field_simp [hfactor_pos.ne']
    rw [hpow]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc_nonneg]
  have hnorm : ∀ z : E, ‖z‖[f; x] ≤ c * ‖z‖[f; y] := by
    intro z
    calc
      ‖z‖[f; x] ≤ Real.sqrt ((((1 - a) ^ (2 : ℕ))⁻¹ : ℝ)) * ‖z‖[f; y] := by
        exact hessianLocalNorm_le_mul_of_loewner_upper
          (f := f) (x := y) (y := x) (v := z) (by positivity) hcmp
      _ = c * ‖z‖[f; y] := by
        rw [hsqrt]
  -- Convert the primal comparison into the reversed endpoint dual comparison via the generic
  -- determinant-based inverse-witness bridge.
  simpa [hy, r, a, c] using
    hessianDualLocalNorm_ofDetNeZero_le_of_localNorm_le_common
      (Mf := Mf) (f := f) (x := x) (y := y) hx hy hc_nonneg hnorm hHx hHy v

/-- Helper for Theorem 5.2.2: the averaged-Hessian residual along an admissible Dikin segment is
controlled by the factor `a / (1 - a)`, where `a = M_f ‖y - x‖_x`. -/
theorem average_hessian_residual_pairing_bound
    {x y u v : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    |inner ℝ v ((hessian f x - G) u)| ≤
      (a / (1 - a)) * ‖v‖[f; x] * ‖u‖[f; x] := by
  let hself : IsSelfConcordantOnWith dom (Mf : NNReal) f := inferInstance
  let hy : y ∈ dom := hself.openDikinEllipsoid_inv_constant_subset hx hxy
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
  let K : E →L[ℝ] E := H - G
  let c : ℝ := a / (1 - a)
  have hMf_pos : 0 < (Mf : ℝ) := by
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by positivity
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    by_contra hMf_not_pos
    have hMf_eq_zero : (Mf : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hMf_not_pos) hMf_nonneg
    have hr_neg : r < 0 := by
      simpa [hMf_eq_zero] using hr_lt
    exact not_lt_of_ge (hessianLocalNorm_nonneg f x (y - x)) hr_neg
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
  have hr_lt : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_lt_one : a < 1 := by
    dsimp [a]
    simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hfactor_pos : 0 < 1 - a := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hH_nonneg : 0 ≤ H := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive H).2 (hself.hessian_isPositive hx)
  have hG_lower :
      (1 - a + a ^ (2 : ℕ) / 3) • H ≤ G := by
    -- Rewrite the averaged-Hessian lower bound into the fixed `H/G/a` spelling.
    simpa [a, r, G, H, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      IsSelfConcordantOnWith.segmentAverageHessian_lower_bound
        (hself := hself) (x := x) (y := y) hx hxy
  have hG_upper : G ≤ (1 / (1 - a)) • H := by
    -- Rewrite the averaged-Hessian upper bound into the same normal form.
    simpa [a, r, G, H, mul_assoc, mul_left_comm, mul_comm] using
      IsSelfConcordantOnWith.segmentAverageHessian_upper_bound
        (hself := hself) (x := x) (y := y) hx hxy
  have hG_symm : G.IsSymmetric := by
    let d : E := y - x
    let Hτ : ℝ → E →L[ℝ] E := fun τ ↦ hessian f (x + τ • d)
    have hsegment_dom : segment ℝ x y ⊆ dom := hself.convex_domain.segment_subset hx hy
    have hHτ_maps : Set.MapsTo (fun τ : ℝ ↦ x + τ • d) (Set.Icc (0 : ℝ) 1) dom := by
      intro τ hτ
      exact hsegment_dom (segment_point_mem_segment (x := x) (y := y) hτ)
    have hHτ_cont : ContinuousOn Hτ (Set.Icc (0 : ℝ) 1) := by
      -- Restrict the continuous Hessian field to the affine segment used in the average.
      simpa [Hτ, d] using
        (hessian_continuousOn (dom := dom) (Mf := Mf) (f := f) hself).comp
          (show Continuous (fun τ : ℝ ↦ x + τ • d) by continuity).continuousOn
          hHτ_maps
    have hHτ_int : IntervalIntegrable Hτ MeasureTheory.volume 0 1 :=
      hHτ_cont.intervalIntegrable_of_Icc (by norm_num)
    have hHτ_apply_cont (w : E) : ContinuousOn (fun τ : ℝ ↦ Hτ τ w) (Set.Icc (0 : ℝ) 1) := by
      let ev : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E w
      simpa [Hτ, ev] using ev.continuous.comp_continuousOn hHτ_cont
    have hHτ_apply_int (w : E) :
        IntervalIntegrable (fun τ : ℝ ↦ Hτ τ w) MeasureTheory.volume 0 1 :=
      (hHτ_apply_cont w).intervalIntegrable_of_Icc (by norm_num)
    have hpair_integral (s t : E) :
        ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t) = inner ℝ s (G t) := by
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) s
      calc
        ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t)
            = ∫ τ in (0 : ℝ)..1, φ (Hτ τ t) := by
                refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
                intro τ
                simp [φ, Hτ, InnerProductSpace.toDual_apply_apply]
        _ = φ (∫ τ in (0 : ℝ)..1, Hτ τ t) := by
              exact ContinuousLinearMap.intervalIntegral_comp_comm (L := φ) (hHτ_apply_int t)
        _ = inner ℝ s (∫ τ in (0 : ℝ)..1, Hτ τ t) := by
              simp [φ, InnerProductSpace.toDual_apply_apply]
        _ = inner ℝ s (G t) := by
              rw [ContinuousLinearMap.intervalIntegral_apply hHτ_int t]
    intro s t
    calc
      inner ℝ (G s) t = inner ℝ t (G s) := real_inner_comm _ _
      _ = ∫ τ in (0 : ℝ)..1, inner ℝ t (Hτ τ s) := (hpair_integral t s).symm
      _ = ∫ τ in (0 : ℝ)..1, inner ℝ s (Hτ τ t) := by
            refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro τ hτ
            have hτIoc : τ ∈ Set.Ioc (0 : ℝ) 1 := by
              simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hτ
            have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := by
              exact ⟨le_of_lt hτIoc.1, hτIoc.2⟩
            have hz : x + τ • d ∈ dom := hHτ_maps hτ'
            have hzPos : (Hτ τ).IsPositive := by
              simpa [Hτ] using hself.hessian_isPositive hz
            simpa [Hτ, real_inner_comm] using hzPos.isSymmetric s t
      _ = inner ℝ s (G t) := hpair_integral s t
  have hK_symm : K.IsSymmetric := by
    exact hessianDifference_isSymmetricPairing (hself.hessian_isPositive hx).isSymmetric hG_symm
  have hlower : -(c • H) ≤ K := by
    -- The upper averaged-Hessian bound supplies the negative side of the symmetric sandwich.
    have hsum : H + c • H = (1 / (1 - a)) • H := by
      have hscalar : (1 : ℝ) + c = 1 / (1 - a) := by
        dsimp [c]
        field_simp [hfactor_pos.ne']
        ring
      calc
        H + c • H = ((1 : ℝ) + c) • H := by
          rw [add_smul, one_smul]
        _ = (1 / (1 - a)) • H := by
          rw [hscalar]
    have hmain : G ≤ H + c • H := by
      rw [hsum]
      exact hG_upper
    rw [ContinuousLinearMap.le_def]
    have hmain' : ((H + c • H) - G).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hmain
    simpa [K, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain'
  have hupper : K ≤ c • H := by
    -- The lower averaged-Hessian bound controls the positive side after one scalar comparison.
    have hscalar_le : (1 : ℝ) ≤ (1 - a + a ^ (2 : ℕ) / 3) + c := by
      dsimp [c]
      field_simp [hfactor_pos.ne']
      nlinarith [ha_nonneg, ha_lt_one]
    have hstep1 :
        (1 : ℝ) • H ≤ ((1 - a + a ^ (2 : ℕ) / 3) + c) • H := by
      exact loewnerSmul_mono_of_nonneg hH_nonneg hscalar_le
    have hstep2 :
        ((1 - a + a ^ (2 : ℕ) / 3) + c) • H =
          (1 - a + a ^ (2 : ℕ) / 3) • H + c • H := by
      rw [add_smul]
    have hstep3 :
        (1 - a + a ^ (2 : ℕ) / 3) • H + c • H ≤ G + c • H := by
      exact loewnerAddRight_bridge hG_lower
    have hmain : H ≤ G + c • H := by
      calc
      H = (1 : ℝ) • H := by simp
      _ ≤ ((1 - a + a ^ (2 : ℕ) / 3) + c) • H := hstep1
      _ = (1 - a + a ^ (2 : ℕ) / 3) • H + c • H := hstep2
      _ ≤ G + c • H := hstep3
    rw [ContinuousLinearMap.le_def]
    have hmain' : (G + c • H - H).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hmain
    simpa [K, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain'
  -- Route correction: the standard branch should close from the averaged-Hessian Loewner
  -- sandwich alone, without reopening the endpoint-witness transport route.
  simpa [a, r, G, H, K, c] using
    abs_inner_le_mul_localNorm_of_operator_sandwich
      (f := f) (x := x) (u := u) (v := v) (hself.hessian_isPositive hx)
      K hc_nonneg hK_symm hlower hupper

/-- Helper for Theorem 5.2.2: the averaged-Hessian residual is bounded in the base dual local
norm by the sharp factor `a / (1 - a)` times the base local norm of the test vector. -/
theorem average_hessian_residual_baseDualBound
    {x y u : E} (hx : x ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let a := (Mf : ℝ) * r
    let H := hessian f x
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    HessianDualLocalNorm.ofDetNeZero f x
      ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx) hH
      (toDual ℝ E ((H - G) u)) ≤
        (a / (1 - a)) * ‖u‖[f; x] := by
  let r : ℝ := ‖y - x‖[f; x]
  let a : ℝ := (Mf : ℝ) * r
  let H : E →L[ℝ] E := hessian f x
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
  let k : E := (H - G) u
  let hPos : H.IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let δ : ℝ := HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E k)
  let w : E := H.inverse k
  have hw_realize : ‖w‖[f; x] = δ ∧ inner ℝ k w = δ ^ (2 : ℕ) := by
    -- The inverse-Hessian witness at `x` realizes both the base dual norm and its square.
    simpa [H, w, k, δ] using
      endpoint_inverse_residual_witness_localNorm_eq_dual_and_pairing_ofDetNeZero
        (Mf := Mf) (f := f) (x := x) hx hH k
  have hw_norm : ‖w‖[f; x] = δ := hw_realize.1
  have hpair_sq : inner ℝ k w = δ ^ (2 : ℕ) := hw_realize.2
  have hδ_nonneg : 0 ≤ δ := by
    change 0 ≤ HessianDualLocalNorm.ofDetNeZero f x hPos hH (toDual ℝ E k)
    rw [HessianDualLocalNorm.ofDetNeZero_def]
    exact Real.sqrt_nonneg _
  have hpair_nonneg : 0 ≤ inner ℝ k w := by
    rw [hpair_sq]
    positivity
  have hpair_bound :
      |inner ℝ w k| ≤ (a / (1 - a)) * ‖w‖[f; x] * ‖u‖[f; x] := by
    -- Apply the averaged-Hessian residual pairing estimate to the inverse-Hessian witness `w`.
    simpa [H, G, k, real_inner_comm] using
      average_hessian_residual_pairing_bound
        (Mf := Mf) (f := f) (x := x) (y := y) (u := u) (v := w) hx hxy
  by_cases hδ_zero : δ = 0
  · -- If the base dual norm vanishes, the desired bound is immediate.
    have hr_lt : r < 1 / (Mf : ℝ) := by
      simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
    have hMf_nonneg : 0 ≤ (Mf : ℝ) := by positivity
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      exact mul_nonneg hMf_nonneg (hessianLocalNorm_nonneg f x (y - x))
    have ha_lt_one : a < 1 := by
      by_cases hMf_zero : (Mf : ℝ) = 0
      · simp [a, hMf_zero]
      · have hMf_pos : 0 < (Mf : ℝ) :=
          lt_of_le_of_ne hMf_nonneg (by simpa [eq_comm] using hMf_zero)
        dsimp [a]
        simpa [r, mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
    have hfactor_nonneg : 0 ≤ (a / (1 - a)) * ‖u‖[f; x] := by
      have hden_pos : 0 < 1 - a := by
        linarith
      have hratio_nonneg : 0 ≤ a / (1 - a) := by
        exact div_nonneg ha_nonneg (le_of_lt hden_pos)
      exact mul_nonneg hratio_nonneg (hessianLocalNorm_nonneg f x u)
    change δ ≤ (a / (1 - a)) * ‖u‖[f; x]
    simpa [hδ_zero] using hfactor_nonneg
  · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (by simpa [eq_comm] using hδ_zero)
    have hsq_bound : δ ^ (2 : ℕ) ≤ (a / (1 - a)) * (δ * ‖u‖[f; x]) := by
      calc
        δ ^ (2 : ℕ) = inner ℝ k w := by symm; exact hpair_sq
        _ = |inner ℝ k w| := by rw [abs_of_nonneg hpair_nonneg]
        _ = |inner ℝ w k| := by rw [real_inner_comm]
        _ ≤ (a / (1 - a)) * ‖w‖[f; x] * ‖u‖[f; x] := hpair_bound
        _ = (a / (1 - a)) * (δ * ‖u‖[f; x]) := by rw [hw_norm]; ring
    -- Cancel the positive witness norm `δ` from the squared bound.
    nlinarith

/-- Helper for Theorem 5.2.2: nonnegative scalar combinations are bounded by the corresponding
weighted sum in a fixed endpoint metric. -/
theorem hessianDualLocalNorm_ofDetNeZero_nonneg_smul_add_le
    {x : E} (hPos : (hessian f x).IsPositive) (hH : (hessian f x).det ≠ 0)
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (φ ψ : StrongDual ℝ E) :
    HessianDualLocalNorm.ofDetNeZero f x hPos hH (β • φ + γ • ψ) ≤
      β * HessianDualLocalNorm.ofDetNeZero f x hPos hH φ +
        γ * HessianDualLocalNorm.ofDetNeZero f x hPos hH ψ := by
  -- Separate the two nonnegative scalar factors and use the fixed-point triangle inequality.
  calc
    HessianDualLocalNorm.ofDetNeZero f x hPos hH (β • φ + γ • ψ) ≤
        HessianDualLocalNorm.ofDetNeZero f x hPos hH (β • φ) +
          HessianDualLocalNorm.ofDetNeZero f x hPos hH (γ • ψ) := by
      exact hessianDualLocalNorm_ofDetNeZero_add_le hPos hH _ _
    _ = β * HessianDualLocalNorm.ofDetNeZero f x hPos hH φ +
          γ * HessianDualLocalNorm.ofDetNeZero f x hPos hH ψ := by
      rw [hessianDualLocalNorm_ofDetNeZero_smul hPos hH φ β,
        hessianDualLocalNorm_ofDetNeZero_smul hPos hH ψ γ, abs_of_nonneg hβ,
        abs_of_nonneg hγ]

/-- Helper for Theorem 5.2.2: transporting the old gradient from the base point to an admissible
endpoint gives the sharp factor `(1 - a)⁻¹`. -/
theorem oldGradientEndpointDualBound
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hxy : y ∈ W⁰[f; x](1 / ((Mf : NNReal) : ℝ))) (hHy : (hessian f y).det ≠ 0)
    {a : ℝ} (ha : a = (Mf : ℝ) * ‖y - x‖[f; x]) :
    HessianDualLocalNorm.ofDetNeZero f y
      ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy)
      hHy (toDual ℝ E (∇ f x)) ≤
        (1 / (1 - a)) * ndec(f, x, (Mf : NNReal), hx, hH) := by
  let hPosY : (hessian f y).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy
  -- Transport the old gradient to the endpoint metric once, then rewrite the base dual norm as
  -- the old Newton decrement.
  calc
    HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f x)) ≤
          (1 / (1 - (Mf : ℝ) * ‖y - x‖[f; x])) *
            HessianDualLocalNorm.ofDetNeZero f x
              ((inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx)
              hH (toDual ℝ E (∇ f x)) := by
      simpa [hPosY] using
        dualLocalNorm_transport_to_endpoint
          (Mf := Mf) (f := f) (x := x) (y := y) (v := ∇ f x) hx hH hxy hHy
    _ = (1 / (1 - a)) * ndec(f, x, (Mf : NNReal), hx, hH) := by
      simpa [ha, NewtonDecrement.ofDetNeZero_def]

/-- Helper for Theorem 5.2.2: the shared positive-variant endpoint assembly combines the
transported endpoint gradient with the base-operator sandwich for `∇²f(x) - α G`. -/
theorem positiveVariantEndpointAssemblyBound
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) (hH : (hessian f x).det ≠ 0)
    (hHy : (hessian f y).det ≠ 0)
    (hxy : y ∈ W⁰[f; x](1 / ((Mf : NNReal) : ℝ))) {α a : ℝ}
    (hα_nonneg : 0 ≤ α) (h1mα_nonneg : 0 ≤ 1 - α)
    (ha : a = (Mf : ℝ) * ‖y - x‖[f; x])
    (hlowerCoeff : α / (1 - a) - 1 ≤ (1 - α) + α * a)
    (hgrad :
      let H := hessian f x
      let u := H.inverse (∇ f x)
      let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
      ∇ f y = (H - α • G) u) :
    ndec(f, y, (Mf : NNReal), hy, hHy) ≤
      (((1 - α) / (1 - a)) + α * (a / (1 - a))) *
        ndec(f, x, (Mf : NNReal), hx, hH) := by
  let H : E →L[ℝ] E := hessian f x
  let u : E := H.inverse (∇ f x)
  let G : E →L[ℝ] E := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
  let K : E →L[ℝ] E := H - α • G
  let δ : ℝ := ndec(f, x, (Mf : NNReal), hx, hH)
  let c : ℝ := (1 - α) + α * a
  let hPosX : (hessian f x).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hx
  let hPosY : (hessian f y).IsPositive :=
    (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f).hessian_isPositive hy
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero Mf))
  have hr_lt : ‖y - x‖[f; x] < 1 / (Mf : ℝ) := by
    simpa using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have ha_nonneg : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg (by positivity : 0 ≤ (Mf : ℝ)) (hessianLocalNorm_nonneg f x (y - x))
  have ha_lt_one : a < 1 := by
    rw [ha]
    simpa [mul_comm] using (lt_div_iff₀ hMf_pos).1 hr_lt
  have hden_pos : 0 < 1 - a := by
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    nlinarith
  have hH_nonneg : 0 ≤ H := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive H).2 hPosX
  have hu_norm : ‖u‖[f; x] = δ := by
    -- Rewrite the Newton-direction local norm once so the operator bound lands directly in `δ`.
    simpa [H, u, δ] using
      inverseNewtonDirectionLocalNorm_eq_ndec
        (dom := dom) (Mf := Mf) (f := f) (x := x) hx hH
  have hG_lower :
      (1 - a + a ^ (2 : ℕ) / 3) • H ≤ G := by
    simpa [ha, H, G, pow_two, mul_assoc, mul_left_comm, mul_comm] using
      IsSelfConcordantOnWith.segmentAverageHessian_lower_bound
        (hself := (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f))
        (x := x) (y := y) hx hxy
  have hG_upper : G ≤ (1 / (1 - a)) • H := by
    simpa [ha, H, G, mul_assoc, mul_left_comm, mul_comm] using
      IsSelfConcordantOnWith.segmentAverageHessian_upper_bound
        (hself := (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f))
        (x := x) (y := y) hx hxy
  have hG_symm : G.IsSymmetric := by
    simpa [G] using
      segmentAverageHessian_isSymmetric
        (hself := (inferInstance : IsSelfConcordantOnWith dom (Mf : NNReal) f))
        (x := x) (y := y) hx hy
  have hK_symm : K.IsSymmetric := by
    have hαG_symm : (α • G).IsSymmetric := by
      simpa using hG_symm.smul (show star α = α by simp)
    exact hessianDifference_isSymmetricPairing hPosX.isSymmetric hαG_symm
  have hαG_upper :
      α • G ≤ (α / (1 - a)) • H := by
    calc
      α • G ≤ α • ((1 / (1 - a)) • H) := by
        exact loewnerSmul_bridge hG_upper hα_nonneg
      _ = (α / (1 - a)) • H := by
        rw [smul_smul]
        ring
  have hscalar_lower : α / (1 - a) ≤ 1 + c := by
    dsimp [c]
    nlinarith [hlowerCoeff]
  have hlower_step : α • G ≤ (1 + c) • H := by
    exact le_trans hαG_upper (loewnerSmul_mono_of_nonneg hH_nonneg hscalar_lower)
  have hlower : -(c • H) ≤ K := by
    rw [ContinuousLinearMap.le_def]
    have hmain : (((1 + c) • H) - α • G).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hlower_step
    simpa [K, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul, one_smul] using
      hmain
  have hαG_lower :
      (α * (1 - a + a ^ (2 : ℕ) / 3)) • H ≤ α • G := by
    have htmp : α • ((1 - a + a ^ (2 : ℕ) / 3) • H) ≤ α • G := by
      exact loewnerSmul_bridge hG_lower hα_nonneg
    simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hscalar_upper : 1 ≤ α * (1 - a + a ^ (2 : ℕ) / 3) + c := by
    dsimp [c]
    nlinarith [hα_nonneg, ha_nonneg]
  have hupper_step : H ≤ α • G + c • H := by
    calc
      H = (1 : ℝ) • H := by simp
      _ ≤ (α * (1 - a + a ^ (2 : ℕ) / 3) + c) • H := by
        exact loewnerSmul_mono_of_nonneg hH_nonneg hscalar_upper
      _ = (α * (1 - a + a ^ (2 : ℕ) / 3)) • H + c • H := by
        rw [add_smul]
      _ ≤ α • G + c • H := by
        exact loewnerAddRight_bridge hαG_lower
  have hupper : K ≤ c • H := by
    rw [ContinuousLinearMap.le_def]
    have hmain : (α • G + c • H - H).IsPositive := by
      rw [← ContinuousLinearMap.le_def]
      exact hupper_step
    simpa [K, c, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmain
  have hbase_raw :
      HessianDualLocalNorm.ofDetNeZero f x hPosX hH (toDual ℝ E (K u)) ≤ c * ‖u‖[f; x] := by
    simpa [H, K] using
      hessianDualLocalNorm_ofDetNeZero_le_of_operator_sandwich
        (Mf := Mf) (f := f) (x := x) (u := u) hx hH K hc_nonneg hK_symm hlower hupper
  have hgrad' : ∇ f y = K u := by
    simpa [H, u, G, K] using hgrad
  have hbase :
      HessianDualLocalNorm.ofDetNeZero f x hPosX hH (toDual ℝ E (∇ f y)) ≤ c * δ := by
    calc
      HessianDualLocalNorm.ofDetNeZero f x hPosX hH (toDual ℝ E (∇ f y))
          = HessianDualLocalNorm.ofDetNeZero f x hPosX hH (toDual ℝ E (K u)) := by
              rw [hgrad']
      _ ≤ c * ‖u‖[f; x] := hbase_raw
      _ = c * δ := by rw [hu_norm]
  have htransport :
      HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f y)) ≤
        (1 / (1 - a)) *
          HessianDualLocalNorm.ofDetNeZero f x hPosX hH (toDual ℝ E (∇ f y)) := by
    simpa [hPosY, ha] using
      dualLocalNorm_transport_to_endpoint
        (Mf := Mf) (f := f) (x := x) (y := y) (v := ∇ f y) hx hH hxy hHy
  have hndec :
      ndec(f, y, (Mf : NNReal), hy, hHy) =
        HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f y)) := by
    rw [NewtonDecrement.ofDetNeZero_def, HessianDualLocalNorm.ofDetNeZero_def]
    simp [InnerProductSpace.toDual_apply_apply]
  -- Transport the endpoint gradient once, then control its base dual norm by the symmetric
  -- operator sandwich for `H - α G`.
  calc
    ndec(f, y, (Mf : NNReal), hy, hHy) =
        HessianDualLocalNorm.ofDetNeZero f y hPosY hHy (toDual ℝ E (∇ f y)) := hndec
    _ ≤ (1 / (1 - a)) *
          HessianDualLocalNorm.ofDetNeZero f x hPosX hH (toDual ℝ E (∇ f y)) := htransport
    _ ≤ (1 / (1 - a)) * (c * δ) := by
          exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (((1 - α) / (1 - a)) + α * (a / (1 - a))) * δ := by
          dsimp [c]
          field_simp [hden_pos.ne']

end SourceFaithfulPublicAPI

end
