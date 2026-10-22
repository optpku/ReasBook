/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_0_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

/- Theorem 5.1.8 lies in the Chapter 5 self-concordant Hessian-comparison domain.

Sampled owner declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `hessian_loewner_bounds_along_segment` from `Theorem_5_1_7`, the segment-local Hessian
  comparison theorem stated directly in Loewner order;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` from
  `Proposition_5_0_15`, the bundled-owner Dikin-ellipsoid version of the same owner-level
  comparison.

Source/core/bridge triage:
* source-facing: the gradient-pairing and lower Taylor bounds between two fixed points;
* core/canonical: the Loewner-order comparison on `hessian f _`;
* bridge/view: the scalar local norm `‖y - x‖[f; x]` appearing only in the comparison factor and
  in the final bound.

Primitive data:
* a `C²` function on an open set containing the segment from `x` to `y`;
* positivity of the base Hessian `hessian f x`, so the Chapter 5 local norm at `x` is a genuine
  Hessian norm;
* a lower Loewner-order comparison of the Hessian along that segment.

Derived API:
* the lower bound for the gradient pairing;
* the affine lower Taylor bound with remainder `ω`.

This file stays source-facing, but its primitive Hessian hypothesis now uses the owner
`hessian f _` directly instead of the derived scalarized quadratic-form surface. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
variable (hcont : ContDiffOn ℝ 2 f dom)
variable (hsegment : segment ℝ x y ⊆ dom)
variable (hopen : IsOpen dom)
variable (hHessPos : (hessian f x).IsPositive)
variable
  (hloewnerLower :
    ∀ ⦃z : E⦄, z ∈ segment ℝ x y →
      (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) • hessian f x ≤ hessian f z)

include hcont hsegment hopen hHessPos hloewnerLower

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: once the Hessian quadratic form is nonnegative, squaring the local
norm recovers that quadratic form exactly. -/
private theorem sqHessianLocalNormEqInnerOfNonneg
    {f : E → ℝ} {z u : E} (hquad : 0 ≤ inner ℝ u (hessian f z u)) :
    ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (hessian f z u) := by
  -- Expand the local norm and use the standard `sqrt(x)^2 = x` identity.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: nonnegative scalar dilations scale the Hessian local norm by the
same scalar at a positive base Hessian. -/
private theorem hessianLocalNormSmulOfNonneg
    {f : E → ℝ} {z u : E} (hzPos : (hessian f z).IsPositive)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[f; z] = τ * ‖u‖[f; z] := by
  have hquad : 0 ≤ inner ℝ u (hessian f z u) := hzPos.inner_nonneg_right u
  -- Reduce to the scalar identity `sqrt (τ² q) = τ sqrt q` with `q ≥ 0`.
  calc
    ‖τ • u‖[f; z] = Real.sqrt ((τ * τ) * inner ℝ u (hessian f z u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f z u)) * Real.sqrt (τ * τ) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = τ * ‖u‖[f; z] := by
      rw [show τ * τ = τ ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ,
        hessianLocalNorm_def]
      ring

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: affine lines have the expected derivative. -/
private theorem lineHasDerivAt
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: every affine parameter `t ∈ [0,1]` lands back on the segment
between `x` and `y`. -/
private theorem segmentPoint_memSegment
    {x y : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ segment ℝ x y := by
  -- Rewrite the affine point into the canonical line-map description of the segment.
  rw [segment_eq_image_lineMap]
  refine ⟨t, ht, ?_⟩
  simp [AffineMap.lineMap_apply_module', add_comm]

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: a `C²` function on an open set has a continuous Hessian owner. -/
private theorem hessianContinuousOnOfContDiffOnTwo
    {dom : Set E} {f : E → ℝ} (hcont : ContDiffOn ℝ 2 f dom) (hopen : IsOpen dom) :
    ContinuousOn (hessian f) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ f) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) dom :=
      hcont.fderiv_of_isOpen hopen (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  -- Differentiate the gradient owner once more to identify the Hessian owner.
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen hopen (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: a pointwise `C²` hypothesis makes the gradient differentiable at
that point. -/
private theorem differentiableAtGradientOfContDiffAtTwo
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) :
    DifferentiableAt ℝ (∇ f) z := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) z := by
    -- A `C²` field has a differentiable first derivative.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule applies directly.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) z
  exact (D.hasFDerivAt.comp z hfdiff.hasFDerivAt).differentiableAt

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: differentiating `f` along an admissible affine line recovers the
gradient pairing with the line direction. -/
private theorem valueLineHasDerivAtOfContDiffOn
    {dom : Set E} {f : E → ℝ}
    (hcont : ContDiffOn ℝ 2 f dom) (hopen : IsOpen dom)
    {z d : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ f (z + s • d)) (inner ℝ (∇ f (z + t • d)) d) t := by
  have hC1 : ContDiffAt ℝ 1 f (z + t • d) := by
    exact
      (hcont.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt
        (hopen.mem_nhds hzt)
  -- Differentiate the ambient function first and then compose with the affine line.
  simpa using
    ((hC1.differentiableAt one_ne_zero).hasGradientAt.hasFDerivAt.comp t
      (lineHasDerivAt z d t).hasFDerivAt).hasDerivAt

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: scalarizing the gradient along an admissible affine line
differentiates to the corresponding Hessian pairing. -/
private theorem scalarizedGradientLineHasDerivAtOfContDiffOn
    {dom : Set E} {f : E → ℝ}
    (hcont : ContDiffOn ℝ 2 f dom) (hopen : IsOpen dom)
    {z d w : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (z + s • d)) w)
      (inner ℝ (hessian f (z + t • d) d) w) t := by
  have hz_C2 : ContDiffAt ℝ 2 f (z + t • d) := by
    exact hcont.contDiffAt (hopen.mem_nhds hzt)
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (z + s • d))
        ((hessian f (z + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Differentiate the raw gradient line before scalarizing it.
    simpa using
      ((differentiableAtGradientOfContDiffAtTwo hz_C2).hasFDerivAt.comp t
        (lineHasDerivAt z d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (z + s • d)))
        (φ.comp ((hessian f (z + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the fixed scalar functional `v ↦ ⟪v, w⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: the rational lower integrand has the expected antiderivative. -/
private theorem integralSqDivEqScaledSqDivAdd
    {a r u : ℝ} (hu : 0 ≤ u)
    (hden : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 + t * a) :
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) =
      u * r ^ (2 : ℕ) / (1 + u * a) := by
  have hnum :
      ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * a)) (Set.Icc (0 : ℝ) u) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 + t * a) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
        MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) u) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 + t * a) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) u := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 + t * a ≠ 0 := (hden t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 + s * a) a t := by
      convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot :=
      ((hasDerivAt_id t).mul_const (r ^ (2 : ℕ))).div hden_deriv hden_ne
    have hslope :
        ((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * a) - t * r ^ (2 : ℕ) * a) /
            (1 + t * a) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * a) - t * r ^ (2 : ℕ) * a) /
            (1 + t * a) ^ (2 : ℕ))
          t := by
      simpa using hquot
    exact hquot'.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hnum hderiv hint
  calc
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)
        = u * r ^ (2 : ℕ) / (1 + u * a) - (0 * r ^ (2 : ℕ) / (1 + 0 * a)) := by
            simpa using hftc
    _ = u * r ^ (2 : ℕ) / (1 + u * a) := by ring

omit hcont hsegment hopen hHessPos hloewnerLower in
/-- Helper for Theorem 5 1 8: the second scalar integration in the lower Taylor bound evaluates
to the Chapter 5 auxiliary function `ω`. -/
private theorem integralMulSqDivEqOmegaAux
    {Mf : NNReal} {r : ℝ} (hr0 : 0 ≤ r) (hMf_pos : 0 < (Mf : ℝ)) :
    let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr0)
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) =
      (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω tω := by
  let a : ℝ := (Mf : ℝ)
  have ha_ne : a ≠ 0 := ne_of_gt (by simpa [a] using hMf_pos)
  have hnum :
      ContinuousOn
        (fun t : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (a * t * r - Real.log (1 + a * t * r)))
        (Set.Icc (0 : ℝ) 1) := by
    have hlog :
        ContinuousOn (fun t : ℝ ↦ Real.log (1 + a * t * r)) (Set.Icc (0 : ℝ) 1) := by
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + a * t * r) by continuity).continuousOn
      · intro t ht
        have harg_pos : 0 < 1 + a * t * r := by
          have hmul_nonneg : 0 ≤ a * t * r := by
            exact mul_nonneg (mul_nonneg hMf_pos.le ht.1) hr0
          linarith
        exact harg_pos.ne'
    have hlin :
        ContinuousOn (fun t : ℝ ↦ a * t * r) (Set.Icc (0 : ℝ) 1) := by
      exact (show Continuous (fun t : ℝ ↦ a * t * r) by continuity).continuousOn
    -- Keep the antiderivative in the exact scalar form feeding `ω`.
    refine continuousOn_const.mul ?_
    exact hlin.sub hlog
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + a * t * r))
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + a * t * r))
          (Set.Icc (0 : ℝ) 1) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + a * t * r) by continuity).continuousOn
      · intro t ht
        have harg_pos : 0 < 1 + a * t * r := by
          have hmul_nonneg : 0 ≤ a * t * r := by
            exact mul_nonneg (mul_nonneg hMf_pos.le ht.1) hr0
          linarith
        exact harg_pos.ne'
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun s : ℝ ↦
            (1 / (a ^ (2 : ℕ))) * (a * s * r - Real.log (1 + a * s * r)))
          (t * r ^ (2 : ℕ) / (1 + a * t * r)) t := by
    intro t ht
    have harg_ne : 1 + a * t * r ≠ 0 := by
      have harg_pos : 0 < 1 + a * t * r := by
        have hmul_nonneg : 0 ≤ a * t * r := by
          exact mul_nonneg (mul_nonneg hMf_pos.le ht.1.le) hr0
        linarith
      exact harg_pos.ne'
    have harg :
        HasDerivAt (fun s : ℝ ↦ 1 + a * s * r) (a * r) t := by
      convert
        (hasDerivAt_const t (1 : ℝ)).add ((((hasDerivAt_id t).const_mul a).mul_const r)) using 1
      ring
    have hlog :
        HasDerivAt (fun s : ℝ ↦ Real.log (1 + a * s * r))
          ((a * r) / (1 + a * t * r)) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_log harg_ne).comp t harg
    have hlin :
        HasDerivAt (fun s : ℝ ↦ a * s * r) (a * r) t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((((hasDerivAt_id t).const_mul a).mul_const r))
    have hbase :
        HasDerivAt
          (fun s : ℝ ↦ a * s * r - Real.log (1 + a * s * r))
          (a * r - ((a * r) / (1 + a * t * r))) t := by
      -- Differentiate the linear and logarithmic pieces separately before recombining them.
      exact hlin.sub hlog
    have hscaled :
        HasDerivAt
          (fun s : ℝ ↦
            (1 / (a ^ (2 : ℕ))) * (a * s * r - Real.log (1 + a * s * r)))
          ((1 / (a ^ (2 : ℕ))) * (a * r - ((a * r) / (1 + a * t * r)))) t := by
      exact hbase.const_mul (1 / (a ^ (2 : ℕ)))
    have hslope :
        ((1 / (a ^ (2 : ℕ))) * (a * r - ((a * r) / (1 + a * t * r)))) =
          t * r ^ (2 : ℕ) / (1 + a * t * r) := by
      have hfrac :
          1 - (1 + a * t * r)⁻¹ = (a * t * r) * (1 + a * t * r)⁻¹ := by
        field_simp [harg_ne]
        ring
      calc
        ((1 / (a ^ (2 : ℕ))) * (a * r - ((a * r) / (1 + a * t * r))))
            = (1 / (a ^ (2 : ℕ))) * (a * r) * (1 - (1 + a * t * r)⁻¹) := by
                ring_nf
        _ = (1 / (a ^ (2 : ℕ))) * (a * r) * ((a * t * r) * (1 + a * t * r)⁻¹) := by
              rw [hfrac]
        _ = t * r ^ (2 : ℕ) / (1 + a * t * r) := by
              field_simp [ha_ne, harg_ne]
    exact hscaled.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show (0 : ℝ) ≤ 1 by norm_num) hnum hderiv hint
  calc
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r)
        =
          ((1 / (a ^ (2 : ℕ))) * (a * 1 * r - Real.log (1 + a * 1 * r))) -
            ((1 / (a ^ (2 : ℕ))) * (a * 0 * r - Real.log (1 + a * 0 * r))) := by
              simpa [a, mul_assoc, mul_left_comm, mul_comm] using hftc
    _ = (1 / (a ^ (2 : ℕ))) * (a * r - Real.log (1 + a * r)) := by
      simp
    _ = (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
          ω (selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr0)) := by
      rw [selfConcordantOmega_apply]
      simp [a, mul_comm]

/-- Helper for Theorem 5 1 8: along the segment, the gradient increment paired with the chord is
bounded below by the textbook transport factor. -/
private theorem segmentGradientIncrementLowerBoundOfLoewnerLower
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    let d := y - x
    let r := ‖d‖[f; x]
    inner ℝ (∇ f (x + α • d) - ∇ f x) d ≥
      α * r ^ (2 : ℕ) / (1 + α * (Mf : ℝ) * r) := by
  let d : E := y - x
  let r : ℝ := ‖d‖[f; x]
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • d)) d
  have hr0 : 0 ≤ r := by
    simpa [r, d] using hessianLocalNorm_nonneg f x d
  have hline_mem :
      ∀ t ∈ Set.Icc (0 : ℝ) α, x + t • d ∈ dom := by
    intro t ht
    exact hsegment (segmentPoint_memSegment (x := x) (y := y) ⟨ht.1, le_trans ht.2 hα1⟩)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) α) := by
    intro t ht
    have hderiv_t :
        HasDerivAt g (inner ℝ d (hessian f (x + t • d) d)) t := by
      simpa [g, real_inner_comm] using
        scalarizedGradientLineHasDerivAtOfContDiffOn hcont hopen (hline_mem t ht)
    -- A differentiable scalarized gradient line is continuous at the same parameter.
    exact hderiv_t.continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) α,
        HasDerivAt g (inner ℝ d (hessian f (x + t • d) d)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) α := Set.mem_Icc_of_Ioo ht
    simpa [g, real_inner_comm] using
      scalarizedGradientLineHasDerivAtOfContDiffOn hcont hopen (hline_mem t ht')
  have hderiv_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ d (hessian f (x + t • d) d))
        MeasureTheory.volume 0 α := by
    have hcont_line :
        ContinuousOn
          (fun t : ℝ ↦ inner ℝ d (hessian f (x + t • d) d))
          (Set.Icc (0 : ℝ) α) := by
      intro t ht
      have hhess_cont : ContinuousAt (hessian f) (x + t • d) :=
        (hessianContinuousOnOfContDiffOnTwo hcont hopen).continuousAt
          (hopen.mem_nhds (hline_mem t ht))
      have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • d) t := by
        simpa using
          (continuousAt_const.add (continuousAt_id.smul continuousAt_const) :
            ContinuousAt (fun s : ℝ ↦ x + s • d) t)
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • d)) t := by
        exact ContinuousAt.comp hhess_cont hline_cont
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) d
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • d) d) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E d).continuous.continuousAt) hhess_line
      have hinner_cont :
          ContinuousAt (fun s : ℝ ↦ inner ℝ d (hessian f (x + s • d) d)) t := by
        simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φ.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont_line.intervalIntegrable_of_Icc hα0
  have hint_lower :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
        MeasureTheory.volume 0 α := by
    have hcont_lower :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) α) := by
      refine continuousOn_const.div ?_ ?_
      · exact
          (show Continuous (fun t : ℝ ↦ (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
          exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr0)
        have : 0 < 1 + t * ((Mf : ℝ) * r) := by
          linarith
        exact pow_ne_zero 2 this.ne'
    exact hcont_lower.intervalIntegrable_of_Icc hα0
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) α,
        r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤
          inner ℝ d (hessian f (x + t • d) d) := by
    intro t ht
    let z : E := x + t • d
    have hzSeg : z ∈ segment ℝ x y := by
      simpa [z] using segmentPoint_memSegment (x := x) (y := y) ⟨ht.1, le_trans ht.2 hα1⟩
    have hloew := hloewnerLower hzSeg
    rw [ContinuousLinearMap.le_def] at hloew
    have hdiag :
        0 ≤ inner ℝ d ((hessian f z -
          (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) • hessian f x) d) :=
      hloew.inner_nonneg_right d
    have hbase_nonneg : 0 ≤ inner ℝ d (hessian f x d) := hHessPos.inner_nonneg_right d
    have hz_nonneg : 0 ≤ inner ℝ d (hessian f z d) := by
      have hden_nonneg :
          0 ≤ (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) * inner ℝ d (hessian f x d) := by
        positivity
      have hdiag' :
          (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) * inner ℝ d (hessian f x d) ≤
            inner ℝ d (hessian f z d) := by
        have hdiag_expanded :
            0 ≤ inner ℝ d (hessian f z d) -
              (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) *
                inner ℝ d (hessian f x d) := by
          simpa [inner_sub_right, inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using hdiag
        linarith
      exact le_trans hden_nonneg hdiag'
    have hsub : z - x = t • d := by
      simp [z, d]
    have hscale : ‖z - x‖[f; x] = t * r := by
      rw [hsub]
      simpa [r] using hessianLocalNormSmulOfNonneg (f := f) (z := x) (u := d) hHessPos ht.1
    have hdiag' :
        (1 / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ)) * r ^ (2 : ℕ) ≤
          inner ℝ d (hessian f z d) := by
      have hbase :
          inner ℝ d (hessian f x d) = r ^ (2 : ℕ) := by
        symm
        exact sqHessianLocalNormEqInnerOfNonneg hbase_nonneg
      have hraw :
          (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) * inner ℝ d (hessian f x d) ≤
            inner ℝ d (hessian f z d) := by
        have hdiag_expanded :
            0 ≤ inner ℝ d (hessian f z d) -
              (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) *
                inner ℝ d (hessian f x d) := by
          simpa [inner_sub_right, inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using hdiag
        linarith
      rw [hscale] at hraw
      simpa [hbase, z, r, mul_assoc, mul_left_comm, mul_comm] using hraw
    simpa [div_eq_mul_inv, z, mul_assoc, mul_left_comm, mul_comm] using hdiag'
  have hmono :
      ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤
        ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) := by
    exact intervalIntegral.integral_mono_on hα0 hint_lower hderiv_int hpoint
  have hftc :
      ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) = g α - g 0 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hα0 hg_cont hderiv hderiv_int
  have hcalc :
      α * r ^ (2 : ℕ) / (1 + α * ((Mf : ℝ) * r)) ≤ g α - g 0 := by
    calc
      α * r ^ (2 : ℕ) / (1 + α * ((Mf : ℝ) * r))
          = ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) := by
              symm
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                integralSqDivEqScaledSqDivAdd hα0 (fun t ht ↦ by
                  have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
                    exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr0)
                  have : 0 < 1 + t * ((Mf : ℝ) * r) := by
                    linarith
                  simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      _ ≤ ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) := hmono
      _ = g α - g 0 := hftc
  simpa [g, d, r, inner_sub_left, mul_assoc, mul_left_comm, mul_comm] using hcalc

/-- Helper for Theorem 5 1 8: integrating the scalar restriction of `f` along the chord recovers
the gradient pairing integral. -/
private theorem segmentScalarIntegralEqOfContDiffOn :
    let d := y - x
    f y - f x = ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d := by
  let d : E := y - x
  let g : ℝ → ℝ := fun t ↦ f (x + t • d)
  have hline_mem :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • d ∈ dom := by
    intro t ht
    exact hsegment (segmentPoint_memSegment (x := x) (y := y) ht)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (valueLineHasDerivAtOfContDiffOn hcont hopen (hline_mem t ht)).continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt g (inner ℝ (∇ f (x + t • d)) d) t := by
    intro t ht
    simpa [g] using
      valueLineHasDerivAtOfContDiffOn hcont hopen (hline_mem t (Set.mem_Icc_of_Ioo ht))
  have hgrad_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d)
        MeasureTheory.volume 0 1 := by
    have hcont_line :
        ContinuousOn (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact
        (scalarizedGradientLineHasDerivAtOfContDiffOn hcont hopen
          (hline_mem t ht)).continuousAt.continuousWithinAt
    exact hcont_line.intervalIntegrable_of_Icc (by norm_num)
  have hftc :
      ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d = g 1 - g 0 := by
    simpa using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (show (0 : ℝ) ≤ 1 by norm_num) hg_cont hderiv hgrad_int
  simpa [g, d] using hftc.symm

-- Proof sketch: integrate the Loewner-order Hessian comparison along the segment
-- `y_τ = x + τ • (y - x)`. The base-point positivity hypothesis makes `‖y - x‖[f; x]` a genuine
-- Hessian norm, and `hloewnerLower` transports that positivity along the segment. The
-- fundamental theorem
-- of calculus gives
-- `∇ f(y) - ∇ f(x) = ∫₀¹ ∇² f(y_τ) (y - x) dτ`, and evaluating `hloewnerLower` on the
-- direction `y - x`
-- yields the scalar lower bound `r² / (1 + τ M_f r)^2` for the integrand, where
-- `r = hessianLocalNorm f x (y - x)`. Evaluating the integral gives the stated denominator
-- `1 + M_f r`.
-- Route correction: the current source-facing surface is semantically too weak for the ambient
-- owners `∇ f` and `hessian f`. On the closed segment `dom = Set.Icc (0 : ℝ) 1`, the function
-- `f t = -|t|` is `C²` on `dom` and has vanishing Hessian owner on the segment, but
-- `gradient_eq_zero_of_not_differentiableAt` forces `∇ f 0 = 0` while `∇ f 1 = -1`, so the
-- displayed lower bound fails. The repaired source-facing surface therefore keeps the ambient
-- owners `∇ f` and `hessian f` only under the missing open-domain premise.
/-- Theorem 5 1 8 (1): if a `C²` function has positive base Hessian `∇² f(x)` and along the
open segment-domain from `x` to `y` satisfies the lower Loewner-order Hessian comparison
`∇² f(z) ≽ (1 + M_f ‖z - x‖_x)⁻² ∇² f(x)`, then the gradient increment paired with `y - x`
is bounded below by `‖y - x‖_x² / (1 + M_f ‖y - x‖_x)`. -/
theorem gradient_difference_inner_ge_hessianLocalNorm_sq_div :
    let r := ‖y - x‖[f; x]
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
      r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) := by
  let d : E := y - x
  let r : ℝ := ‖d‖[f; x]
  -- Specialize the parameterized chord estimate at the full endpoint `α = 1`.
  have hseg :
      inner ℝ (∇ f (x + (1 : ℝ) • d) - ∇ f x) d ≥
        (1 : ℝ) * r ^ (2 : ℕ) / (1 + (1 : ℝ) * (Mf : ℝ) * r) := by
    exact segmentGradientIncrementLowerBoundOfLoewnerLower
      (hcont := hcont) (hsegment := hsegment) (hopen := hopen)
      (hHessPos := hHessPos) (hloewnerLower := hloewnerLower)
      (α := 1) (by norm_num) (by norm_num)
  simpa [d, r, one_mul, mul_assoc, mul_left_comm, mul_comm] using hseg

-- Proof sketch: write
-- `f y - f x - ⟪∇ f(x), y - x⟫ = ∫₀¹ ⟪∇ f(y_τ) - ∇ f(x), y - x⟫ dτ`
-- along the segment `y_τ = x + τ • (y - x)`, then apply clause (1) to each pair `(x, y_τ)`.
-- This gives the integrand lower bound `τ r² / (1 + τ M_f r)`, where
-- `r = hessianLocalNorm f x (y - x)`. Evaluating the integral yields
-- `(1 / M_f²) * ω(M_f r)` when `M_f > 0`, and its limiting value `(1 / 2) r²` when `M_f = 0`.
-- Route correction: clause (2) inherits the same ambient-differentiability issue as clause (1),
-- so the repaired statement keeps the same open-domain premise.
/-- Theorem 5 1 8 (2): under the same owner-level Hessian comparison along the segment from `x`
to `y` in an open set `dom` and the same base-Hessian positivity hypothesis at `x`, the function
value at `y` admits
the affine lower Taylor bound at `x` with remainder
`M_f⁻² ω(M_f ‖y - x‖_x)`, interpreted as `(1 / 2) ‖y - x‖_x²` when `M_f = 0`. -/
theorem taylor_lower_bound_of_hessian_loewner_lower :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    f y ≥
      f x + inner ℝ (∇ f x) (y - x) +
        if hMf : Mf = 0 then
          r ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
  let d : E := y - x
  let r : ℝ := ‖d‖[f; x]
  let tω := selfConcordantOmegaArg Mf r (by
    exact neg_one_lt_mf_mul_of_nonneg (by
      simpa [r, d] using hessianLocalNorm_nonneg f x d))
  have hr0 : 0 ≤ r := by
    simpa [r, d] using hessianLocalNorm_nonneg f x d
  have hvalue_eq :
      f y - f x = ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d := by
    simpa [d] using
      segmentScalarIntegralEqOfContDiffOn
        (hcont := hcont) (hsegment := hsegment) (hopen := hopen)
        (hHessPos := hHessPos) (hloewnerLower := hloewnerLower)
  have hline_mem :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • d ∈ dom := by
    intro t ht
    exact hsegment (segmentPoint_memSegment (x := x) (y := y) ht)
  have hpsi_cont :
      ContinuousOn (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d) - ∇ f x) d) (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hcont_t :
        ContinuousAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d) t := by
      exact
        (scalarizedGradientLineHasDerivAtOfContDiffOn hcont hopen
          (hline_mem t ht)).continuousAt
    have hsub :
        (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d) - ∇ f x) d) =
          fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d - inner ℝ (∇ f x) d := by
      ext s
      simp [inner_sub_left]
    rw [hsub]
    exact (hcont_t.sub continuousAt_const).continuousWithinAt
  have hpsi_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d) - ∇ f x) d)
        MeasureTheory.volume 0 1 := by
    exact hpsi_cont.intervalIntegrable_of_Icc (by norm_num)
  have hlower_int :
      IntervalIntegrable
        (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r))
        MeasureTheory.volume 0 1 := by
    have hcont_lower :
        ContinuousOn
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r))
          (Set.Icc (0 : ℝ) 1) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + t * (Mf : ℝ) * r) by continuity).continuousOn
      · intro t ht
        have hmul_nonneg : 0 ≤ t * (Mf : ℝ) * r := by
          exact mul_nonneg (mul_nonneg ht.1 Mf.2) hr0
        have : 0 < 1 + t * (Mf : ℝ) * r := by
          linarith
        exact this.ne'
    exact hcont_lower.intervalIntegrable_of_Icc (by norm_num)
  have hgradLine_int :
      IntervalIntegrable (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) MeasureTheory.volume 0 1 := by
    have hcont_line :
        ContinuousOn (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact
        (scalarizedGradientLineHasDerivAtOfContDiffOn hcont hopen
          (hline_mem t ht)).continuousAt.continuousWithinAt
    exact hcont_line.intervalIntegrable_of_Icc (by norm_num)
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ ↦ inner ℝ (∇ f x) d) MeasureTheory.volume 0 1 := by
    exact
      (intervalIntegral.intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ ↦ inner ℝ (∇ f x) d) MeasureTheory.volume 0 1)
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) ≤
          inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
    intro t ht
    simpa [d, r, mul_assoc, mul_left_comm, mul_comm] using
      segmentGradientIncrementLowerBoundOfLoewnerLower
        (hcont := hcont) (hsegment := hsegment) (hopen := hopen)
        (hHessPos := hHessPos) (hloewnerLower := hloewnerLower)
        (α := t) ht.1 ht.2
  have hgap_eq :
      f y - f x - inner ℝ (∇ f x) d =
        ∫ t in 0..1, inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
    calc
      f y - f x - inner ℝ (∇ f x) d
          = (∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d) -
              ∫ t in 0..1, inner ℝ (∇ f x) d := by
                rw [hvalue_eq]
                simp
      _ = ∫ t in 0..1, inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
            calc
              (∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d) - ∫ t in 0..1, inner ℝ (∇ f x) d
                  = ∫ t in 0..1, (inner ℝ (∇ f (x + t • d)) d - inner ℝ (∇ f x) d) := by
                      symm
                      exact intervalIntegral.integral_sub hgradLine_int hconst_int
              _ = ∫ t in 0..1, inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
                    refine intervalIntegral.integral_congr ?_
                    intro t
                    simp [inner_sub_left]
  have hgap_lower :
      ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) ≤
        f y - f x - inner ℝ (∇ f x) d := by
    calc
      ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r)
          ≤ ∫ t in 0..1, inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
              exact intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
                hlower_int hpsi_int hpoint
      _ = f y - f x - inner ℝ (∇ f x) d := hgap_eq.symm
  by_cases hMf : Mf = 0
  · have hint :
        ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) = r ^ (2 : ℕ) / 2 := by
      rw [hMf]
      calc
        ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (0 : ℝ) * r)
            = ∫ t in 0..1, t * r ^ (2 : ℕ) := by
                refine intervalIntegral.integral_congr ?_
                intro t
                simp
        _ = r ^ (2 : ℕ) / 2 := by
              rw [intervalIntegral.integral_mul_const, integral_id]
              ring
    have hfinal : r ^ (2 : ℕ) / 2 ≤ f y - f x - inner ℝ (∇ f x) d := by
      rw [← hint]
      exact hgap_lower
    have hresult :
        f y ≥ f x + inner ℝ (∇ f x) d + r ^ (2 : ℕ) / 2 := by
      linarith
    simpa [d, r, tω, hMf] using hresult
  · have hMf_pos : 0 < (Mf : ℝ) := by
      have hMf_nn : 0 < Mf := by
        exact pos_iff_ne_zero.mpr hMf
      exact_mod_cast hMf_nn
    have hint :
        ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) =
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω tω := by
      simpa [r, tω] using integralMulSqDivEqOmegaAux (Mf := Mf) (r := r) hr0 hMf_pos
    have hfinal :
        (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω ≤ f y - f x - inner ℝ (∇ f x) d := by
      rw [← hint]
      exact hgap_lower
    have hresult :
        f y ≥ f x + inner ℝ (∇ f x) d + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
      linarith
    simpa [d, r, tω, hMf] using hresult

end

/-- Helper for Theorem 5 1 8: once the Hessian quadratic form is nonnegative, squaring the local
norm recovers that quadratic form exactly. -/
private theorem sq_hessianLocalNorm_eq_inner_of_nonneg
    {f : E → ℝ} {z u : E} (hquad : 0 ≤ inner ℝ u (hessian f z u)) :
    ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (hessian f z u) := by
  -- Expand the local norm and use the standard `sqrt(x)^2 = x` identity.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5 1 8: nonnegative scalar dilations scale the Hessian local norm by the
same scalar. -/
private theorem hessianLocalNorm_smul_of_nonneg
    {f : E → ℝ} {z u : E} (hzPos : (hessian f z).IsPositive)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[f; z] = τ * ‖u‖[f; z] := by
  have hquad : 0 ≤ inner ℝ u (hessian f z u) := hzPos.inner_nonneg_right u
  -- Reduce to the scalar identity `sqrt (τ² q) = τ sqrt q` with `q ≥ 0`.
  calc
    ‖τ • u‖[f; z] = Real.sqrt ((τ * τ) * inner ℝ u (hessian f z u)) := by
      rw [hessianLocalNorm_def]
      congr 1
      simp [inner_smul_left, inner_smul_right, mul_assoc]
    _ = Real.sqrt (inner ℝ u (hessian f z u)) * Real.sqrt (τ * τ) := by
      rw [mul_comm, Real.sqrt_mul hquad]
    _ = τ * ‖u‖[f; z] := by
      rw [show τ * τ = τ ^ (2 : ℕ) by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ,
        hessianLocalNorm_def]
      ring

omit [CompleteSpace E] in
/-- Helper for Theorem 5 1 8: affine lines have the expected derivative. -/
private theorem line_hasDerivAt
    (z d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ z + s • d) d t := by
  -- Differentiate the scalar parameter and keep the direction fixed.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add z

omit [CompleteSpace E] in
/-- Helper for Theorem 5 1 8: convexity places every affine segment point
`x + t • (y - x)` back in the ambient domain. -/
private theorem segmentPoint_mem
    {dom : Set E} (hconv : Convex ℝ dom) {x y : E}
    (hx : x ∈ dom) (hy : y ∈ dom) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ dom := by
  -- Rewrite the affine interpolation point into the canonical convex-combination form.
  have hrewrite : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub]
    rw [show (1 - t : ℝ) • x = x - t • x by rw [sub_smul, one_smul]]
    abel
  have h1t : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  rw [hrewrite]
  exact hconv hx hy h1t ht0 hsum

/-- Helper for Theorem 5 1 8: the rational lower integrand has the expected antiderivative. -/
private theorem integral_sq_div_eq_scaled_sq_div_add
    {a r u : ℝ} (hu : 0 ≤ u)
    (hden : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 + t * a) :
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) =
      u * r ^ (2 : ℕ) / (1 + u * a) := by
  have hnum :
      ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * a))
        (Set.Icc (0 : ℝ) u) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 + t * a) by continuity).continuousOn
    · intro t ht
      exact (hden t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
        MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) u) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 + t * a) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) u := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 + t * a ≠ 0 := (hden t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 + s * a) a t := by
      convert (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot :=
      ((hasDerivAt_id t).mul_const (r ^ (2 : ℕ))).div hden_deriv hden_ne
    have hslope :
        ((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * a) - t * r ^ (2 : ℕ) * a) /
            (1 + t * a) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ) := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 + s * a))
          (((1 : ℝ) * r ^ (2 : ℕ) * (1 + t * a) - t * r ^ (2 : ℕ) * a) /
            (1 + t * a) ^ (2 : ℕ))
          t := by
      simpa using hquot
    exact hquot'.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hnum hderiv hint
  calc
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 + t * a) ^ (2 : ℕ)
        = u * r ^ (2 : ℕ) / (1 + u * a) - (0 * r ^ (2 : ℕ) / (1 + 0 * a)) := by
            simpa using hftc
    _ = u * r ^ (2 : ℕ) / (1 + u * a) := by ring

/-- Helper for Theorem 5 1 8: the second scalar integration in the lower Taylor bound evaluates
to the Chapter 5 auxiliary function `ω`. -/
private theorem integralMulSqDivEqOmega
    {Mf : NNReal} {r : ℝ} (hr0 : 0 ≤ r) (hMf_pos : 0 < (Mf : ℝ)) :
    let tω := selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr0)
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) =
      (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω tω := by
  let a : ℝ := (Mf : ℝ)
  have ha_ne : a ≠ 0 := ne_of_gt (by simpa [a] using hMf_pos)
  have hnum :
      ContinuousOn
        (fun t : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (a * t * r - Real.log (1 + a * t * r)))
        (Set.Icc (0 : ℝ) 1) := by
    have hlog :
        ContinuousOn (fun t : ℝ ↦ Real.log (1 + a * t * r)) (Set.Icc (0 : ℝ) 1) := by
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + a * t * r) by continuity).continuousOn
      · intro t ht
        have harg_pos : 0 < 1 + a * t * r := by
          have ht_nonneg : 0 ≤ t := ht.1
          have har_nonneg : 0 ≤ a * r := mul_nonneg hMf_pos.le hr0
          have hmul_nonneg : 0 ≤ a * t * r := by
            nlinarith
          linarith
        exact harg_pos.ne'
    have hlin :
        ContinuousOn (fun t : ℝ ↦ a * t * r) (Set.Icc (0 : ℝ) 1) := by
      exact (show Continuous (fun t : ℝ ↦ a * t * r) by continuity).continuousOn
    -- Keep the antiderivative in the exact source-friendly scalar form.
    refine continuousOn_const.mul ?_
    exact hlin.sub hlog
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + a * t * r))
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + a * t * r))
          (Set.Icc (0 : ℝ) 1) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + a * t * r) by continuity).continuousOn
      · intro t ht
        have harg_pos : 0 < 1 + a * t * r := by
          have ht_nonneg : 0 ≤ t := ht.1
          have har_nonneg : 0 ≤ a * r := mul_nonneg hMf_pos.le hr0
          have hmul_nonneg : 0 ≤ a * t * r := by
            nlinarith
          linarith
        exact harg_pos.ne'
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (fun s : ℝ ↦
            (1 / (a ^ (2 : ℕ))) * (a * s * r - Real.log (1 + a * s * r)))
          (t * r ^ (2 : ℕ) / (1 + a * t * r)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioo ht
    have harg_ne : 1 + a * t * r ≠ 0 := by
      have harg_pos : 0 < 1 + a * t * r := by
        have ht_nonneg : 0 ≤ t := ht.1.le
        have har_nonneg : 0 ≤ a * r := mul_nonneg hMf_pos.le hr0
        have hmul_nonneg : 0 ≤ a * t * r := by
          nlinarith
        linarith
      exact harg_pos.ne'
    have harg :
        HasDerivAt (fun s : ℝ ↦ 1 + a * s * r) (a * r) t := by
      convert
        (hasDerivAt_const t (1 : ℝ)).add ((((hasDerivAt_id t).const_mul a).mul_const r)) using 1
      ring
    have hlog :
        HasDerivAt (fun s : ℝ ↦ Real.log (1 + a * s * r))
          ((a * r) / (1 + a * t * r)) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_log harg_ne).comp t harg
    have hlin :
        HasDerivAt (fun s : ℝ ↦ a * s * r) (a * r) t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((((hasDerivAt_id t).const_mul a).mul_const r))
    have hbase :
        HasDerivAt
          (fun s : ℝ ↦ a * s * r - Real.log (1 + a * s * r))
          (a * r - ((a * r) / (1 + a * t * r))) t := by
      -- Differentiate the linear and logarithmic pieces separately before recombining them.
      exact hlin.sub hlog
    have hscaled :
        HasDerivAt
          (fun s : ℝ ↦
            (1 / (a ^ (2 : ℕ))) * (a * s * r - Real.log (1 + a * s * r)))
          ((1 / (a ^ (2 : ℕ))) * (a * r - ((a * r) / (1 + a * t * r)))) t := by
      exact hbase.const_mul (1 / (a ^ (2 : ℕ)))
    have hslope :
        ((1 / (a ^ (2 : ℕ))) * (a * r - ((a * r) / (1 + a * t * r)))) =
          t * r ^ (2 : ℕ) / (1 + a * t * r) := by
      have hfrac :
          1 - (1 + a * t * r)⁻¹ = (a * t * r) * (1 + a * t * r)⁻¹ := by
        field_simp [harg_ne]
        ring
      calc
        ((1 / (a ^ (2 : ℕ))) * (a * r - ((a * r) / (1 + a * t * r))))
            = (1 / (a ^ (2 : ℕ))) * (a * r) * (1 - (1 + a * t * r)⁻¹) := by
                ring_nf
        _ = (1 / (a ^ (2 : ℕ))) * (a * r) * ((a * t * r) * (1 + a * t * r)⁻¹) := by
              rw [hfrac]
        _ = t * r ^ (2 : ℕ) / (1 + a * t * r) := by
              field_simp [ha_ne, harg_ne]
    exact hscaled.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show (0 : ℝ) ≤ 1 by norm_num) hnum hderiv hint
  calc
    ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r)
        =
          ((1 / (a ^ (2 : ℕ))) * (a * 1 * r - Real.log (1 + a * 1 * r))) -
            ((1 / (a ^ (2 : ℕ))) * (a * 0 * r - Real.log (1 + a * 0 * r))) := by
              simpa [a, mul_assoc, mul_left_comm, mul_comm] using hftc
    _ = (1 / (a ^ (2 : ℕ))) * (a * r - Real.log (1 + a * r)) := by
      simp
    _ = (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
          ω (selfConcordantOmegaArg Mf r (neg_one_lt_mf_mul_of_nonneg hr0)) := by
      rw [selfConcordantOmega_apply]
      simp [a, mul_comm]

/-- Helper for Theorem 5 1 8: an admissible Dikin step forces `(Mf : ℝ) > 0` whenever the
reciprocal radius contributes nontrivially. -/
private theorem mf_pos_of_mem_openDikinEllipsoid
    {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    0 < (Mf : ℝ) := by
  let r := ‖y - x‖[f; x]
  have hr : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg f x (y - x)
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := by
    exact_mod_cast Mf.2
  by_contra hMf_nonpos
  have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf_nonpos) hMf_nonneg
  have hr_neg : r < 0 := by
    simpa [hMf_eq_zero] using hr
  linarith

/-- Helper for Theorem 5 1 8: on the open self-concordant domain, the Hessian owner varies
continuously. -/
private theorem hessian_continuousOn_of_selfConcordant
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) :
    ContinuousOn (hessian f) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ f) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) dom :=
      (hself.contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).fderiv_of_isOpen
          hself.isOpen_domain
          (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen
      hself.isOpen_domain
      (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn

/-- Helper for Theorem 5 1 8: a `C²` field has a differentiable gradient at the point. -/
private theorem differentiableAt_gradient_of_contDiffAt_two
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) :
    DifferentiableAt ℝ (∇ f) z := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) z := by
    -- A `C²` field has a differentiable first derivative.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  -- Rewrite the gradient through the Riesz map so the chain rule applies directly.
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) z
  exact (D.hasFDerivAt.comp z hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5 1 8: differentiating `f` along an admissible affine line recovers the
gradient pairing with the line direction. -/
private theorem value_line_hasDerivAt_of_selfConcordant
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {z d : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ f (z + s • d)) (inner ℝ (∇ f (z + t • d)) d) t := by
  have hC1 : ContDiffAt ℝ 1 f (z + t • d) := by
    exact
      (hself.contDiffOn.of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt
          (hself.isOpen_domain.mem_nhds hzt)
  -- Differentiate the ambient function first and then compose with the affine line.
  simpa using
    ((hC1.differentiableAt one_ne_zero).hasGradientAt.hasFDerivAt.comp t
      (line_hasDerivAt z d t).hasFDerivAt).hasDerivAt

/-- Helper for Theorem 5 1 8: scalarizing the gradient along an admissible affine line
differentiates to the corresponding Hessian pairing. -/
private theorem scalarized_gradient_line_hasDerivAt_of_selfConcordant
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {z d w : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (z + s • d)) w)
      (inner ℝ (hessian f (z + t • d) d) w) t := by
  have hz_C2 : ContDiffAt ℝ 2 f (z + t • d) := by
    exact
      (hself.contDiffOn.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt
          (hself.isOpen_domain.mem_nhds hzt)
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (z + s • d))
        ((hessian f (z + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Route correction: differentiate the raw scalarized gradient line before subtracting any
    -- endpoint terms.
    simpa using
      ((differentiableAt_gradient_of_contDiffAt_two hz_C2).hasFDerivAt.comp t
        (line_hasDerivAt z d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (z + s • d)))
        (φ.comp ((hessian f (z + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional `v ↦ ⟪v, w⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

/-- Helper for Theorem 5 1 8: along a self-concordant segment, the gradient increment paired with
the full chord is bounded below by the textbook transport factor. -/
private theorem segmentGradientIncrementLowerBoundAtBase
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hy : y ∈ dom)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    let d := y - x
    let r := ‖d‖[f; x]
    inner ℝ (∇ f (x + α • d) - ∇ f x) d ≥
      α * r ^ (2 : ℕ) / (1 + α * (Mf : ℝ) * r) := by
  let d : E := y - x
  let r : ℝ := ‖d‖[f; x]
  have hr0 : 0 ≤ r := by
    simpa [d, r] using hessianLocalNorm_nonneg f x d
  let g : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • d)) d
  -- Route correction: integrate the scalarized gradient line directly and feed the self-concordant
  -- transport estimate pointwise along the segment.
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) α) := by
    intro t ht
    have hz : x + t • d ∈ dom := segmentPoint_mem hself.convex_domain hx hy ht.1 (le_trans ht.2 hα1)
    have hderiv_t : HasDerivAt g (inner ℝ d (hessian f (x + t • d) d)) t := by
      simpa [g, real_inner_comm] using
        scalarized_gradient_line_hasDerivAt_of_selfConcordant hself hz
    exact hderiv_t.continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) α,
        HasDerivAt g (inner ℝ d (hessian f (x + t • d) d)) t := by
    intro t ht
    have hz : x + t • d ∈ dom := segmentPoint_mem hself.convex_domain hx hy (le_of_lt ht.1)
      (le_trans (le_of_lt ht.2) hα1)
    simpa [g, real_inner_comm] using
      scalarized_gradient_line_hasDerivAt_of_selfConcordant hself hz
  have hderiv_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ d (hessian f (x + t • d) d))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ inner ℝ d (hessian f (x + t • d) d))
          (Set.Icc (0 : ℝ) α) := by
      intro t ht
      have hz : x + t • d ∈ dom := segmentPoint_mem hself.convex_domain hx hy ht.1
        (le_trans ht.2 hα1)
      have hsmul_cont : ContinuousAt (fun s : ℝ ↦ s • d) t := by
        simpa [one_smul] using ((hasDerivAt_id t).smul_const d).continuousAt
      have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • d) t := by
        exact ContinuousAt.comp (continuousAt_const.add continuousAt_id) hsmul_cont
      have hhess_cont : ContinuousAt (hessian f) (x + t • d) :=
        (hessian_continuousOn_of_selfConcordant hself).continuousAt
          (hself.isOpen_domain.mem_nhds hz)
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • d)) t := by
        refine ContinuousAt.comp hhess_cont ?_
        exact ContinuousAt.comp (continuousAt_const.add continuousAt_id) hsmul_cont
      let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) d
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • d) d) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E d).continuous.continuousAt) hhess_line
      have hinner_cont :
          ContinuousAt (fun s : ℝ ↦ inner ℝ d (hessian f (x + s • d) d)) t := by
        simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φ.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hα0
  have hint_lower :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
        MeasureTheory.volume 0 α := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) α) := by
      refine continuousOn_const.div ?_ ?_
      · exact
          (show Continuous (fun t : ℝ ↦ (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
          exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr0)
        have : 0 < 1 + t * ((Mf : ℝ) * r) := by
          linarith
        exact pow_ne_zero 2 this.ne'
    exact hcont.intervalIntegrable_of_Icc hα0
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) α,
        r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤
          inner ℝ d (hessian f (x + t • d) d) := by
    intro t ht
    have ht1 : t ≤ 1 := le_trans ht.2 hα1
    have hz : x + t • d ∈ dom := segmentPoint_mem hself.convex_domain hx hy ht.1 ht1
    have hquadz : 0 ≤ inner ℝ d (hessian f (x + t • d) d) :=
      hself.hessian_posSemidef hz d
    have hsub : (x + t • d) - x = t • d := by
      abel
    have hdisp :
        ‖(x + t • d) - x‖[f; x + t • d] ≥
          ‖(x + t • d) - x‖[f; x] /
            (1 + (Mf : ℝ) * ‖(x + t • d) - x‖[f; x]) := by
      exact hself.displacement_localNorm_lower_bound hx hz
    rw [hsub,
      hessianLocalNorm_smul_of_nonneg (hself.hessian_isPositive hz) ht.1,
      hessianLocalNorm_smul_of_nonneg (hself.hessian_isPositive hx) ht.1] at hdisp
    have hden_pos : 0 < 1 + t * ((Mf : ℝ) * r) := by
      have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
        exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr0)
      linarith
    have hdir : r / (1 + t * ((Mf : ℝ) * r)) ≤ ‖d‖[f; x + t • d] := by
      by_cases ht_zero : t = 0
      · subst ht_zero
        simp [r]
      · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
        have hdisp' : t * (r / (1 + t * ((Mf : ℝ) * r))) ≤ t * ‖d‖[f; x + t • d] := by
          simpa [r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdisp
        exact le_of_mul_le_mul_left hdisp' ht_pos
    have hsq_norm :
        (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) ≤ ‖d‖[f; x + t • d] ^ (2 : ℕ) := by
      have hdir_nonneg : 0 ≤ r / (1 + t * ((Mf : ℝ) * r)) := by positivity
      have hnorm_nonneg : 0 ≤ ‖d‖[f; x + t • d] :=
        hessianLocalNorm_nonneg f (x + t • d) d
      nlinarith [hdir, hdir_nonneg, hnorm_nonneg]
    have hfrac :
        (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) := by
      field_simp [hden_pos.ne']
    calc
      r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) = (r / (1 + t * ((Mf : ℝ) * r))) ^ (2 : ℕ) := by
        exact hfrac.symm
      _ ≤ ‖d‖[f; x + t • d] ^ (2 : ℕ) := hsq_norm
      _ = inner ℝ d (hessian f (x + t • d) d) := sq_hessianLocalNorm_eq_inner_of_nonneg hquadz
  have hmono :
      ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) ≤
        ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) := by
    exact intervalIntegral.integral_mono_on hα0 hint_lower hderiv_int hpoint
  have hftc :
      ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) = g α - g 0 := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hα0 hg_cont hderiv hderiv_int
  have hcalc :
      α * r ^ (2 : ℕ) / (1 + α * ((Mf : ℝ) * r)) ≤ g α - g 0 := by
    calc
      α * r ^ (2 : ℕ) / (1 + α * ((Mf : ℝ) * r))
          = ∫ t in 0..α, r ^ (2 : ℕ) / (1 + t * ((Mf : ℝ) * r)) ^ (2 : ℕ) := by
              symm
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                integral_sq_div_eq_scaled_sq_div_add hα0 (fun t ht ↦ by
                  have hmul_nonneg : 0 ≤ t * ((Mf : ℝ) * r) := by
                    exact mul_nonneg ht.1 (mul_nonneg Mf.2 hr0)
                  have : 0 < 1 + t * ((Mf : ℝ) * r) := by
                    linarith
                  simpa [mul_assoc, mul_left_comm, mul_comm] using this)
      _ ≤ ∫ t in 0..α, inner ℝ d (hessian f (x + t • d) d) := hmono
      _ = g α - g 0 := hftc
  simpa [g, d, r, inner_sub_left, mul_assoc, mul_left_comm, mul_comm] using hcalc

/-- Helper for Theorem 5 1 8: integrating the scalar restriction of `f` along a self-concordant
segment recovers the gradient pairing integral. -/
private theorem segmentScalarIntegralEq
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x d : E} (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • d ∈ dom) :
    f (x + d) - f x = ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d := by
  let g : ℝ → ℝ := fun t ↦ f (x + t • d)
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact
      (value_line_hasDerivAt_of_selfConcordant hself (hsegment t ht)).continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (inner ℝ (∇ f (x + t • d)) d) t := by
    intro t ht
    simpa [g] using
      value_line_hasDerivAt_of_selfConcordant hself (hsegment t (Set.mem_Icc_of_Ioo ht))
  have hgrad_int :
      IntervalIntegrable (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact
        (scalarized_gradient_line_hasDerivAt_of_selfConcordant hself
          (hsegment t ht)).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hftc :
      ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d = g 1 - g 0 := by
    simpa using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (show (0 : ℝ) ≤ 1 by norm_num) hg_cont hderiv hgrad_int
  simpa [g] using hftc.symm

namespace IsSelfConcordantOnWith

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: derive `y ∈ dom` from the Dikin-step hypothesis via
-- `openDikinEllipsoid_inv_constant_subset`, use convexity of `dom` to place the whole segment
-- from `x` to `y` inside `dom`, and apply
-- `hessian_loewner_bounds_of_mem_openDikinEllipsoid` pointwise to the intermediate points
-- `x + τ • (y - x)` to recover the lower segment-wise Loewner hypothesis required by the
-- source-facing Theorem 5.1.8. The two displayed estimates then follow by the local theorems
-- `gradient_difference_inner_ge_hessianLocalNorm_sq_div` and
-- `taylor_lower_bound_of_hessian_loewner_lower`.
-- The repaired source-facing theorems above now match this owner-level open-domain surface.
/-- Under the Chapter 5 owner `IsSelfConcordantOnWith dom Mf f`, every admissible Dikin step
`y ∈ W⁰[f; x](1 / (Mf : ℝ))` satisfies both lower bounds from Theorem 5.1.8: the gradient pairing
dominates `‖y - x‖_x² / (1 + M_f ‖y - x‖_x)`, and the function value dominates the affine Taylor
approximation at `x` with the explicit self-concordant remainder `ω`. This is the canonical
owner-level bridge from self-concordance to the source-facing lower estimates. -/
theorem gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
        r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) ∧
      f y ≥
        f x + inner ℝ (∇ f x) (y - x) +
          if hMf : Mf = 0 then
            r ^ (2 : ℕ) / 2
          else
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
  let d : E := y - x
  let r : ℝ := ‖d‖[f; x]
  let tω := selfConcordantOmegaArg Mf r (by
    exact neg_one_lt_mf_mul_of_nonneg (by
      simpa [r] using hessianLocalNorm_nonneg f x d))
  have hy : y ∈ dom := by
    exact
      IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset
        (domain := dom) (Mf := (Mf : NNReal)) (f := f) hself hx hxy
  have hsegment :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • d ∈ dom := by
    intro t ht
    exact segmentPoint_mem hself.convex_domain hx hy ht.1 ht.2
  have hgrad_lower :
      inner ℝ (∇ f y - ∇ f x) d ≥ r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) := by
    have hseg :
        inner ℝ (∇ f (x + (1 : ℝ) • d) - ∇ f x) d ≥
          (1 : ℝ) * r ^ (2 : ℕ) / (1 + (1 : ℝ) * (Mf : ℝ) * r) := by
      exact
        segmentGradientIncrementLowerBoundAtBase hself hx hy
          (show (0 : ℝ) ≤ 1 by norm_num)
          (show (1 : ℝ) ≤ 1 by norm_num)
    simpa [d, r, one_mul, mul_assoc, mul_left_comm, mul_comm] using hseg
  have hMf_pos : 0 < (Mf : ℝ) := by
    exact mf_pos_of_mem_openDikinEllipsoid hxy
  have hMf_ne : Mf ≠ 0 := by
    intro hMf
    exact hMf_pos.ne' (by simpa using hMf)
  have hvalue_eq :
      f y - f x = ∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d := by
    simpa [d] using segmentScalarIntegralEq hself hsegment
  have hpsi_cont :
      ContinuousOn (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d) - ∇ f x) d) (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hcont :
        ContinuousAt (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d) t := by
      exact
        (scalarized_gradient_line_hasDerivAt_of_selfConcordant hself (hsegment t ht)).continuousAt
    have hsub :
        (fun s : ℝ ↦ inner ℝ (∇ f (x + s • d) - ∇ f x) d) =
          fun s : ℝ ↦ inner ℝ (∇ f (x + s • d)) d - inner ℝ (∇ f x) d := by
      ext s
      simp [inner_sub_left]
    rw [hsub]
    exact (hcont.sub continuousAt_const).continuousWithinAt
  have hpsi_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d) - ∇ f x) d)
        MeasureTheory.volume 0 1 := by
    exact hpsi_cont.intervalIntegrable_of_Icc (by norm_num)
  have hlower_int :
      IntervalIntegrable
        (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r))
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r))
          (Set.Icc (0 : ℝ) 1) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 + t * (Mf : ℝ) * r) by continuity).continuousOn
      · intro t ht
        have hmul_nonneg : 0 ≤ t * (Mf : ℝ) * r := by
          exact mul_nonneg (mul_nonneg ht.1 hMf_pos.le) (hessianLocalNorm_nonneg f x d)
        have : 0 < 1 + t * (Mf : ℝ) * r := by
          linarith
        exact this.ne'
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hgradLine_int :
      IntervalIntegrable (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn (fun t : ℝ ↦ inner ℝ (∇ f (x + t • d)) d) (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact
        (scalarized_gradient_line_hasDerivAt_of_selfConcordant hself
          (hsegment t ht)).continuousAt.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ ↦ inner ℝ (∇ f x) d) MeasureTheory.volume 0 1 := by
    exact
      (intervalIntegral.intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ ↦ inner ℝ (∇ f x) d) MeasureTheory.volume 0 1)
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) ≤
          inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
    intro t ht
    simpa [d, r, mul_assoc, mul_left_comm, mul_comm] using
      segmentGradientIncrementLowerBoundAtBase hself hx hy ht.1 ht.2
  have hgap_eq :
      f y - f x - inner ℝ (∇ f x) d =
        ∫ t in 0..1, inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
    calc
      f y - f x - inner ℝ (∇ f x) d
          = (∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d) -
              ∫ t in 0..1, inner ℝ (∇ f x) d := by
                rw [hvalue_eq]
                simp
      _ = ∫ t in 0..1, inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
            calc
              (∫ t in 0..1, inner ℝ (∇ f (x + t • d)) d) - ∫ t in 0..1, inner ℝ (∇ f x) d
                  = ∫ t in 0..1, (inner ℝ (∇ f (x + t • d)) d - inner ℝ (∇ f x) d) := by
                      symm
                      exact intervalIntegral.integral_sub hgradLine_int hconst_int
              _ = ∫ t in 0..1, inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
                    refine intervalIntegral.integral_congr ?_
                    intro t
                    simp [inner_sub_left]
  have hgap_lower :
      ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) ≤
        f y - f x - inner ℝ (∇ f x) d := by
    calc
      ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r)
          ≤ ∫ t in 0..1, inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
              exact intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
                hlower_int hpsi_int hpoint
      _ = f y - f x - inner ℝ (∇ f x) d := hgap_eq.symm
  constructor
  · simpa [d, r] using hgrad_lower
  · have hint :
        ∫ t in 0..1, t * r ^ (2 : ℕ) / (1 + t * (Mf : ℝ) * r) =
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω tω := by
      simpa [r, tω] using integralMulSqDivEqOmega
        (by simpa [r] using hessianLocalNorm_nonneg f x d) hMf_pos
    have hfinal :
        (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω ≤ f y - f x - inner ℝ (∇ f x) d := by
      rw [← hint]
      exact hgap_lower
    have hresult :
        f y ≥ f x + inner ℝ (∇ f x) d + (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
      linarith
    simpa [d, r, tω, hMf_ne] using hresult

-- Proof sketch: project the first component of the owner-level conjunction above.
/-- The owner-level gradient-pairing lower bound derived from `IsSelfConcordantOnWith dom Mf f`
and the admissible Dikin-step hypothesis. -/
theorem gradient_difference_inner_ge_hessianLocalNorm_sq_div_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
      ‖y - x‖[f; x] ^ (2 : ℕ) / (1 + (Mf : ℝ) * ‖y - x‖[f; x]) := by
  simpa using
    (gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid hself hx hxy).1

-- Proof sketch: project the second component of the owner-level conjunction above.
/-- The owner-level Taylor lower bound with remainder `ω`, derived from
`IsSelfConcordantOnWith dom Mf f` and the admissible Dikin-step hypothesis. -/
theorem taylor_lower_bound_with_selfConcordantOmega_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    f y ≥
      f x + inner ℝ (∇ f x) (y - x) +
        if hMf : Mf = 0 then
          r ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
  simpa using
    (gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid hself hx hxy).2

end

end IsSelfConcordantOnWith

end
