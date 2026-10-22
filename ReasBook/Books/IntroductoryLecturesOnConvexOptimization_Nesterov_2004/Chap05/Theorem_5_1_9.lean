/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DikinEllipsoidNotation Gradient HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.9 lies in the Chapter 5 self-concordance / local Taylor-upper-bound domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner for quantitative
  self-concordance;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the owner for the
  local Hessian norm;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` and
  `IsSelfConcordantOnWith.displacement_localNorm_upper_bound` from `Theorem_5_1_5`, the canonical
  owner-level admissible-step transport API;
* `ω_* : Set.Iio (1 : ℝ) → ℝ` and `selfConcordantOmegaStarArg` from `Definition_5_0_21`, the
  chapter owners for the self-concordant upper remainder.

Source/core/bridge triage:
* source-facing: Theorem 5.1.9 itself, stated for `IsSelfConcordantOnWith dom Mf f` and an
  admissible Dikin step `y ∈ W⁰[f; x](1 / (Mf : ℝ))`;
* core/canonical: `IsSelfConcordantOnWith dom Mf f`, `‖u‖[f; x]`, `hessian f z`, and `ω_*`;
* bridge/view: the transport-data helper below, which isolates the proof-route ingredients
  extracted canonically from the owner.

Primitive data:
* the owner witness `hself : IsSelfConcordantOnWith dom Mf f`;
* the center membership `hx : x ∈ dom`;
* the admissible-step hypothesis `hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))`.

Derived API:
* domain membership of the endpoint `y`;
* the local-norm transport bound at the endpoint;
* Hessian quadratic-form nonnegativity along the admissible step;
* the gradient-pairing and first-order Taylor upper bounds.

The numbered item is therefore owner-level. The transport-data theorem remains only as a private
proof bridge; the public theorem surface lives in `namespace IsSelfConcordantOnWith`. -/

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}
variable (hf_C2 : ContDiffOn ℝ 2 f dom)
variable (hstep :
  ∀ ⦃x h : E⦄, x ∈ dom → ‖h‖[f; x] < 1 / (Mf : ℝ) → x + h ∈ dom)
variable (htransport :
  ∀ ⦃x h : E⦄, x ∈ dom → x + h ∈ dom →
    ‖h‖[f; x] < 1 / (Mf : ℝ) →
      ‖h‖[f; x + h] ≤ ‖h‖[f; x] / (1 - (Mf : ℝ) * ‖h‖[f; x]))
variable (hquad_nonneg :
  ∀ ⦃x h : E⦄, x ∈ dom → x + h ∈ dom →
    ‖h‖[f; x] < 1 / (Mf : ℝ) →
      0 ≤ inner ℝ h (hessian f (x + h) h))

include hf_C2 hstep htransport hquad_nonneg

omit hf_C2 hstep htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: squaring the local norm recovers the Hessian quadratic form whenever
that quadratic form is nonnegative. -/
private theorem sq_hessianLocalNorm_eq_inner_of_nonneg
    {z u : E} (hquad : 0 ≤ inner ℝ u (hessian f z u)) :
    ‖u‖[f; z] ^ (2 : ℕ) = inner ℝ u (hessian f z u) := by
  -- Expand the local norm and use `sqrt(x)^2 = x` on the nonnegative quadratic form.
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

omit hf_C2 hstep htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: nonnegative scalar dilations scale the local norm by the same
scalar. -/
private theorem hessianLocalNorm_smul_of_nonneg
    {z u : E} {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖τ • u‖[f; z] = τ * ‖u‖[f; z] := by
  by_cases hquad : 0 ≤ inner ℝ u (hessian f z u)
  · -- In the nonnegative quadratic-form regime, this is the usual `sqrt (τ² q) = τ sqrt q`.
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
  · -- If the quadratic form is nonpositive, both square roots vanish.
    have hquad_nonpos : inner ℝ u (hessian f z u) ≤ 0 := le_of_not_ge hquad
    have hscaled_nonpos :
        inner ℝ (τ • u) (hessian f z (τ • u)) ≤ 0 := by
      have hrewrite :
          inner ℝ (τ • u) (hessian f z (τ • u)) =
            (τ * τ) * inner ℝ u (hessian f z u) := by
        simp [inner_smul_left, inner_smul_right, mul_assoc]
      rw [hrewrite]
      nlinarith [sq_nonneg τ, hquad_nonpos]
    -- Expand both sides and use `sqrt_eq_zero_of_nonpos`.
    rw [hessianLocalNorm_def, hessianLocalNorm_def, Real.sqrt_eq_zero_of_nonpos hscaled_nonpos,
      Real.sqrt_eq_zero_of_nonpos hquad_nonpos]
    ring

omit hf_C2 hstep htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: the open-Dikin hypothesis forces the self-concordance constant to be
strictly positive, so the reciprocal radius `1 / M_f` is genuinely positive. -/
private theorem mf_pos_of_mem_openDikinEllipsoid
    {x y : E} (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    0 < (Mf : ℝ) := by
  let r := ‖y - x‖[f; x]
  have hr : r < 1 / (Mf : ℝ) := by
    simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using hessianLocalNorm_nonneg f x (y - x)
  have hMf_nonneg : 0 ≤ (Mf : ℝ) := by exact_mod_cast Mf.2
  by_contra hMf_nonpos
  have hMf_eq_zero : (Mf : ℝ) = 0 := le_antisymm (le_of_not_gt hMf_nonpos) hMf_nonneg
  have hr_neg : r < 0 := by
    simpa [hMf_eq_zero] using hr
  linarith

omit hf_C2 hquad_nonneg in
/-- Helper for Theorem 5.1.9: every scaled substep of the admissible displacement stays in the
domain, and the transport estimate rescales with the expected factor `τ`. -/
private theorem segment_step_mem_dom_and_scaled_transport
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    x + τ • (y - x) ∈ dom ∧
      ‖τ • (y - x)‖[f; x + τ • (y - x)] ≤
        (τ * ‖y - x‖[f; x]) / (1 - (Mf : ℝ) * τ * ‖y - x‖[f; x]) := by
  let h := y - x
  let r := ‖h‖[f; x]
  have hr : r < 1 / (Mf : ℝ) := by
    simpa [h, r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hr_nonneg : 0 ≤ r := by
    simpa [h, r] using hessianLocalNorm_nonneg f x (y - x)
  have hτ_nonneg : 0 ≤ τ := hτ.1
  have hτr_le_r : τ * r ≤ r := by
    simpa using mul_le_mul_of_nonneg_right hτ.2 hr_nonneg
  have hτr_lt : τ * r < 1 / (Mf : ℝ) := lt_of_le_of_lt hτr_le_r hr
  have hscaled_lt : ‖τ • h‖[f; x] < 1 / (Mf : ℝ) := by
    rw [hessianLocalNorm_smul_of_nonneg (f := f) (z := x) (u := h) hτ_nonneg]
    exact hτr_lt
  have hz : x + τ • h ∈ dom := hstep hx hscaled_lt
  have hbound := htransport hx hz hscaled_lt
  constructor
  · exact hz
  · -- Rewrite the transport bound using the homogeneity of the local norm at the base point.
    simpa [h, r, hessianLocalNorm_smul_of_nonneg (f := f) (z := x) (u := h) hτ_nonneg,
      mul_assoc, mul_left_comm, mul_comm] using hbound

omit hf_C2 hstep htransport hquad_nonneg [CompleteSpace E] in
/-- Helper for Theorem 5.1.9: the affine line `s ↦ x + s • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

omit hf_C2 hstep htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: a pointwise `C²` hypothesis upgrades the gradient to a genuinely
Fréchet-differentiable map with derivative `hessian f z`. -/
private theorem gradient_hasFDerivAt_of_contDiffAt
    {z : E} (hz_C2 : ContDiffAt ℝ 2 f z) :
    HasFDerivAt (∇ f) (hessian f z) z := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) z := by
    have hC1_fderiv : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
      hz_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hC1_fderiv.differentiableAt one_ne_zero
  have hgradDiff : DifferentiableAt ℝ (∇ f) z := by
    -- Rewrite the gradient through the Riesz map before differentiating.
    simpa [gradient, D] using D.differentiableAt.comp z hfderiv
  -- The derivative of the gradient is the Hessian by definition.
  simpa [hessian] using hgradDiff.hasFDerivAt

omit hf_C2 htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: once the reciprocal Dikin radius is positive, the step axiom makes
the domain open. -/
private theorem dom_isOpen_of_step
    (hMf_pos : 0 < (Mf : ℝ)) :
    IsOpen dom := by
  refine Metric.isOpen_iff.2 ?_
  intro z hz
  have hcont_quad : Continuous fun u : E ↦ inner ℝ u (hessian f z u) := by
    continuity
  have hcont_norm : Continuous fun u : E ↦ ‖u‖[f; z] := by
    simpa [hessianLocalNorm_def] using Real.continuous_sqrt.comp hcont_quad
  have hzero : ‖(0 : E)‖[f; z] < 1 / (Mf : ℝ) := by
    simp [hessianLocalNorm_def, one_div, hMf_pos]
  have hsmall :
      {u : E | ‖u‖[f; z] < 1 / (Mf : ℝ)} ∈ nhds (0 : E) := by
    exact hcont_norm.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hzero)
  rcases Metric.mem_nhds_iff.1 hsmall with ⟨ε, hε_pos, hε⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro y hy
  have hy_sub : y - z ∈ Metric.ball (0 : E) ε := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hlt : ‖y - z‖[f; z] < 1 / (Mf : ℝ) := hε hy_sub
  have hz_mem : z + (y - z) ∈ dom := hstep hz hlt
  simpa using hz_mem

omit htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: on the resulting open domain, `C²` regularity makes the gradient
continuous. -/
private theorem gradient_continuousOn
    (hMf_pos : 0 < (Mf : ℝ)) :
    ContinuousOn (∇ f) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hdom_open : IsOpen dom := dom_isOpen_of_step (f := f) (Mf := Mf) hstep hMf_pos
  have hfd_cont : ContinuousOn (fderiv ℝ f) dom := by
    exact
      (hf_C2.fderiv_of_isOpen hdom_open
        (show (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) by norm_num)).continuousOn
  simpa [gradient, D] using D.continuous.comp_continuousOn hfd_cont

omit htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: on the same open domain, the Hessian varies continuously. -/
private theorem hessian_continuousOn
    (hMf_pos : 0 < (Mf : ℝ)) :
    ContinuousOn (hessian f) dom := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hdom_open : IsOpen dom := dom_isOpen_of_step (f := f) (Mf := Mf) hstep hMf_pos
  have hgrad_contDiff : ContDiffOn ℝ 1 (∇ f) dom := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ f) dom :=
      hf_C2.fderiv_of_isOpen hdom_open
        (show (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) by norm_num)
    simpa [gradient, D] using D.contDiff.comp_contDiffOn hfd
  simpa [hessian] using
    (hgrad_contDiff.fderiv_of_isOpen hdom_open
      (show (0 : WithTop ℕ∞) + 1 ≤ (1 : WithTop ℕ∞) by norm_num)).continuousOn

omit htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: differentiating `f` along an admissible affine line recovers the
gradient pairing with the line direction. -/
private theorem value_line_hasDerivAt
    (hMf_pos : 0 < (Mf : ℝ))
    {z d : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ f (z + s • d)) (inner ℝ (∇ f (z + t • d)) d) t := by
  have hdom_open : IsOpen dom := dom_isOpen_of_step (f := f) (Mf := Mf) hstep hMf_pos
  have hC1 : ContDiffAt ℝ 1 f (z + t • d) := by
    have hnhds : dom ∈ nhds (z + t • d) := hdom_open.mem_nhds hzt
    exact (hf_C2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt hnhds
  -- Differentiate the ambient function first and then compose with the affine line.
  simpa using
    ((hC1.differentiableAt one_ne_zero).hasGradientAt.hasFDerivAt.comp t
      (line_hasDerivAt z d t).hasFDerivAt).hasDerivAt

omit htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: scalarizing the gradient along an admissible affine line
differentiates to the corresponding Hessian pairing. -/
private theorem scalarized_gradient_line_hasDerivAt
    (hMf_pos : 0 < (Mf : ℝ))
    {z d w : E} {t : ℝ} (hzt : z + t • d ∈ dom) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (∇ f (z + s • d)) w)
      (inner ℝ (hessian f (z + t • d) d) w) t := by
  have hdom_open : IsOpen dom := dom_isOpen_of_step (f := f) (Mf := Mf) hstep hMf_pos
  have hz_C2 : ContDiffAt ℝ 2 f (z + t • d) := by
    exact hf_C2.contDiffAt (hdom_open.mem_nhds hzt)
  have hgradLine :
      HasFDerivAt (fun s : ℝ ↦ ∇ f (z + s • d))
        ((hessian f (z + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d)) t := by
    -- Route correction: differentiate the raw scalarized gradient line before subtracting any
    -- endpoint terms.
    simpa using
      ((gradient_hasFDerivAt_of_contDiffAt (f := f) hz_C2).comp t
        (line_hasDerivAt z d t).hasFDerivAt)
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) w
  have hscalar :
      HasFDerivAt (fun s : ℝ ↦ φ (∇ f (z + s • d)))
        (φ.comp ((hessian f (z + t • d)).comp (ContinuousLinearMap.toSpanSingleton ℝ d))) t := by
    -- Postcompose with the scalar functional `v ↦ ⟪v, w⟫`.
    simpa [φ] using ((φ.hasFDerivAt).comp t hgradLine)
  simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt

omit hf_C2 hstep htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: the rational Hessian majorant integrates to the expected
transport factor `u r² / (1 - M_f u r)`. -/
private theorem integral_sq_div_eq_scaled_sq_div
    {r u : ℝ} (hu : 0 ≤ u)
    (hden : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 - (Mf : ℝ) * t * r) :
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ) =
      u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
  let a : ℝ := (Mf : ℝ) * r
  have hden' : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 - t * a := by
    intro t ht
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using hden t ht
  have hnum : ContinuousOn (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - t * a))
      (Set.Icc (0 : ℝ) u) := by
    refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
    · exact (show Continuous (fun t : ℝ ↦ 1 - t * a) by continuity).continuousOn
    · intro t ht
      exact (hden' t ht).ne'
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ))
        MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ))
          (Set.Icc (0 : ℝ) u) := by
      refine continuousOn_const.div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ (1 - t * a) ^ (2 : ℕ)) by continuity).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (hden' t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        HasDerivAt
          (fun s : ℝ ↦ s * r ^ (2 : ℕ) / (1 - s * a))
          (r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) u := Set.mem_Icc_of_Ioo ht
    have hden_ne : 1 - t * a ≠ 0 := (hden' t ht').ne'
    have hden_deriv :
        HasDerivAt (fun s : ℝ ↦ 1 - s * a) (-a) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const a) using 1
      ring
    have hquot :=
      ((hasDerivAt_id t).mul_const (r ^ (2 : ℕ))).div hden_deriv hden_ne
    have hquot_slope :
        ((1 : ℝ) * r ^ (2 : ℕ) * (1 - t * a) - t * r ^ (2 : ℕ) * -a) /
            (1 - t * a) ^ (2 : ℕ) =
          r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ) := by
      field_simp [hden_ne]
      ring
    have hquot' :
        HasDerivAt (fun s : ℝ ↦ (s * r ^ (2 : ℕ)) / (1 - s * a))
          (((1 : ℝ) * r ^ (2 : ℕ) * (1 - t * a) - t * r ^ (2 : ℕ) * -a) /
            (1 - t * a) ^ (2 : ℕ)) t := by
      simpa using hquot
    exact hquot'.congr_deriv hquot_slope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hnum hderiv hint
  calc
    ∫ t in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ)
        = ∫ t in 0..u, r ^ (2 : ℕ) / (1 - t * a) ^ (2 : ℕ) := by
            congr with t
            simp [a, mul_left_comm, mul_comm]
    _
        = u * r ^ (2 : ℕ) / (1 - u * a) -
            (0 * r ^ (2 : ℕ) / (1 - 0 * a)) := by
              simpa using hftc
    _ = u * r ^ (2 : ℕ) / (1 - u * a) := by ring
    _ = u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
      simp [a, mul_left_comm, mul_comm]

omit hf_C2 hstep htransport hquad_nonneg in
/-- Helper for Theorem 5.1.9: the second scalar integration in the source proof evaluates to the
logarithmic `ω_*` antiderivative. -/
private theorem integral_mul_sq_div_eq_omega_star
    {r u : ℝ} (hu : 0 ≤ u) (hMf_pos : 0 < (Mf : ℝ))
    (hden : ∀ t ∈ Set.Icc (0 : ℝ) u, 0 < 1 - (Mf : ℝ) * t * r) :
    ∫ t in 0..u, t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) =
      (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
        (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
  let a : ℝ := (Mf : ℝ)
  have ha_ne : a ≠ 0 := ne_of_gt (by simpa [a] using hMf_pos)
  have hnum :
      ContinuousOn
        (fun t : ℝ ↦ (1 / (a ^ (2 : ℕ))) * (-(a * t * r) - Real.log (1 - a * t * r)))
        (Set.Icc (0 : ℝ) u) := by
    have hlog :
        ContinuousOn (fun t : ℝ ↦ Real.log (1 - a * t * r)) (Set.Icc (0 : ℝ) u) := by
      refine Real.continuousOn_log.comp ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 - a * t * r) by continuity).continuousOn
      · intro t ht
        simpa [a, mul_assoc, mul_left_comm, mul_comm] using (hden t ht).ne'
    have hlin :
        ContinuousOn (fun t : ℝ ↦ -(a * t * r)) (Set.Icc (0 : ℝ) u) := by
      exact (show Continuous (fun t : ℝ ↦ -(a * t * r)) by continuity).continuousOn
    -- Keep the antiderivative in the exact source-friendly scalar form.
    refine continuousOn_const.mul ?_
    exact hlin.sub hlog
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r))
        MeasureTheory.volume 0 u := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r))
          (Set.Icc (0 : ℝ) u) := by
      refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
      · exact (show Continuous (fun t : ℝ ↦ 1 - (Mf : ℝ) * t * r) by continuity).continuousOn
      · intro t ht
        exact (hden t ht).ne'
    exact hcont.intervalIntegrable_of_Icc hu
  have hderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) u,
        HasDerivAt
          (fun s : ℝ ↦
            (1 / (a ^ (2 : ℕ))) * (-(a * s * r) - Real.log (1 - a * s * r)))
          (t * r ^ (2 : ℕ) / (1 - a * t * r)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) u := Set.mem_Icc_of_Ioo ht
    have harg_ne : 1 - a * t * r ≠ 0 := by
      simpa [a, mul_assoc, mul_left_comm, mul_comm] using (hden t ht').ne'
    have harg :
        HasDerivAt (fun s : ℝ ↦ 1 - a * s * r) (-(a * r)) t := by
      convert
        (hasDerivAt_const t (1 : ℝ)).sub ((((hasDerivAt_id t).const_mul a).mul_const r)) using 1
      ring
    have hlog :
        HasDerivAt (fun s : ℝ ↦ Real.log (1 - a * s * r))
          ((-(a * r)) / (1 - a * t * r)) t := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Real.hasDerivAt_log harg_ne).comp t harg
    have hlin :
        HasDerivAt (fun s : ℝ ↦ -(a * s * r)) (-(a * r)) t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((((hasDerivAt_id t).const_mul a).mul_const r).neg)
    have hbase :
        HasDerivAt
          (fun s : ℝ ↦ -(a * s * r) - Real.log (1 - a * s * r))
          (-(a * r) - ((-(a * r)) / (1 - a * t * r))) t := by
      -- Differentiate the linear and logarithmic pieces separately before recombining them.
      exact hlin.sub hlog
    have hscaled :
        HasDerivAt
          (fun s : ℝ ↦
            (1 / (a ^ (2 : ℕ))) * (-(a * s * r) - Real.log (1 - a * s * r)))
          ((1 / (a ^ (2 : ℕ))) * (-(a * r) - ((-(a * r)) / (1 - a * t * r)))) t := by
      exact hbase.const_mul (1 / (a ^ (2 : ℕ)))
    have hslope :
        ((1 / (a ^ (2 : ℕ))) * (-(a * r) - ((-(a * r)) / (1 - a * t * r)))) =
          t * r ^ (2 : ℕ) / (1 - a * t * r) := by
      have hfrac :
          (1 - a * t * r)⁻¹ - 1 = (a * t * r) * (1 - a * t * r)⁻¹ := by
        field_simp [harg_ne]
        ring
      calc
        ((1 / (a ^ (2 : ℕ))) * (-(a * r) - ((-(a * r)) / (1 - a * t * r))))
            = (1 / (a ^ (2 : ℕ))) * (a * r) * ((1 - a * t * r)⁻¹ - 1) := by
                ring_nf
        _ = (1 / (a ^ (2 : ℕ))) * (a * r) * ((a * t * r) * (1 - a * t * r)⁻¹) := by
              rw [hfrac]
        _ = t * r ^ (2 : ℕ) / (1 - a * t * r) := by
              field_simp [ha_ne, harg_ne]
    exact hscaled.congr_deriv hslope
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu hnum hderiv hint
  calc
    ∫ t in 0..u, t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r)
        = ((1 / (a ^ (2 : ℕ))) * (-(a * u * r) - Real.log (1 - a * u * r))) -
            ((1 / (a ^ (2 : ℕ))) * (-(a * 0 * r) - Real.log (1 - a * 0 * r))) := by
              simpa [a, mul_assoc, mul_left_comm, mul_comm] using hftc
    _ = (1 / (a ^ (2 : ℕ))) * (-(a * u * r) - Real.log (1 - a * u * r)) := by
      simp
    _ = (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
          (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
      simp [a, mul_assoc, mul_comm]

-- Proof sketch: set `h := y - x` and `r := ‖h‖[f; x]`. For the gradient pairing, integrate
-- `τ ↦ inner ℝ h (hessian f (x + τ • h) h)` along the segment, use the admissible-step
-- hypothesis to keep the segment inside `dom`, apply the local-norm transport bound and
-- `hessianLocalNorm_def` pointwise together with `Real.sq_sqrt` using `hquad_nonneg`, and
-- evaluate the resulting scalar
-- integral `∫₀¹ r² / (1 - τ M_f r)²`. For the function-value estimate, integrate the first bound
-- once more along the same segment and compute
-- `∫₀¹ τ r² / (1 - τ M_f r) = M_f⁻² ω_*(M_f r)`.
/-- Theorem 5.1.9: if `f` is `C²` on `dom` and every admissible local step `h` from a point
`x ∈ dom` stays in `dom`, satisfies the local-norm transport bound
`‖h‖[f; x + h] ≤ ‖h‖[f; x] / (1 - M_f ‖h‖[f; x])`, and has nonnegative Hessian quadratic form at
the endpoint, then every admissible Dikin step `y ∈ W⁰[f; x](1 / M_f)` satisfies the gradient
pairing and first-order Taylor upper bounds from the textbook statement. -/
theorem localNorm_gradient_pairing_and_value_upper_bounds_of_transport_data
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    inner ℝ (∇ f y - ∇ f x) (y - x) ≤
        r ^ (2 : ℕ) / (1 - (Mf : ℝ) * r) ∧
      f y ≤
        f x + inner ℝ (∇ f x) (y - x) +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := by
  let h := y - x
  let r := ‖h‖[f; x]
  have hr : r < 1 / (Mf : ℝ) := by
    simpa [h, r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy
  have hr_nonneg : 0 ≤ r := by
    simpa [h, r] using hessianLocalNorm_nonneg f x (y - x)
  have hMf_pos : 0 < (Mf : ℝ) :=
    mf_pos_of_mem_openDikinEllipsoid (f := f) (Mf := Mf) hxy
  have hy : y ∈ dom := by
    -- The endpoint is itself the `τ = 1` segment point, so the admissible-step hypothesis
    -- already puts it back in `dom`.
    have hstep_mem :
        x + (1 : ℝ) • h ∈ dom := by
      exact
        (segment_step_mem_dom_and_scaled_transport
          (f := f) (Mf := Mf) hstep htransport hx hxy (τ := 1) (by simp)).1
    dsimp [h] at hstep_mem
    simpa using hstep_mem
  have hsegment :
      ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) 1 →
        x + τ • h ∈ dom ∧
          ‖τ • h‖[f; x + τ • h] ≤ (τ * r) / (1 - (Mf : ℝ) * τ * r) := by
    intro τ hτ
    simpa [h, r] using
      (segment_step_mem_dom_and_scaled_transport
        (f := f) (Mf := Mf) hstep htransport hx hxy (τ := τ) hτ)
  -- The transport side is now stabilized: every segment point is in `dom`, and the admissible
  -- step `τ • h` satisfies the exact rescaled transport inequality. The remaining proof follows
  -- the source route by integrating this Hessian majorant twice along the affine segment.
  let g : ℝ → ℝ := fun u ↦ inner ℝ (∇ f (x + u • h)) h
  let φ : ℝ → ℝ := fun u ↦ f (x + u • h)
  let ψ : ℝ → ℝ := fun u ↦ inner ℝ (∇ f (x + u • h) - ∇ f x) h
  let Φ : ℝ → ℝ := fun u ↦ f (x + u • h) - f x - u * inner ℝ (∇ f x) h
  -- Route correction: previous attempts stopped at the transport scaffold; the source proof now
  -- continues by integrating the exact Hessian majorant twice along the segment.
  have hden_on :
      ∀ {u t : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) u →
        0 < 1 - (Mf : ℝ) * t * r := by
    intro u t hu ht
    have htr_le : t * r ≤ r := by
      have htle1 : t ≤ 1 := le_trans ht.2 hu.2
      simpa using mul_le_mul_of_nonneg_right htle1 hr_nonneg
    have htr_lt : t * r < 1 / (Mf : ℝ) := lt_of_le_of_lt htr_le hr
    have hmfr_lt : (Mf : ℝ) * (t * r) < 1 := mf_mul_lt_one_of_lt_inv (Mf := Mf) htr_lt
    simpa [mul_assoc, mul_left_comm, mul_comm] using sub_pos.2 hmfr_lt
  -- The Hessian quadratic form along the open segment is dominated by the transported rational
  -- majorant from the source formula.
  have segment_hessian_quadratic_upper_of_transport :
      ∀ {τ : ℝ}, τ ∈ Set.Ioo (0 : ℝ) 1 →
        inner ℝ h (hessian f (x + τ • h) h) ≤
          r ^ (2 : ℕ) / (1 - (Mf : ℝ) * τ * r) ^ (2 : ℕ) := by
    intro τ hτ
    have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc_of_Ioo hτ
    have hz : x + τ • h ∈ dom := (hsegment hτIcc).1
    have hτ_nonneg : 0 ≤ τ := hτ.1.le
    have hτr_lt : τ * r < 1 / (Mf : ℝ) := by
      have hτr_le : τ * r ≤ r := by
        simpa using mul_le_mul_of_nonneg_right hτIcc.2 hr_nonneg
      exact lt_of_le_of_lt hτr_le hr
    have hscaled_lt : ‖τ • h‖[f; x] < 1 / (Mf : ℝ) := by
      rw [hessianLocalNorm_smul_of_nonneg (f := f) (z := x) (u := h) hτ_nonneg]
      exact hτr_lt
    have hquad_scaled :
        0 ≤ inner ℝ (τ • h) (hessian f (x + τ • h) (τ • h)) :=
      hquad_nonneg hx hz hscaled_lt
    have hden_pos : 0 < 1 - (Mf : ℝ) * τ * r := hden_on hτIcc ⟨hτ.1.le, le_rfl⟩
    have hnorm_bound :
        ‖τ • h‖[f; x + τ • h] ≤ (τ * r) / (1 - (Mf : ℝ) * τ * r) :=
      (hsegment hτIcc).2
    have hnorm_sq_bound :
        ‖τ • h‖[f; x + τ • h] ^ (2 : ℕ) ≤
          ((τ * r) / (1 - (Mf : ℝ) * τ * r)) ^ (2 : ℕ) := by
      have hright_nonneg : 0 ≤ (τ * r) / (1 - (Mf : ℝ) * τ * r) := by
        exact div_nonneg (mul_nonneg hτ_nonneg hr_nonneg) hden_pos.le
      nlinarith [hessianLocalNorm_nonneg f (x + τ • h) (τ • h), hnorm_bound, hright_nonneg]
    have hsq_eq :
        ‖τ • h‖[f; x + τ • h] ^ (2 : ℕ) =
          inner ℝ (τ • h) (hessian f (x + τ • h) (τ • h)) := by
      simpa using
        sq_hessianLocalNorm_eq_inner_of_nonneg
          (f := f) (z := x + τ • h) (u := τ • h) hquad_scaled
    have hscaled_ineq :
        inner ℝ (τ • h) (hessian f (x + τ • h) (τ • h)) ≤
          ((τ * r) / (1 - (Mf : ℝ) * τ * r)) ^ (2 : ℕ) := by
      calc
        inner ℝ (τ • h) (hessian f (x + τ • h) (τ • h)) =
            ‖τ • h‖[f; x + τ • h] ^ (2 : ℕ) := by
              symm
              exact hsq_eq
        _ ≤ ((τ * r) / (1 - (Mf : ℝ) * τ * r)) ^ (2 : ℕ) := hnorm_sq_bound
    have hscaled_ineq' :
        (τ ^ (2 : ℕ)) * inner ℝ h (hessian f (x + τ • h) h) ≤
          (τ ^ (2 : ℕ)) * (r ^ (2 : ℕ) / (1 - (Mf : ℝ) * τ * r) ^ (2 : ℕ)) := by
      simpa [pow_two, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm,
        div_eq_mul_inv] using hscaled_ineq
    have hfinal :
        inner ℝ h (hessian f (x + τ • h) h) ≤
          r ^ (2 : ℕ) / (1 - (Mf : ℝ) * τ * r) ^ (2 : ℕ) := by
      have hτsq_pos : 0 < τ ^ (2 : ℕ) := by
        nlinarith [hτ.1]
      nlinarith [hscaled_ineq', hτsq_pos]
    exact hfinal
  let θ : ℝ → ℝ := fun u ↦ inner ℝ (hessian f (x + u • h) h) h
  change
    inner ℝ (∇ f y - ∇ f x) h ≤ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * r) ∧
      f y ≤
        f x + inner ℝ (∇ f x) h +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r))
  have hdom_open : IsOpen dom :=
    dom_isOpen_of_step (f := f) (Mf := Mf) hstep hMf_pos
  -- Route correction: package the raw line continuity once, then reuse it in both FTC layers.
  have segment_gradient_line_continuousOn :
      ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hz : x + u • h ∈ dom := (hsegment hu).1
    exact
      (scalarized_gradient_line_hasDerivAt
        (f := f) (dom := dom) (Mf := Mf) hf_C2 hstep hMf_pos
        (z := x) (d := h) (w := h) (t := u) hz).continuousAt.continuousWithinAt
  -- The scalar Hessian pairing is continuous on every truncated segment and hence integrable.
  have segment_hessian_pairing_intervalIntegrable :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        IntervalIntegrable θ MeasureTheory.volume 0 u := by
    intro u hu
    have hcont :
        ContinuousOn θ (Set.Icc (0 : ℝ) u) := by
      intro t ht
      have hz : x + t • h ∈ dom := (hsegment ⟨ht.1, le_trans ht.2 hu.2⟩).1
      have hhess_on : ContinuousOn (hessian f) dom :=
        hessian_continuousOn (f := f) (dom := dom) (Mf := Mf) hf_C2 hstep hMf_pos
      have hhess_cont : ContinuousAt (hessian f) (x + t • h) :=
        hhess_on.continuousAt (hdom_open.mem_nhds hz)
      have hline_cont : ContinuousAt (fun s : ℝ ↦ x + s • h) t :=
        (line_hasDerivAt x h t).continuousAt
      have hhess_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • h)) t := by
        exact ContinuousAt.comp hhess_cont hline_cont
      let φh : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) h
      have happly_line : ContinuousAt (fun s : ℝ ↦ hessian f (x + s • h) h) t := by
        simpa using
          ContinuousAt.comp ((ContinuousLinearMap.apply ℝ E h).continuous.continuousAt) hhess_line
      have hinner_cont : ContinuousAt θ t := by
        simpa [θ, φh, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
          ContinuousAt.comp φh.continuous.continuousAt happly_line
      exact hinner_cont.continuousWithinAt
    exact hcont.intervalIntegrable_of_Icc hu.1
  -- The first FTC layer identifies the gradient-pairing increment with the Hessian integral.
  have segment_gradient_pairing_eq_integral :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        ψ u = ∫ s in 0..u, θ s := by
    intro u hu
    have hg_cont :
        ContinuousOn g (Set.Icc (0 : ℝ) u) :=
      segment_gradient_line_continuousOn.mono
        (by
          intro t ht
          exact ⟨ht.1, le_trans ht.2 hu.2⟩)
    have hderiv :
        ∀ t ∈ Set.Ioo (0 : ℝ) u, HasDerivAt g (θ t) t := by
      intro t ht
      have hz : x + t • h ∈ dom := (hsegment ⟨ht.1.le, le_of_lt (lt_of_lt_of_le ht.2 hu.2)⟩).1
      simpa [g, θ] using
        (scalarized_gradient_line_hasDerivAt
          (f := f) (dom := dom) (Mf := Mf) hf_C2 hstep hMf_pos
          (z := x) (d := h) (w := h) (t := t) hz)
    have hftc :
        ∫ s in 0..u, θ s = g u - g 0 := by
      simpa using
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
          hu.1 hg_cont hderiv (segment_hessian_pairing_intervalIntegrable hu)
    calc
      ψ u = g u - g 0 := by
        simp [ψ, g, inner_sub_left]
      _ = ∫ s in 0..u, θ s := by
        symm
        exact hftc
  -- Compare the exact Hessian integral to the rational transport majorant from the source proof.
  have segment_gradient_pairing_upper_of_transport :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        ψ u ≤ u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
    intro u hu
    have hint_upper :
        IntervalIntegrable
          (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ))
          MeasureTheory.volume 0 u := by
      have hcont :
          ContinuousOn
            (fun t : ℝ ↦ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ))
            (Set.Icc (0 : ℝ) u) := by
        have hden_cont : Continuous (fun t : ℝ ↦ (1 - (Mf : ℝ) * t * r) ^ (2 : ℕ)) := by
          continuity
        refine continuousOn_const.div ?_ ?_
        · exact hden_cont.continuousOn
        · intro t ht
          exact pow_ne_zero 2 (hden_on hu ht).ne'
      exact hcont.intervalIntegrable_of_Icc hu.1
    have hmono :
        ∫ s in 0..u, θ s ≤
          ∫ s in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) ^ (2 : ℕ) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hu.1
        (segment_hessian_pairing_intervalIntegrable hu) hint_upper ?_
      intro s hs
      simpa [θ, real_inner_comm] using
        (segment_hessian_quadratic_upper_of_transport
          (τ := s) ⟨hs.1, lt_of_lt_of_le hs.2 hu.2⟩)
    calc
      ψ u = ∫ s in 0..u, θ s := segment_gradient_pairing_eq_integral hu
      _ ≤ ∫ s in 0..u, r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) ^ (2 : ℕ) := hmono
      _ = u * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * u * r) := by
        exact integral_sq_div_eq_scaled_sq_div (Mf := Mf) hu.1 (hden := fun t ht ↦ hden_on hu ht)
  -- Package the value line once so the second FTC layer only has to rewrite the affine term.
  have segment_value_line_continuousOn :
      ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    have hz : x + u • h ∈ dom := (hsegment hu).1
    exact
      (value_line_hasDerivAt
        (f := f) (dom := dom) (Mf := Mf) hf_C2 hstep hMf_pos
        (z := x) (d := h) (t := u) hz).continuousAt.continuousWithinAt
  have segment_gradient_pairing_continuousOn :
      ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    have hconst : ContinuousOn (fun _ : ℝ ↦ inner ℝ (∇ f x) h) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const
    simpa [ψ, g, inner_sub_left] using segment_gradient_line_continuousOn.sub hconst
  -- The second FTC layer integrates the gradient-pairing remainder to recover the value remainder.
  have segment_value_remainder_eq_integral :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        Φ u = ∫ s in 0..u, ψ s := by
    intro u hu
    have hφ_cont :
        ContinuousOn φ (Set.Icc (0 : ℝ) u) :=
      segment_value_line_continuousOn.mono
        (by
          intro t ht
          exact ⟨ht.1, le_trans ht.2 hu.2⟩)
    have hderiv :
        ∀ t ∈ Set.Ioo (0 : ℝ) u, HasDerivAt φ (g t) t := by
      intro t ht
      have hz : x + t • h ∈ dom := (hsegment ⟨ht.1.le, le_of_lt (lt_of_lt_of_le ht.2 hu.2)⟩).1
      simpa [φ, g] using
        (value_line_hasDerivAt
          (f := f) (dom := dom) (Mf := Mf) hf_C2 hstep hMf_pos
          (z := x) (d := h) (t := t) hz)
    have hintg :
        IntervalIntegrable g MeasureTheory.volume 0 u := by
      exact
        (segment_gradient_line_continuousOn.mono
          (by
            intro t ht
            exact ⟨ht.1, le_trans ht.2 hu.2⟩)).intervalIntegrable_of_Icc hu.1
    have hconst :
        IntervalIntegrable (fun _ : ℝ ↦ g 0) MeasureTheory.volume 0 u :=
      intervalIntegrable_const
    have hftc :
        ∫ s in 0..u, g s = φ u - φ 0 := by
      simpa using
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.1 hφ_cont hderiv hintg
    calc
      Φ u = φ u - φ 0 - u * g 0 := by
        simp [Φ, φ, g]
      _ = (∫ s in 0..u, g s) - u * g 0 := by
        rw [hftc]
      _ = (∫ s in 0..u, g s) - (∫ s in 0..u, g 0) := by
        rw [intervalIntegral.integral_const]
        ring
      _ = (∫ s in 0..u, (g s - g 0)) := by
        symm
        simpa using (intervalIntegral.integral_sub hintg hconst)
      _ = (∫ s in 0..u, ψ s) := by
        refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro s
        simp [ψ, g, inner_sub_left]
  -- Integrate the already established gradient-pairing majorant to recover the `ω_*` remainder.
  have segment_value_upper_of_transport :
      ∀ {u : ℝ}, u ∈ Set.Icc (0 : ℝ) 1 →
        Φ u ≤
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
    intro u hu
    have hintψ :
        IntervalIntegrable ψ MeasureTheory.volume 0 u := by
      exact
        (segment_gradient_pairing_continuousOn.mono
          (by
            intro t ht
            exact ⟨ht.1, le_trans ht.2 hu.2⟩)).intervalIntegrable_of_Icc hu.1
    have hint_upper :
        IntervalIntegrable
          (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r))
          MeasureTheory.volume 0 u := by
      have hcont :
          ContinuousOn
            (fun t : ℝ ↦ t * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * t * r))
            (Set.Icc (0 : ℝ) u) := by
        have hden_cont : Continuous (fun t : ℝ ↦ 1 - (Mf : ℝ) * t * r) := by
          exact continuous_const.sub ((continuous_const.mul continuous_id).mul continuous_const)
        refine (continuousOn_id.mul continuousOn_const).div ?_ ?_
        · exact hden_cont.continuousOn
        · intro t ht
          exact (hden_on hu ht).ne'
      exact hcont.intervalIntegrable_of_Icc hu.1
    have value_remainder_integral_upper_of_transport :
        ∫ s in 0..u, ψ s ≤
          ∫ s in 0..u, s * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) := by
      -- Compare the exact second-FTC integrand with the scalar transport majorant pointwise.
      refine intervalIntegral.integral_mono_on hu.1 hintψ hint_upper ?_
      intro s hs
      exact
        segment_gradient_pairing_upper_of_transport
          (u := s) ⟨hs.1, le_trans hs.2 hu.2⟩
    -- Finish the second FTC layer by evaluating the dominating scalar antiderivative.
    calc
      Φ u = ∫ s in 0..u, ψ s := segment_value_remainder_eq_integral hu
      _ ≤ ∫ s in 0..u, s * r ^ (2 : ℕ) / (1 - (Mf : ℝ) * s * r) :=
        value_remainder_integral_upper_of_transport
      _ =
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * (u * r) - Real.log (1 - (Mf : ℝ) * (u * r))) := by
              exact integral_mul_sq_div_eq_omega_star
                (Mf := Mf) hu.1 hMf_pos (hden := fun t ht ↦ hden_on hu ht)
  -- Specialize the parameterized bounds at `u = 1`, where the affine line reaches `y`.
  have hy_line : x + (1 : ℝ) • h = y := by
    dsimp [h]
    simp [sub_eq_add_neg]
  have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨by norm_num, le_rfl⟩
  constructor
  · have hgrad_endpoint : ψ 1 ≤ r ^ (2 : ℕ) / (1 - (Mf : ℝ) * r) := by
      simpa using (segment_gradient_pairing_upper_of_transport (u := 1) h1Icc)
    have hψ1 : ψ 1 = inner ℝ (∇ f y - ∇ f x) (y - x) := by
      dsimp [ψ, h]
      rw [hy_line]
    rw [← hψ1]
    exact hgrad_endpoint
  · have hvalue_endpoint_raw := segment_value_upper_of_transport (u := 1) h1Icc
    have hrem :
        f y - f x - inner ℝ (∇ f x) h ≤
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
            (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := by
      have hvalue_endpoint' :
          f y - f x - inner ℝ (∇ f x) h ≤
            (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
              (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := by
        have hΦ1 : Φ 1 = f y - f x - inner ℝ (∇ f x) h := by
          dsimp [Φ, φ]
          rw [hy_line]
          ring
        have hvalue_endpoint_one := hvalue_endpoint_raw
        rw [one_mul] at hvalue_endpoint_one
        rw [← hΦ1]
        exact hvalue_endpoint_one
      exact hvalue_endpoint'
    have hstep1 :
        f y - f x ≤
          inner ℝ (∇ f x) h +
            (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
              (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) :=
      (sub_le_iff_le_add').1 hrem
    have hstep2 :
        f y ≤
          f x + (inner ℝ (∇ f x) h +
            (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
              (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r))) :=
      (sub_le_iff_le_add').1 hstep1
    have hadd_assoc :
        f x + inner ℝ (∇ f x) h +
            (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
              (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) =
          f x + (inner ℝ (∇ f x) h +
            (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
              (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r))) :=
      add_assoc _ _ _
    rw [hadd_assoc]
    exact hstep2

end

namespace IsSelfConcordantOnWith

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: feed the source-facing Theorem 5.1.9 with the canonical owner data already
-- available from `IsSelfConcordantOnWith dom Mf f` and Theorem 5.1.5: `C²` regularity comes from
-- `contDiffOn`, admissible steps stay in `dom` by `openDikinEllipsoid_inv_constant_subset`, the
-- local-norm transport bound is `displacement_localNorm_upper_bound`, and Hessian
-- positive-semidefiniteness is `hessian_posSemidef`.
/-- Under the Chapter 5 owner `IsSelfConcordantOnWith dom Mf f`, every admissible Dikin step
satisfies the gradient-pairing and first-order Taylor upper bounds from Theorem 5.1.9. This is
the canonical owner-level bridge from self-concordance to the source-facing local estimate. -/
theorem localNorm_gradient_pairing_and_value_upper_bounds
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let τω := selfConcordantOmegaStarArg Mf r (by
      exact mf_mul_lt_one_of_lt_inv <|
        by simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy)
    inner ℝ (∇ f y - ∇ f x) (y - x) ≤
        r ^ (2 : ℕ) / (1 - (Mf : ℝ) * r) ∧
      f y ≤
        f x + inner ℝ (∇ f x) (y - x) +
          (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* τω := by
  let hf_C2 : ContDiffOn ℝ 2 f dom := hself.contDiffOn.of_le (by norm_num)
  let hstep :
      ∀ ⦃x h : E⦄, x ∈ dom → ‖h‖[f; x] < 1 / (Mf : ℝ) → x + h ∈ dom :=
    fun {x h} hx hh ↦
      (openDikinEllipsoid_inv_constant_subset hself hx)
        ((mem_openDikinEllipsoid_iff f x (x + h) (1 / (Mf : ℝ))).2 (by simpa using hh))
  let htransport :
      ∀ ⦃x h : E⦄, x ∈ dom → x + h ∈ dom →
        ‖h‖[f; x] < 1 / (Mf : ℝ) →
          ‖h‖[f; x + h] ≤ ‖h‖[f; x] / (1 - (Mf : ℝ) * ‖h‖[f; x]) :=
    fun {x h} hx _ hh ↦
      by
        simpa using
          displacement_localNorm_upper_bound hself hx
            ((mem_openDikinEllipsoid_iff f x (x + h) (1 / (Mf : ℝ))).2 (by simpa using hh))
  let hquad_nonneg :
      ∀ ⦃x h : E⦄, x ∈ dom → x + h ∈ dom →
        ‖h‖[f; x] < 1 / (Mf : ℝ) →
          0 ≤ inner ℝ h (hessian f (x + h) h) :=
    fun {x h} _ hxh _ ↦ hself.hessian_posSemidef hxh h
  let r := ‖y - x‖[f; x]
  let τω := selfConcordantOmegaStarArg Mf r (by
    exact mf_mul_lt_one_of_lt_inv <|
      by simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy)
  have hmain :
      inner ℝ (∇ f y - ∇ f x) (y - x) ≤
          r ^ (2 : ℕ) / (1 - (Mf : ℝ) * r) ∧
        f y ≤
          f x + inner ℝ (∇ f x) (y - x) +
            (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
              (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := by
    simpa [r] using
      (localNorm_gradient_pairing_and_value_upper_bounds_of_transport_data
        hf_C2 hstep htransport hquad_nonneg hx hxy)
  have hτω : ↑τω = (Mf : ℝ) * r := by
    simp [τω]
  constructor
  · exact hmain.1
  · calc
      f y ≤
          f x + inner ℝ (∇ f x) (y - x) +
            (1 / ((Mf : ℝ) ^ (2 : ℕ))) *
              (-(Mf : ℝ) * r - Real.log (1 - (Mf : ℝ) * r)) := hmain.2
      _ =
          f x + inner ℝ (∇ f x) (y - x) +
            (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* τω := by
              rw [selfConcordantOmegaStar_apply, hτω]
              ring

-- Proof sketch: project the first component of the owner-level theorem above.
/-- The owner-level gradient-pairing upper bound derived from `IsSelfConcordantOnWith dom Mf f`
and the admissible Dikin-step hypothesis. -/
theorem localNorm_gradient_pairing_upper_bound
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    inner ℝ (∇ f y - ∇ f x) (y - x) ≤
      ‖y - x‖[f; x] ^ (2 : ℕ) / (1 - (Mf : ℝ) * ‖y - x‖[f; x]) := by
  simpa using
    (localNorm_gradient_pairing_and_value_upper_bounds
      hself hx hxy).1

-- Proof sketch: project the second component of the owner-level theorem above.
/-- The owner-level Taylor upper bound with remainder `ω_*`, derived from
`IsSelfConcordantOnWith dom Mf f` and the admissible Dikin-step hypothesis. -/
theorem localNorm_taylor_upper_bound_with_selfConcordantOmegaStar
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let τω := selfConcordantOmegaStarArg Mf r (by
      exact mf_mul_lt_one_of_lt_inv <|
        by simpa [r] using (mem_openDikinEllipsoid_iff f x y (1 / (Mf : ℝ))).1 hxy)
    f y ≤
      f x + inner ℝ (∇ f x) (y - x) +
        (1 / ((Mf : ℝ) ^ (2 : ℕ))) * ω_* τω := by
  simpa using
    (localNorm_gradient_pairing_and_value_upper_bounds
      hself hx hxy).2

end

end IsSelfConcordantOnWith

end
