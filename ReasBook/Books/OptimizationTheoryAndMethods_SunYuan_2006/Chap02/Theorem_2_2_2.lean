/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1

open Filter InnerProductSpace
open scoped Gradient

-- Domain sampling:
-- * source-facing owners: Chapter01 `IsDescentDirectionAt` for the descent-direction
--   hypothesis and Chapter02 `lineSearchObjective` /
--   `IsExactLineSearchStepOnNonnegativeRay` for one-dimensional exact line search;
-- * core/canonical regularity owners in nearby Chapter 2 files: local `ContDiffOn ℝ 2 f D`
--   on a set containing the traced segment and the derived Hessian operator `fderiv ℝ (∇ f)`;
-- * bridge/view: Chapter02 `cos_angle_searchDirection_negGradient` rewrites the cosine term
--   into the dot-product form when needed.
-- Primitive data are therefore the descent direction at `xk`, the exact line-search step, a
-- local domain `D` containing the traced segment from `xk` to `xk + αk • dk`, `C²` regularity
-- on `D`, and the Hessian norm bound on `D`; the pointwise `HasGradientAt`/`HasFDerivAt` facts
-- along the ray are derived API from that owner abstraction rather than primitive public
-- assumptions here.

section Theorem222

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [CompleteSpace Point]

/-- Helper for Chapter02 Theorem 2.2.2: an exact line-search step on the nonnegative ray is
strictly positive when the search direction is genuinely descending at the base point. -/
lemma exactLineSearchStep_pos_of_descent
    (f : Point → ℝ) (xk dk : Point) (αk : ℝ)
    (h_descent : IsDescentDirectionAt f xk dk)
    (h_exactLineSearch : IsExactLineSearchStepOnNonnegativeRay f xk dk αk) :
    0 < αk := by
  -- Use the strict local decrease supplied by the descent direction to rule out the endpoint `0`.
  rcases h_descent.exists_localDecrease_lineSearchObjective with ⟨δ, hδ, hDecrease⟩
  by_contra hαk
  have hαk_eq_zero : αk = 0 := by
    linarith [h_exactLineSearch.nonneg]
  have hδhalf_nonneg : 0 ≤ δ / 2 := by positivity
  have hExactAtHalf :
      lineSearchObjective f xk dk αk ≤ lineSearchObjective f xk dk (δ / 2) :=
    h_exactLineSearch.optimal hδhalf_nonneg
  have hStrictAtHalf :
      lineSearchObjective f xk dk (δ / 2) < lineSearchObjective f xk dk 0 := by
    refine hDecrease (δ / 2) ?_ ?_
    · positivity
    · linarith
  rw [hαk_eq_zero] at hExactAtHalf
  linarith

omit [CompleteSpace Point] in
/-- Helper for Chapter02 Theorem 2.2.2: every scaled point `xk + (t * α) • dk` with
`0 ≤ α ≤ αk` and `t ∈ [0, 1]` lies on the segment from `xk` to `xk + αk • dk`. -/
lemma scaledSearchRay_mem_segment_of_nonneg_le_step
    (xk dk : Point) {αk α t : ℝ}
    (hαk : 0 < αk)
    (hα_nonneg : 0 ≤ α)
    (hα_le : α ≤ αk)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    xk + (t * α) • dk ∈ segment ℝ xk (xk + αk • dk) := by
  -- Reparameterize the point by the affine line map between the segment endpoints.
  rw [segment_eq_image_lineMap]
  refine ⟨(t * α) / αk, ?_, ?_⟩
  · constructor
    · exact div_nonneg (mul_nonneg ht.1 hα_nonneg) hαk.le
    · refine (div_le_one hαk).2 ?_
      nlinarith [ht.2, hα_le]
  · have hmul : ((t * α) / αk) * αk = t * α := by
      field_simp [hαk.ne']
    calc
      AffineMap.lineMap xk (xk + αk • dk) ((t * α) / αk)
          = xk + ((t * α) / αk) • ((xk + αk • dk) - xk) := by
            simp [AffineMap.lineMap_apply_module, sub_eq_add_neg, add_smul, smul_add,
              add_assoc, add_left_comm, add_comm]
      _ = xk + ((t * α) / αk) • (αk • dk) := by simp
      _ = xk + (((t * α) / αk) * αk) • dk := by rw [smul_smul]
      _ = xk + (t * α) • dk := by rw [hmul]

/-- Helper for Chapter02 Theorem 2.2.2: if `0 ≤ α ≤ αk`, then the shorter search segment from
`xk` to `xk + α • dk` is contained in the exact-step segment from `xk` to `xk + αk • dk`. -/
lemma searchRay_segment_subset_of_nonneg_le_step
    (xk dk : Point) {αk α : ℝ}
    (hαk : 0 < αk)
    (hα_nonneg : 0 ≤ α)
    (hα_le : α ≤ αk) :
    segment ℝ xk (xk + α • dk) ⊆ segment ℝ xk (xk + αk • dk) := by
  -- Reparameterize any point on the shorter segment by the longer search segment.
  intro z hz
  rw [segment_eq_image' ℝ xk (xk + α • dk)] at hz
  rcases hz with ⟨t, ht, rfl⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_smul, mul_comm,
    mul_left_comm, mul_assoc] using
    scaledSearchRay_mem_segment_of_nonneg_le_step xk dk hαk hα_nonneg hα_le ht

/-- Helper for Chapter02 Theorem 2.2.2: the affine unit-interval trace
`t ↦ x + t • (α • d)` has constant derivative `α • d`. -/
lemma unitIntervalTraceHasDerivAt (x d : Point) (α t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • (α • d)) (α • d) t := by
  -- Differentiate the affine trace directly.
  simpa [one_smul] using ((hasDerivAt_id' t).smul_const (α • d)).const_add x

/-- Helper for Chapter02 Theorem 2.2.2: the affine unit-interval trace of the search ray is
`C²`. -/
lemma unitIntervalTraceContDiff (x d : Point) (α : ℝ) :
    ContDiff ℝ 2 (fun t : ℝ ↦ x + t • (α • d)) := by
  -- The trace is the sum of a constant map and a linear map.
  simpa using contDiff_const.add (contDiff_id.smul_const (α • d))

/-- Helper for Chapter02 Theorem 2.2.2: the unit-interval trace of the step `α • d` stays in
any domain containing the segment from `x` to `x + α • d`. -/
lemma unitIntervalTraceMapsToDomain
    {D : Set Point} (x d : Point) (α : ℝ)
    (h_segment : segment ℝ x (x + α • d) ⊆ D) :
    Set.MapsTo (fun t : ℝ ↦ x + t • (α • d)) (Set.uIcc (0 : ℝ) 1) D := by
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le zero_le_one] using ht
  -- Rewrite the trace point in the standard segment parametrization.
  have htrace_mem : x + t • (α • d) ∈ segment ℝ x (x + α • d) := by
    rw [segment_eq_image' ℝ x (x + α • d)]
    refine ⟨t, ht', ?_⟩
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_smul]
  exact h_segment htrace_mem

/-- Helper for Chapter02 Theorem 2.2.2: composing `f` with the unit-interval trace gives a
`C²` scalar profile on `[0, 1]`. -/
lemma unitIntervalTraceContDiffOn
    {D : Set Point} (f : Point → ℝ) (x d : Point) (α : ℝ)
    (h_segment : segment ℝ x (x + α • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D) :
    ContDiffOn ℝ 2 (lineSearchObjective f x (α • d)) (Set.uIcc (0 : ℝ) 1) := by
  -- Compose the ambient `C²` objective with the smooth affine trace.
  change ContDiffOn ℝ 2 (f ∘ fun t : ℝ ↦ x + t • (α • d)) (Set.uIcc (0 : ℝ) 1)
  exact hC2.comp (unitIntervalTraceContDiff x d α).contDiffOn
    (unitIntervalTraceMapsToDomain x d α h_segment)

/-- Helper for Chapter02 Theorem 2.2.2: the first derivative of the rescaled line-search profile
at `0` is `α * ⟪∇ f x, d⟫`. -/
lemma unitIntervalTraceFirstIteratedDerivZero
    {D : Set Point} (f : Point → ℝ) (x d : Point) (α : ℝ)
    (hD : IsOpen D)
    (h_segment : segment ℝ x (x + α • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D) :
    iteratedDerivWithin 1 (lineSearchObjective f x (α • d)) (Set.uIcc (0 : ℝ) 1) 0 =
      α * inner ℝ (∇ f x) d := by
  let φ : ℝ → ℝ := lineSearchObjective f x (α • d)
  have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have h0_mem : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    exact Set.mem_uIcc_of_le le_rfl zero_le_one
  have hx_mem : x ∈ D := by
    simpa using unitIntervalTraceMapsToDomain x d α h_segment h0_mem
  have hφ_contDiffAt : ContDiffAt ℝ 2 φ 0 := by
    -- Openness upgrades the on-domain `C²` hypothesis to a pointwise `C²` fact at the base point.
    have hf_contDiffAt : ContDiffAt ℝ 2 f x := hC2.contDiffAt (hD.mem_nhds hx_mem)
    have hf_contDiffAt' : ContDiffAt ℝ 2 f (x + (0 : ℝ) • (α • d)) := by
      simpa [zero_smul] using hf_contDiffAt
    change ContDiffAt ℝ 2 (f ∘ fun t : ℝ ↦ x + t • (α • d)) 0
    simpa [zero_smul] using
      hf_contDiffAt'.comp 0 (unitIntervalTraceContDiff x d α).contDiffAt
  have hx_diff : DifferentiableAt ℝ f x :=
    hC2.contDiffAt (hD.mem_nhds hx_mem) |>.differentiableAt (by norm_num)
  calc
    iteratedDerivWithin 1 φ (Set.uIcc (0 : ℝ) 1) 0 = iteratedDeriv 1 φ 0 := by
      exact iteratedDerivWithin_eq_iteratedDeriv hs (hφ_contDiffAt.of_le (by norm_num)) h0_mem
    _ = deriv φ 0 := by simp [iteratedDeriv_one]
    _ = α * inner ℝ (∇ f x) d := by
      simpa [φ, real_inner_comm, inner_smul_right, zero_smul, lineSearchObjective_apply] using
        deriv_lineSearchObjective_apply f x (α • d) 0 (by simpa [zero_smul] using hx_diff)

/-- Helper for Chapter02 Theorem 2.2.2: the second derivative of the rescaled profile is the
Hessian quadratic form along the traced segment, scaled by `α²`. -/
lemma unitIntervalTraceSecondIteratedDeriv
    {D : Set Point} (f : Point → ℝ) (x d : Point) (α t : ℝ)
    (hD : IsOpen D)
    (h_segment : segment ℝ x (x + α • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    iteratedDerivWithin 2 (lineSearchObjective f x (α • d)) (Set.uIcc (0 : ℝ) 1) t =
      α ^ (2 : ℕ) * inner ℝ d
        ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (x + t • (α • d))) d) := by
  let φ : ℝ → ℝ := lineSearchObjective f x (α • d)
  let γ : ℝ → Point := fun s ↦ x + s • (α • d)
  have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have hz : γ t ∈ D :=
    unitIntervalTraceMapsToDomain x d α h_segment ht
  have hf_contDiffAt : ContDiffAt ℝ 2 f (γ t) := hC2.contDiffAt (hD.mem_nhds hz)
  have hφ_contDiffAt : ContDiffAt ℝ 2 φ t := by
    -- The scalar profile inherits `C²` regularity from `f` at the traced point.
    change ContDiffAt ℝ 2 (f ∘ γ) t
    exact hf_contDiffAt.comp t (unitIntervalTraceContDiff x d α).contDiffAt
  have hγ_continuous : Continuous γ := (unitIntervalTraceContDiff x d α).continuous
  have htrace_deriv : HasDerivAt γ (α • d) t := by
    simpa [γ] using unitIntervalTraceHasDerivAt x d α t
  have hderiv_eventually :
      deriv φ =ᶠ[nhds t] fun s ↦ inner ℝ (∇ f (γ s)) (α • d) := by
    -- Near `t`, the derivative bridge is exact because the trace stays in `D`.
    have hpreimage : {s : ℝ | γ s ∈ D} ∈ nhds t :=
      hγ_continuous.continuousAt.preimage_mem_nhds (hD.mem_nhds hz)
    filter_upwards [hpreimage] with s hs_mem
    have hs_diff : DifferentiableAt ℝ f (γ s) :=
      hC2.contDiffAt (hD.mem_nhds hs_mem) |>.differentiableAt (by norm_num)
    simpa [φ, γ] using deriv_lineSearchObjective_apply f x (α • d) s hs_diff
  have hgrad_contDiffAt :
      ContDiffAt ℝ 1 (((toDual ℝ Point).symm) ∘ (fderiv ℝ f)) (γ t) := by
    -- Differentiate the Fréchet derivative and transport through the Riesz isomorphism.
    have hfderiv_contDiffAt : ContDiffAt ℝ 1 (fderiv ℝ f) (γ t) :=
      hf_contDiffAt.fderiv_right_succ
    exact
      (LinearIsometryEquiv.contDiff ((toDual ℝ Point).symm)).contDiffAt.comp (γ t)
        hfderiv_contDiffAt
  have hgrad_trace_deriv :
      HasDerivAt ((((toDual ℝ Point).symm) ∘ (fderiv ℝ f)) ∘ γ)
        ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d)) t := by
    -- Chain the derivative of the gradient with the derivative of the affine trace.
    exact
      hgrad_contDiffAt.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t htrace_deriv
  have hderiv_eventually' :
      deriv φ =ᶠ[nhds t]
        fun s ↦ inner ℝ (((toDual ℝ Point).symm) (fderiv ℝ f (γ s))) (α • d) := by
    simpa [gradient] using hderiv_eventually
  have hinner_deriv :
      HasDerivAt
        (fun s ↦ inner ℝ (((toDual ℝ Point).symm) (fderiv ℝ f (γ s))) (α • d))
        (inner ℝ
          ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d))
          (α • d)) t := by
    -- The second derivative is the derivative of the first derivative pairing.
    simpa [Function.comp, γ] using
      hgrad_trace_deriv.inner ℝ (hasDerivAt_const t (α • d))
  have hderiv_deriv :
      HasDerivAt (deriv φ)
        (inner ℝ
          ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d))
          (α • d)) t := by
    exact hinner_deriv.congr_of_eventuallyEq hderiv_eventually'
  have hsecond :
      iteratedDeriv 2 φ t =
        inner ℝ
          ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d))
          (α • d) := by
    -- Identify the second iterated derivative with the derivative of `deriv φ`.
    calc
      iteratedDeriv 2 φ t = deriv (deriv φ) t := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      _ = inner ℝ
            ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d))
            (α • d) := hderiv_deriv.deriv
  calc
    iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) t = iteratedDeriv 2 φ t := by
      exact iteratedDerivWithin_eq_iteratedDeriv hs hφ_contDiffAt ht
    _ = inner ℝ ((fderiv ℝ (∇ f) (γ t)) (α • d)) (α • d) := hsecond
    _ = α ^ (2 : ℕ) * inner ℝ d ((fderiv ℝ (∇ f) (γ t)) d) := by
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, real_inner_comm]

/-- Helper for Chapter02 Theorem 2.2.2: an operator-norm bound on `A` bounds its quadratic form
`⟪v, A v⟫` by `M * ‖v‖²`. -/
lemma quadraticForm_le_mul_normSq_of_bound
    (M : ℝ) (hM_nonneg : 0 ≤ M) (A : Point →L[ℝ] Point) (v : Point)
    (hA : ‖A‖ ≤ M) :
    inner ℝ v (A v) ≤ M * ‖v‖ ^ (2 : ℕ) := by
  -- Combine Cauchy-Schwarz with the operator-norm estimate.
  have hAv : ‖A v‖ ≤ M * ‖v‖ := by
    calc
      ‖A v‖ ≤ ‖A‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
  calc
    inner ℝ v (A v) ≤ ‖v‖ * ‖A v‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * (M * ‖v‖) := mul_le_mul_of_nonneg_left hAv (norm_nonneg _)
    _ = M * ‖v‖ ^ (2 : ℕ) := by
      rw [pow_two]
      ring

/-- Helper for Chapter02 Theorem 2.2.2: on an interval `[0, b]`, an interior minimizer of a
twice continuously differentiable profile with initial negative slope and uniform upper second
derivative bound must satisfy `-deriv φ 0 / M ≤ αStar`. -/
lemma intervalMinimizer_ge_negDeriv_div_secondDerivBound
    {φ : ℝ → ℝ} {b M αStar : ℝ}
    (hC2 : ContDiffOn ℝ 2 φ (Set.Icc (0 : ℝ) b))
    (h_deriv0 : deriv φ 0 < 0)
    (hM : 0 < M)
    (h_secondDeriv :
      ∀ α ∈ Set.Icc (0 : ℝ) b, iteratedDeriv 2 φ α ≤ M)
    (hαStar : αStar ∈ Set.Ioo (0 : ℝ) b)
    (h_min : IsMinOn φ (Set.Icc (0 : ℝ) b) αStar) :
    -deriv φ 0 / M ≤ αStar := by
  -- Apply the one-dimensional mean-value argument to the derivative on `[0, αStar]`.
  have hα0 : 0 < αStar := hαStar.1
  have hαb : αStar < b := hαStar.2
  let s : Set ℝ := Set.Icc (0 : ℝ) αStar
  let g : ℝ → ℝ := derivWithin φ s
  have hs : UniqueDiffOn ℝ s := by
    simpa [s] using uniqueDiffOn_Icc hα0
  have hC2' : ContDiffOn ℝ 2 φ s := by
    simpa [s] using hC2.mono (Set.Icc_subset_Icc_right hαb.le)
  have hg_diff' : DifferentiableOn ℝ (iteratedDerivWithin 1 φ s) s :=
    hC2'.differentiableOn_iteratedDerivWithin (by norm_num) hs
  have hg_diff : DifferentiableOn ℝ g s := by
    simpa [g, iteratedDerivWithin_one] using hg_diff'
  have hg_cont' : ContinuousOn (iteratedDerivWithin 1 φ s) s :=
    hC2'.continuousOn_iteratedDerivWithin (by norm_num) hs
  have hg_cont : ContinuousOn g s := by
    simpa [g, iteratedDerivWithin_one] using hg_cont'
  have h0mem : (0 : ℝ) ∈ s := by simp [s, hα0.le]
  have hαmem : αStar ∈ s := by simp [s, hα0.le]
  have hDiff0 : DifferentiableAt ℝ φ 0 :=
    differentiableAt_of_deriv_ne_zero (by linarith)
  have hDerivWithin0 : g 0 = deriv φ 0 := by
    simpa [g] using hDiff0.derivWithin (hs 0 h0mem)
  have hLocalMin : IsLocalMin φ αStar :=
    h_min.isLocalMin (Icc_mem_nhds hα0 hαb)
  have hDiffAlpha : DifferentiableAt ℝ φ αStar := by
    simpa using (hC2.contDiffAt (Icc_mem_nhds hα0 hαb)).differentiableAt (by norm_num)
  have hDerivWithinAlpha : g αStar = 0 := by
    calc
      g αStar = derivWithin φ s αStar := rfl
      _ = deriv φ αStar := hDiffAlpha.derivWithin (hs αStar hαmem)
      _ = 0 := hLocalMin.deriv_eq_zero
  have hs_right : s ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine mem_of_superset (Ioc_mem_nhdsGT hα0) ?_
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  have hs_left : s ∈ nhdsWithin αStar (Set.Iio αStar) := by
    refine mem_of_superset (Ico_mem_nhdsLT hα0) ?_
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  have hfa : Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv φ 0)) := by
    simpa [ContinuousWithinAt, hDerivWithin0] using
      (hg_cont.continuousWithinAt h0mem).mono_of_mem_nhdsWithin hs_right
  have hfb : Tendsto g (nhdsWithin αStar (Set.Iio αStar)) (nhds (0 : ℝ)) := by
    simpa [ContinuousWithinAt, hDerivWithinAlpha] using
      (hg_cont.continuousWithinAt hαmem).mono_of_mem_nhdsWithin hs_left
  obtain ⟨ξ, hξ, hMVT⟩ :=
    exists_ratio_deriv_eq_ratio_slope' g hα0 id
      (hg_diff.mono (by intro x hx; exact ⟨hx.1.le, hx.2.le⟩))
      (by
        simpa using
          (differentiableOn_id :
            DifferentiableOn ℝ (fun x : ℝ ↦ x) (Set.Ioo (0 : ℝ) αStar)))
      hfa
      (by simpa [Filter.Tendsto] using
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ)))
      hfb
      (by simpa [Filter.Tendsto] using
        (nhdsWithin_le_nhds : nhdsWithin αStar (Set.Iio αStar) ≤ nhds αStar))
  have hξ_mem : ξ ∈ s := ⟨hξ.1.le, hξ.2.le⟩
  have hξ_mem_b : ξ ∈ Set.Icc (0 : ℝ) b := ⟨le_of_lt hξ.1, hξ.2.le.trans hαb.le⟩
  have hContDiffAtξ : ContDiffAt ℝ 2 φ ξ :=
    hC2.contDiffAt (Icc_mem_nhds hξ.1 (hξ.2.trans hαb))
  have hDerivg : deriv g ξ = iteratedDeriv 2 φ ξ := by
    calc
      deriv g ξ = derivWithin g s ξ := (derivWithin_of_mem_nhds (Icc_mem_nhds hξ.1 hξ.2)).symm
      _ = iteratedDerivWithin 2 φ s ξ := by simp [g, iteratedDerivWithin_succ]
      _ = iteratedDeriv 2 φ ξ := iteratedDerivWithin_eq_iteratedDeriv hs hContDiffAtξ hξ_mem
  have hEq : αStar * iteratedDeriv 2 φ ξ = -deriv φ 0 := by
    simpa [g, hDerivWithin0, hDerivWithinAlpha, hDerivg] using hMVT
  have hBound : -deriv φ 0 ≤ αStar * M := by
    nlinarith [hEq, h_secondDeriv ξ hξ_mem_b, hα0]
  exact (div_le_iff₀ hM).2 (by simpa [mul_comm] using hBound)

/-- Helper for Chapter02 Theorem 2.2.2: if a `C²` profile on `[0, a]` has negative initial
slope, vanishing derivative at the right endpoint, and uniform upper second-derivative bound
`M`, then `-deriv φ 0 / M ≤ a`. -/
lemma endpoint_ge_negDeriv_div_secondDerivBound
    {φ : ℝ → ℝ} {a M : ℝ}
    (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 φ (Set.Icc (0 : ℝ) a))
    (hDiffa : DifferentiableAt ℝ φ a)
    (h_deriv0 : deriv φ 0 < 0)
    (h_deriva : deriv φ a = 0)
    (hM : 0 < M)
    (h_secondDeriv :
      ∀ t ∈ Set.Icc (0 : ℝ) a, iteratedDeriv 2 φ t ≤ M) :
    -deriv φ 0 / M ≤ a := by
  -- Apply the mean value theorem to the derivative profile on `[0, a]`.
  let s : Set ℝ := Set.Icc (0 : ℝ) a
  let g : ℝ → ℝ := derivWithin φ s
  have hs : UniqueDiffOn ℝ s := by
    simpa [s] using uniqueDiffOn_Icc ha
  have hg_diff' : DifferentiableOn ℝ (iteratedDerivWithin 1 φ s) s :=
    hC2.differentiableOn_iteratedDerivWithin (by norm_num) hs
  have hg_diff : DifferentiableOn ℝ g s := by
    simpa [g, iteratedDerivWithin_one] using hg_diff'
  have hg_cont' : ContinuousOn (iteratedDerivWithin 1 φ s) s :=
    hC2.continuousOn_iteratedDerivWithin (by norm_num) hs
  have hg_cont : ContinuousOn g s := by
    simpa [g, iteratedDerivWithin_one] using hg_cont'
  have h0mem : (0 : ℝ) ∈ s := by simp [s, ha.le]
  have hamem : a ∈ s := by simp [s, ha.le]
  have hDiff0 : DifferentiableAt ℝ φ 0 :=
    differentiableAt_of_deriv_ne_zero (by linarith)
  have hDerivWithin0 : g 0 = deriv φ 0 := by
    simpa [g] using hDiff0.derivWithin (hs 0 h0mem)
  have hDerivWithina : g a = 0 := by
    calc
      g a = derivWithin φ s a := rfl
      _ = deriv φ a := hDiffa.derivWithin (hs a hamem)
      _ = 0 := h_deriva
  have hs_right : s ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    refine mem_of_superset (Ioc_mem_nhdsGT ha) ?_
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  have hs_left : s ∈ nhdsWithin a (Set.Iio a) := by
    refine mem_of_superset (Ico_mem_nhdsLT ha) ?_
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  have hfa : Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv φ 0)) := by
    simpa [ContinuousWithinAt, hDerivWithin0] using
      (hg_cont.continuousWithinAt h0mem).mono_of_mem_nhdsWithin hs_right
  have hfb : Tendsto g (nhdsWithin a (Set.Iio a)) (nhds (0 : ℝ)) := by
    simpa [ContinuousWithinAt, hDerivWithina] using
      (hg_cont.continuousWithinAt hamem).mono_of_mem_nhdsWithin hs_left
  obtain ⟨ξ, hξ, hMVT⟩ :=
    exists_ratio_deriv_eq_ratio_slope' g ha id
      (hg_diff.mono (by intro x hx; exact ⟨hx.1.le, hx.2.le⟩))
      (by
        simpa using
          (differentiableOn_id :
            DifferentiableOn ℝ (fun x : ℝ ↦ x) (Set.Ioo (0 : ℝ) a)))
      hfa
      (by simpa [Filter.Tendsto] using
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds (0 : ℝ)))
      hfb
      (by simpa [Filter.Tendsto] using
        (nhdsWithin_le_nhds : nhdsWithin a (Set.Iio a) ≤ nhds a))
  have hξ_mem : ξ ∈ s := ⟨hξ.1.le, hξ.2.le⟩
  have hContDiffAtξ : ContDiffAt ℝ 2 φ ξ :=
    hC2.contDiffAt (Icc_mem_nhds hξ.1 hξ.2)
  have hDerivg : deriv g ξ = iteratedDeriv 2 φ ξ := by
    calc
      deriv g ξ = derivWithin g s ξ := (derivWithin_of_mem_nhds (Icc_mem_nhds hξ.1 hξ.2)).symm
      _ = iteratedDerivWithin 2 φ s ξ := by simp [g, iteratedDerivWithin_succ]
      _ = iteratedDeriv 2 φ ξ := iteratedDerivWithin_eq_iteratedDeriv hs hContDiffAtξ hξ_mem
  have hEq : a * iteratedDeriv 2 φ ξ = -deriv φ 0 := by
    simpa [g, hDerivWithin0, hDerivWithina, hDerivg] using hMVT
  have hBound : -deriv φ 0 ≤ a * M := by
    nlinarith [hEq, h_secondDeriv ξ hξ_mem, ha]
  exact (div_le_iff₀ hM).2 (by simpa [mul_comm] using hBound)

/-- Helper for Chapter02 Theorem 2.2.2: every admissible step `α ∈ [0, αk]` satisfies the
textbook quadratic upper model
`f (xk + α • dk) ≤ f xk + α * ⟪∇ f xk, dk⟫ + (M / 2) * α² * ‖dk‖²`. -/
lemma lineSearchObjective_le_base_add_linear_add_quadratic_onIcc
    {D : Set Point} (f : Point → ℝ) (xk dk : Point) (αk M α : ℝ)
    (hM : 0 < M)
    (hD : IsOpen D)
    (hαk : 0 < αk)
    (hα : α ∈ Set.Icc (0 : ℝ) αk)
    (h_segment : segment ℝ xk (xk + αk • dk) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (h_hessianBound : ∀ z ∈ D, ‖fderiv ℝ (∇ f) z‖ ≤ M) :
    lineSearchObjective f xk dk α ≤
      lineSearchObjective f xk dk 0 + α * inner ℝ (∇ f xk) dk +
        (M / 2) * α ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) := by
  -- Route correction: use Taylor-Lagrange on the rescaled unit-interval profile instead of
  -- pushing the Hessian transport directly on `[0, α]`.
  by_cases hα_zero : α = 0
  · -- The zero step is exactly the base-value case.
    simp [hα_zero]
  have hα_pos : 0 < α := by
    rcases hα with ⟨hα_nonneg, _⟩
    exact lt_of_le_of_ne hα_nonneg (Ne.symm hα_zero)
  have h_segmentα : segment ℝ xk (xk + α • dk) ⊆ D :=
    fun z hz ↦ h_segment (searchRay_segment_subset_of_nonneg_le_step xk dk hαk hα.1 hα.2 hz)
  let φ : ℝ → ℝ := lineSearchObjective f xk (α • dk)
  have hφC2 : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) 1) := by
    simpa [φ] using
      unitIntervalTraceContDiffOn f xk dk α h_segmentα hC2
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := φ) (x := 1) (x₀ := 0) (n := 1) zero_ne_one hφC2
  have hξu : ξ ∈ Set.uIcc (0 : ℝ) 1 := by
    exact ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hξD : xk + ξ • (α • dk) ∈ D :=
    unitIntervalTraceMapsToDomain xk dk α h_segmentα hξu
  have hsecond_bound :
      iteratedDeriv 2 φ ξ ≤ α ^ (2 : ℕ) * (M * ‖dk‖ ^ (2 : ℕ)) := by
    calc
      iteratedDeriv 2 φ ξ =
          iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) ξ := by
            symm
            exact iteratedDerivWithin_eq_iteratedDeriv
              (by simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
              (by
                change ContDiffAt ℝ 2 (f ∘ fun t : ℝ ↦ xk + t • (α • dk)) ξ
                exact (hC2.contDiffAt (hD.mem_nhds hξD)).comp ξ
                  (unitIntervalTraceContDiff xk dk α).contDiffAt)
              hξu
      _ = α ^ (2 : ℕ) * inner ℝ dk
            ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z))
                (xk + ξ • (α • dk))) dk) := by
            simpa [φ] using
              unitIntervalTraceSecondIteratedDeriv f xk dk α ξ hD h_segmentα hC2 hξu
      _ = α ^ (2 : ℕ) * inner ℝ dk ((fderiv ℝ (∇ f) (xk + ξ • (α • dk))) dk) := by
            rw [show fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z))
                (xk + ξ • (α • dk)) =
                  fderiv ℝ (∇ f) (xk + ξ • (α • dk)) by rfl]
      _ ≤ α ^ (2 : ℕ) * (M * ‖dk‖ ^ (2 : ℕ)) := by
            gcongr
            exact quadraticForm_le_mul_normSq_of_bound M hM.le _ dk (h_hessianBound _ hξD)
  have hfirst :
      iteratedDerivWithin 1 φ (Set.uIcc (0 : ℝ) 1) 0 = α * inner ℝ (∇ f xk) dk :=
    unitIntervalTraceFirstIteratedDerivZero f xk dk α hD h_segmentα hC2
  have hTaylor' :
      φ 1 =
        φ 0 + α * inner ℝ (∇ f xk) dk + iteratedDeriv 2 φ ξ / 2 := by
    -- Expand Taylor's polynomial at order one and keep the Lagrange remainder explicit.
    have hbase :
        φ 1 - taylorWithinEval φ 1 (Set.uIcc (0 : ℝ) 1) 0 1 = iteratedDeriv 2 φ ξ / 2 := by
      simpa [pow_two] using hTaylor
    rw [taylorWithinEval_succ, taylor_within_zero_eval] at hbase
    rw [hfirst] at hbase
    norm_num at hbase
    have hbase' :
        φ 1 - (φ 0 + α * inner ℝ (∇ f xk) dk) = iteratedDeriv 2 φ ξ / 2 := by
      simpa [gradient] using hbase
    calc
      φ 1 = (φ 1 - (φ 0 + α * inner ℝ (∇ f xk) dk)) +
          (φ 0 + α * inner ℝ (∇ f xk) dk) := by ring
      _ = iteratedDeriv 2 φ ξ / 2 + (φ 0 + α * inner ℝ (∇ f xk) dk) := by
            rw [hbase']
      _ = φ 0 + α * inner ℝ (∇ f xk) dk + iteratedDeriv 2 φ ξ / 2 := by ring
  calc
    lineSearchObjective f xk dk α = φ 1 := by
      simp [φ, lineSearchObjective_apply, smul_smul]
    _ = φ 0 + α * inner ℝ (∇ f xk) dk + iteratedDeriv 2 φ ξ / 2 := hTaylor'
    _ ≤ φ 0 + α * inner ℝ (∇ f xk) dk +
          (α ^ (2 : ℕ) * (M * ‖dk‖ ^ (2 : ℕ))) / 2 := by
            gcongr
    _ = lineSearchObjective f xk dk 0 + α * inner ℝ (∇ f xk) dk +
          (M / 2) * α ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) := by
            simp [φ, lineSearchObjective_zero]
            ring

/-- Chapter02 Theorem 2.2.2: if `αk` solves the exact line-search problem on the nonnegative
ray from `xk` in the descent direction `dk`, the traced segment from `xk` to
`xk + αk • dk` lies in an open set `D` on which `f` is `C²`, and the Hessian operator
`fderiv ℝ (∇ f) z` has norm bounded by the positive constant `M` for every `z ∈ D`, then the
achieved decrease is bounded below by `(1 / (2 * M)) * ‖∇ f xk‖^2 *
  (Real.cos (InnerProductGeometry.angle dk (-(∇ f xk))))^2`. -/
theorem exactLineSearch_decrease_ge_half_inv_hessianBound_mul_gradientNormSq_mul_cosSq
    {D : Set Point} (f : Point → ℝ) (xk dk : Point) (αk M : ℝ)
    (hM : 0 < M)
    (h_descent : IsDescentDirectionAt f xk dk)
    (h_exactLineSearch : IsExactLineSearchStepOnNonnegativeRay f xk dk αk)
    (hD : IsOpen D)
    (h_segment : segment ℝ xk (xk + αk • dk) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (h_hessianBound : ∀ z ∈ D, ‖fderiv ℝ (∇ f) z‖ ≤ M) :
    f xk - f (xk + αk • dk) ≥
      (1 / (2 * M)) * ‖∇ f xk‖ ^ (2 : ℕ) *
        (Real.cos (InnerProductGeometry.angle dk (-(∇ f xk)))) ^ (2 : ℕ) := by
  -- Route correction: rescale the search ray to the unit interval, prove the trial step lies
  -- before the exact step by a derivative MVT argument, then evaluate the quadratic model there.
  have hαk : 0 < αk :=
    exactLineSearchStep_pos_of_descent f xk dk αk h_descent h_exactLineSearch
  have hdk_ne : dk ≠ 0 := h_descent.direction_ne
  have hnorm_d_ne : ‖dk‖ ≠ 0 := norm_ne_zero_iff.mpr hdk_ne
  have hxk_mem : xk ∈ D := h_segment (by simpa using left_mem_segment ℝ xk (xk + αk • dk))
  have hstep_mem : xk + αk • dk ∈ D := by
    exact h_segment (by simpa using right_mem_segment ℝ xk (xk + αk • dk))
  have hDiff0 : DifferentiableAt ℝ f xk := h_descent.differentiableAt
  have hDiffStep : DifferentiableAt ℝ f (xk + αk • dk) :=
    (hC2.contDiffAt (hD.mem_nhds hstep_mem)).differentiableAt (by norm_num)
  have hstationary :
      inner ℝ (∇ f (xk + αk • dk)) dk = 0 := by
    -- Exact optimality at a positive step makes the directional derivative vanish.
    have hnhds : Set.Ici 0 ∈ nhds αk := Ici_mem_nhds hαk
    have hlocal : IsLocalMin (lineSearchObjective f xk dk) αk :=
      h_exactLineSearch.isMinOn.isLocalMin hnhds
    have hderivzero : deriv (lineSearchObjective f xk dk) αk = 0 := hlocal.deriv_eq_zero
    have hderiv :
        deriv (lineSearchObjective f xk dk) αk =
          inner ℝ (∇ f (xk + αk • dk)) dk :=
      deriv_lineSearchObjective_apply f xk dk αk hDiffStep
    rw [hderivzero] at hderiv
    simpa using hderiv.symm
  let ψ : ℝ → ℝ := lineSearchObjective f xk (αk • dk)
  have hψC2 : ContDiffOn ℝ 2 ψ (Set.Icc (0 : ℝ) 1) := by
    simpa [ψ, Set.uIcc_of_le zero_le_one] using
      unitIntervalTraceContDiffOn f xk dk αk h_segment hC2
  have hψDiff1 : DifferentiableAt ℝ ψ 1 := by
    -- The endpoint `1` corresponds to the exact step `αk`.
    have hDiffStep' : DifferentiableAt ℝ f (xk + (1 : ℝ) • (αk • dk)) := by
      simpa [one_smul] using hDiffStep
    change DifferentiableAt ℝ (f ∘ fun t : ℝ ↦ xk + t • (αk • dk)) 1
    simpa [one_smul] using hDiffStep'.comp 1
      (unitIntervalTraceHasDerivAt xk dk αk 1).differentiableAt
  have hψDeriv0 : deriv ψ 0 = αk * inner ℝ (∇ f xk) dk := by
    -- Differentiate the rescaled profile at the base point.
    calc
      deriv ψ 0 = inner ℝ (∇ f xk) (αk • dk) := by
        simpa [ψ, zero_smul] using
          deriv_lineSearchObjective_apply f xk (αk • dk) 0 (by simpa [zero_smul] using hDiff0)
      _ = αk * inner ℝ (∇ f xk) dk := by
        rw [inner_smul_right, mul_comm]
  have hψDeriv0neg : deriv ψ 0 < 0 := by
    rw [hψDeriv0]
    nlinarith [h_descent.inner_gradient_neg, hαk]
  have hψDeriv1 : deriv ψ 1 = 0 := by
    -- The exact-step stationarity transfers to the rescaled profile.
    calc
      deriv ψ 1 = inner ℝ (∇ f (xk + 1 • (αk • dk))) (αk • dk) := by
        simpa [ψ, one_smul] using
          deriv_lineSearchObjective_apply f xk (αk • dk) 1 (by simpa [one_smul] using hDiffStep)
      _ = αk * inner ℝ (∇ f (xk + αk • dk)) dk := by
        simp [inner_smul_right, mul_comm, mul_left_comm, mul_assoc]
      _ = 0 := by simp [hstationary]
  have hψSecond :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        iteratedDeriv 2 ψ t ≤ M * αk ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) := by
    intro t ht
    have htu : t ∈ Set.uIcc (0 : ℝ) 1 := by
      exact Set.mem_uIcc_of_le ht.1 ht.2
    have hz : xk + t • (αk • dk) ∈ D :=
      unitIntervalTraceMapsToDomain xk dk αk h_segment htu
    calc
      iteratedDeriv 2 ψ t =
          iteratedDerivWithin 2 ψ (Set.uIcc (0 : ℝ) 1) t := by
            symm
            exact iteratedDerivWithin_eq_iteratedDeriv
              (by simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num))
              (by
                change ContDiffAt ℝ 2 (f ∘ fun s : ℝ ↦ xk + s • (αk • dk)) t
                exact (hC2.contDiffAt (hD.mem_nhds hz)).comp t
                  (unitIntervalTraceContDiff xk dk αk).contDiffAt)
              htu
      _ = αk ^ (2 : ℕ) * inner ℝ dk
            ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z))
                (xk + t • (αk • dk))) dk) := by
            simpa [ψ] using
              unitIntervalTraceSecondIteratedDeriv f xk dk αk t hD h_segment hC2 htu
      _ = αk ^ (2 : ℕ) * inner ℝ dk ((fderiv ℝ (∇ f) (xk + t • (αk • dk))) dk) := by
            rw [show fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z))
                (xk + t • (αk • dk)) =
                  fderiv ℝ (∇ f) (xk + t • (αk • dk)) by rfl]
      _ ≤ αk ^ (2 : ℕ) * (M * ‖dk‖ ^ (2 : ℕ)) := by
            gcongr
            exact quadraticForm_le_mul_normSq_of_bound M hM.le _ dk (h_hessianBound _ hz)
      _ = M * αk ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) := by ring
  have htrial_le_unit :
      -(deriv ψ 0) / (M * αk ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ)) ≤ (1 : ℝ) := by
    exact endpoint_ge_negDeriv_div_secondDerivBound
      (a := 1) (M := M * αk ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ))
      (by norm_num) hψC2 hψDiff1 hψDeriv0neg hψDeriv1
      (by
        have hnorm_sq_pos : 0 < ‖dk‖ ^ (2 : ℕ) := by
          exact pow_pos (norm_pos_iff.mpr hdk_ne) 2
        positivity)
      hψSecond
  let αbar : ℝ := -(inner ℝ (∇ f xk) dk) / (M * ‖dk‖ ^ (2 : ℕ))
  have hαbar_nonneg : 0 ≤ αbar := by
    -- The descent-direction hypothesis makes the textbook trial step nonnegative.
    refine div_nonneg ?_ ?_
    · linarith [h_descent.inner_gradient_neg]
    · have hnorm_sq_pos : 0 < ‖dk‖ ^ (2 : ℕ) := by
        exact pow_pos (norm_pos_iff.mpr hdk_ne) 2
      positivity
  have htrial_clear :
      -(inner ℝ (∇ f xk) dk) ≤ M * αk * ‖dk‖ ^ (2 : ℕ) := by
    have htrial_le_unit' := htrial_le_unit
    rw [hψDeriv0] at htrial_le_unit'
    have hnorm_sq_ne : ‖dk‖ ^ (2 : ℕ) ≠ 0 := by
      exact pow_ne_zero 2 hnorm_d_ne
    have hαk_sq_ne : αk ^ (2 : ℕ) ≠ 0 := by
      exact pow_ne_zero 2 hαk.ne'
    field_simp [hM.ne', hαk_sq_ne, hnorm_sq_ne] at htrial_le_unit'
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using htrial_le_unit'
  have hαbar_le : αbar ≤ αk := by
    have hdenom_pos : 0 < M * ‖dk‖ ^ (2 : ℕ) := by
      have hnorm_sq_pos : 0 < ‖dk‖ ^ (2 : ℕ) := by
        exact pow_pos (norm_pos_iff.mpr hdk_ne) 2
      positivity
    refine (div_le_iff₀ hdenom_pos).2 ?_
    simpa [αbar, mul_assoc, mul_left_comm, mul_comm] using htrial_clear
  have hαbar_mem : αbar ∈ Set.Icc (0 : ℝ) αk := ⟨hαbar_nonneg, hαbar_le⟩
  have htrial_model :
      lineSearchObjective f xk dk αbar ≤
        lineSearchObjective f xk dk 0 + αbar * inner ℝ (∇ f xk) dk +
          (M / 2) * αbar ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) :=
    lineSearchObjective_le_base_add_linear_add_quadratic_onIcc
      f xk dk αk M αbar hM hD hαk hαbar_mem h_segment hC2 h_hessianBound
  have hexact_compare :
      f xk - f (xk + αk • dk) ≥ f xk - f (xk + αbar • dk) := by
    -- Exact line search compares the true step with the textbook trial step `αbar`.
    have hopt : lineSearchObjective f xk dk αk ≤ lineSearchObjective f xk dk αbar :=
      h_exactLineSearch.optimal hαbar_nonneg
    simpa [lineSearchObjective_apply] using sub_le_sub_left hopt (f xk)
  have htrial_decrease :
      f xk - f (xk + αbar • dk) ≥
        (inner ℝ (∇ f xk) dk) ^ (2 : ℕ) /
          (2 * M * ‖dk‖ ^ (2 : ℕ)) := by
    -- Evaluate the quadratic model at the minimizing trial step.
    have hmodel :
        f (xk + αbar • dk) ≤
          f xk + αbar * inner ℝ (∇ f xk) dk +
            (M / 2) * αbar ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) := by
      simpa [lineSearchObjective_apply, lineSearchObjective_zero] using htrial_model
    have hmodel' :
        f xk - f (xk + αbar • dk) ≥
          -(αbar * inner ℝ (∇ f xk) dk) -
            (M / 2) * αbar ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) := by
      nlinarith [hmodel]
    have hαbar_eval :
        -(αbar * inner ℝ (∇ f xk) dk) -
            (M / 2) * αbar ^ (2 : ℕ) * ‖dk‖ ^ (2 : ℕ) =
          (inner ℝ (∇ f xk) dk) ^ (2 : ℕ) /
            (2 * M * ‖dk‖ ^ (2 : ℕ)) := by
      have hnorm_sq_ne : ‖dk‖ ^ (2 : ℕ) ≠ 0 := by
        exact pow_ne_zero 2 hnorm_d_ne
      unfold αbar
      field_simp [hM.ne', hnorm_sq_ne]
      ring
    rw [hαbar_eval] at hmodel'
    exact hmodel'
  have hcos_rewrite :
      (1 / (2 * M)) * ‖∇ f xk‖ ^ (2 : ℕ) *
          (Real.cos (InnerProductGeometry.angle dk (-(∇ f xk)))) ^ (2 : ℕ) =
        (inner ℝ (∇ f xk) dk) ^ (2 : ℕ) /
          (2 * M * ‖dk‖ ^ (2 : ℕ)) := by
    calc
      (1 / (2 * M)) * ‖∇ f xk‖ ^ (2 : ℕ) *
          (Real.cos (InnerProductGeometry.angle dk (-(∇ f xk)))) ^ (2 : ℕ)
          =
        (1 / (2 * M)) *
          (‖∇ f xk‖ *
            Real.cos (InnerProductGeometry.angle dk (-(∇ f xk)))) ^ (2 : ℕ) := by
              rw [pow_two, pow_two]
              ring
      _ =
        (1 / (2 * M)) *
          (-(inner ℝ (∇ f xk) dk / ‖dk‖)) ^ (2 : ℕ) := by
            rw [gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm]
      _ =
        (inner ℝ (∇ f xk) dk) ^ (2 : ℕ) /
          (2 * M * ‖dk‖ ^ (2 : ℕ)) := by
            have hnorm_sq_ne : ‖dk‖ ^ (2 : ℕ) ≠ 0 := by
              exact pow_ne_zero 2 hnorm_d_ne
            field_simp [pow_two, hM.ne', hnorm_sq_ne]
  calc
    f xk - f (xk + αk • dk) ≥ f xk - f (xk + αbar • dk) := hexact_compare
    _ ≥ (inner ℝ (∇ f xk) dk) ^ (2 : ℕ) / (2 * M * ‖dk‖ ^ (2 : ℕ)) := htrial_decrease
    _ = (1 / (2 * M)) * ‖∇ f xk‖ ^ (2 : ℕ) *
          (Real.cos (InnerProductGeometry.angle dk (-(∇ f xk)))) ^ (2 : ℕ) :=
          hcos_rewrite.symm

end Theorem222
