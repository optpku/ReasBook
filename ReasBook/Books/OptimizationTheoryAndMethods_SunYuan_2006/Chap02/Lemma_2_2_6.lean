/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Filter InnerProductSpace
open scoped Gradient

noncomputable section

-- Domain sampling: this bridge theorem lives in smooth line search on a real Hilbert space.
-- The relevant owner abstractions are the Chapter 2 ray profile `lineSearchObjective`, the
-- one-variable Taylor integral remainder owner `taylor_integral_remainder`, the local regularity
-- owner `ContDiffOn` on a neighborhood of the traced segment, and the Hessian operator
-- `fderiv ℝ (∇ f)`. The primitive data are therefore the search line, the open domain containing
-- its traced segment, and the ambient `C²` regularity on that domain; the Hessian integral term
-- is derived API.

section

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [CompleteSpace Point]

/-- Helper for Chapter02 Lemma 2.2.6: the affine trace `t ↦ x + t • (α • d)` has constant
derivative `α • d`. -/
lemma unit_interval_trace_hasDerivAt (x d : Point) (α t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • (α • d)) (α • d) t := by
  -- Differentiate the affine trace directly.
  simpa [one_smul] using ((hasDerivAt_id' t).smul_const (α • d)).const_add x

/-- Helper for Chapter02 Lemma 2.2.6: the affine trace along the search direction is smooth. -/
lemma unit_interval_trace_contDiff (x d : Point) (α : ℝ) :
    ContDiff ℝ 2 (fun t : ℝ ↦ x + t • (α • d)) := by
  -- The trace is a constant-plus-linear map, hence `C²`.
  simpa using contDiff_const.add (contDiff_id.smul_const (α • d))

/-- Helper for Chapter02 Lemma 2.2.6: the unit-interval trace of the search ray stays inside the
domain that contains the segment from `x` to `x + α • d`. -/
lemma unit_interval_trace_mapsTo_domain
    {D : Set Point} (x d : Point) (α : ℝ)
    (h_segment : segment ℝ x (x + α • d) ⊆ D) :
    Set.MapsTo (fun t : ℝ ↦ x + t • (α • d)) (Set.uIcc (0 : ℝ) 1) D := by
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le zero_le_one] using ht
  -- Rewrite the trace as the standard segment parametrization.
  have htrace_mem : x + t • (α • d) ∈ segment ℝ x (x + α • d) := by
    rw [segment_eq_image' ℝ x (x + α • d)]
    refine ⟨t, ht', ?_⟩
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, smul_smul]
  exact h_segment htrace_mem

/-- Helper for Chapter02 Lemma 2.2.6: composing `f` with the affine search trace gives a `C²`
scalar profile on `[0, 1]`. -/
lemma unit_interval_trace_contDiffOn
    {D : Set Point} (f : Point → ℝ) (x d : Point) (α : ℝ)
    (h_segment : segment ℝ x (x + α • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D) :
    ContDiffOn ℝ 2 (lineSearchObjective f x (α • d)) (Set.uIcc (0 : ℝ) 1) := by
  -- Compose the ambient `C²` objective with the smooth affine trace.
  change ContDiffOn ℝ 2 (f ∘ fun t : ℝ ↦ x + t • (α • d)) (Set.uIcc (0 : ℝ) 1)
  exact hC2.comp (unit_interval_trace_contDiff x d α).contDiffOn
    (unit_interval_trace_mapsTo_domain x d α h_segment)

/-- Helper for Chapter02 Lemma 2.2.6: the first trace derivative at `0` is the directional
gradient pairing `α * ⟪∇ f x, d⟫`. -/
lemma unit_interval_trace_first_iteratedDeriv_zero
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
  have hx_mem : x ∈ D :=
    by simpa using unit_interval_trace_mapsTo_domain x d α h_segment h0_mem
  have hφ_contDiffAt : ContDiffAt ℝ 2 φ 0 := by
    -- Use openness of `D` to upgrade the on-domain regularity to a genuine pointwise `C²` fact.
    have hf_contDiffAt : ContDiffAt ℝ 2 f x := hC2.contDiffAt (hD.mem_nhds hx_mem)
    have hf_contDiffAt_zero : ContDiffAt ℝ 2 f (x + (0 : ℝ) • (α • d)) := by
      simpa [one_smul] using hf_contDiffAt
    change ContDiffAt ℝ 2 (f ∘ fun t : ℝ ↦ x + t • (α • d)) 0
    exact hf_contDiffAt_zero.comp 0 (unit_interval_trace_contDiff x d α).contDiffAt
  have hx_diff : DifferentiableAt ℝ f x :=
    hC2.contDiffAt (hD.mem_nhds hx_mem) |>.differentiableAt (by norm_num)
  calc
    iteratedDerivWithin 1 φ (Set.uIcc (0 : ℝ) 1) 0 = iteratedDeriv 1 φ 0 := by
      exact iteratedDerivWithin_eq_iteratedDeriv hs (hφ_contDiffAt.of_le (by norm_num)) h0_mem
    _ = deriv φ 0 := by simp [iteratedDeriv_one]
    _ = α * inner ℝ (∇ f x) d := by
      simpa [φ, real_inner_comm, inner_smul_right, one_smul, lineSearchObjective_apply] using
        deriv_lineSearchObjective_apply f x (α • d) 0 (by simpa [one_smul] using hx_diff)

/-- Helper for Chapter02 Lemma 2.2.6: the second trace derivative is the Hessian quadratic form
along the traced segment, scaled by `α²`. -/
lemma unit_interval_trace_second_iteratedDeriv
    {D : Set Point} (f : Point → ℝ) (x d : Point) (α t : ℝ)
    (hD : IsOpen D)
    (h_segment : segment ℝ x (x + α • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    iteratedDerivWithin 2 (lineSearchObjective f x (α • d)) (Set.uIcc (0 : ℝ) 1) t =
      α ^ (2 : ℕ) * inner ℝ d ((fderiv ℝ (∇ f) (x + t • (α • d))) d) := by
  let φ : ℝ → ℝ := lineSearchObjective f x (α • d)
  let γ : ℝ → Point := fun s ↦ x + s • (α • d)
  have hs : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have hz : γ t ∈ D :=
    unit_interval_trace_mapsTo_domain x d α h_segment ht
  have hf_contDiffAt : ContDiffAt ℝ 2 f (γ t) := hC2.contDiffAt (hD.mem_nhds hz)
  have hφ_contDiffAt : ContDiffAt ℝ 2 φ t := by
    -- The traced scalar profile inherits `C²` regularity from the ambient objective.
    change ContDiffAt ℝ 2 (f ∘ γ) t
    exact hf_contDiffAt.comp t (unit_interval_trace_contDiff x d α).contDiffAt
  have hγ_continuous : Continuous γ := (unit_interval_trace_contDiff x d α).continuous
  have htrace_deriv : HasDerivAt γ (α • d) t := by
    -- The affine trace has constant derivative `α • d`.
    simpa [γ] using unit_interval_trace_hasDerivAt x d α t
  have hderiv_eventually :
      deriv φ =ᶠ[nhds t] fun s ↦ inner ℝ (∇ f (γ s)) (α • d) := by
    -- Near `t`, the traced points stay inside `D`, so the line-search derivative formula applies.
    have hpreimage : {s : ℝ | γ s ∈ D} ∈ nhds t :=
      hγ_continuous.continuousAt.preimage_mem_nhds (hD.mem_nhds hz)
    filter_upwards [hpreimage] with s hs_mem
    have hs_diff : DifferentiableAt ℝ f (γ s) :=
      hC2.contDiffAt (hD.mem_nhds hs_mem) |>.differentiableAt (by norm_num)
    simpa [φ, γ] using deriv_lineSearchObjective_apply f x (α • d) s hs_diff
  have hgrad_contDiffAt :
      ContDiffAt ℝ 1 (((toDual ℝ Point).symm) ∘ (fderiv ℝ f)) (γ t) := by
    -- Differentiate `fderiv` once and transport through the Riesz isomorphism.
    have hfderiv_contDiffAt : ContDiffAt ℝ 1 (fderiv ℝ f) (γ t) :=
      hf_contDiffAt.fderiv_right_succ
    exact
      (LinearIsometryEquiv.contDiff ((toDual ℝ Point).symm)).contDiffAt.comp (γ t)
        hfderiv_contDiffAt
  have hgrad_trace_deriv :
      HasDerivAt ((((toDual ℝ Point).symm) ∘ (fderiv ℝ f)) ∘ γ)
        ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d)) t := by
    -- Route correction: differentiate the traced gradient field first, then pair with `α • d`.
    exact
      hgrad_contDiffAt.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t htrace_deriv
  have hderiv_eventually' :
      deriv φ =ᶠ[nhds t]
        fun s ↦ inner ℝ (((toDual ℝ Point).symm) (fderiv ℝ f (γ s))) (α • d) := by
    -- Re-express the gradient through `toDual.symm ∘ fderiv` before taking one more derivative.
    simpa [gradient] using hderiv_eventually
  have hinner_deriv :
      HasDerivAt
        (fun s ↦ inner ℝ (((toDual ℝ Point).symm) (fderiv ℝ f (γ s))) (α • d))
        (inner ℝ
          ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d))
          (α • d)) t := by
    -- Differentiate the scalar gradient pairing along the affine trace.
    simpa [Function.comp, γ] using
      hgrad_trace_deriv.inner ℝ (hasDerivAt_const t (α • d))
  have hderiv_deriv :
      HasDerivAt (deriv φ)
        (inner ℝ
          ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d))
          (α • d)) t := by
    -- Transfer the derivative across the eventual equality for `deriv φ`.
    exact hinner_deriv.congr_of_eventuallyEq hderiv_eventually'
  have hsecond :
      iteratedDeriv 2 φ t =
        inner ℝ
          ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) (α • d))
          (α • d) := by
    -- Identify the second iterated derivative with `deriv (deriv φ)`.
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
      -- Pull both occurrences of `α` out of the Hessian quadratic form.
      rw [ContinuousLinearMap.map_smul, inner_smul_left, inner_smul_right]
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, real_inner_comm]

/-- Helper for Chapter02 Lemma 2.2.6: evaluating the traced profile at `1` recovers the original
line-search objective at step length `α`. -/
theorem lineSearchObjective_smul_direction_one_eq
    (f : Point → ℝ) (x d : Point) (α : ℝ) :
    lineSearchObjective f x (α • d) 1 = lineSearchObjective f x d α := by
  -- Collapse the two equivalent ways of writing the same traced point.
  simp [lineSearchObjective_apply, smul_smul]

/-- Chapter02 Lemma 2.2.6: if `f : Point → ℝ` is twice continuously differentiable on an open set
`D` containing the segment from `x` to `x + α • d`, then the line-search objective
`lineSearchObjective f x d` admits the
second-order integral expansion
`lineSearchObjective f x d α = f x + α * ⟪∇ f x, d⟫ + α ^ (2 : ℕ) * ∫ t in 0..1,
  (1 - t) * ⟪d, (fderiv ℝ (∇ f) (x + (t * α) • d)) d⟫`.
This keeps the source-facing Chapter 2 owner `lineSearchObjective` for the search ray while
recasting the regularity hypothesis as a local `ContDiffOn` bridge to mathlib's one-variable
Taylor integral remainder theorem, rather than as a global `ContDiff` assumption on all of
`Point`. -/
theorem lineTaylorFormula_withIntegralHessianRemainder
    {D : Set Point} (f : Point → ℝ) (x d : Point) (α : ℝ)
    (hD : IsOpen D)
    (h_segment : segment ℝ x (x + α • d) ⊆ D)
    (hC2 : ContDiffOn ℝ 2 f D) :
    lineSearchObjective f x d α =
      f x + α * inner ℝ (∇ f x) d +
        α ^ (2 : ℕ) * ∫ t in 0..1,
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) := by
  let φ : ℝ → ℝ := lineSearchObjective f x (α • d)
  have hφC2 : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) 1) :=
    unit_interval_trace_contDiffOn f x d α h_segment hC2
  have hTaylor :=
    taylor_integral_remainder (f := φ) (x₀ := (0 : ℝ)) (x := 1) (n := 1) hφC2
  have hIntegral :
      ∫ t in (0 : ℝ)..1,
          ((1 - t) ^ 1 / ((Nat.factorial 1 : ℕ) : ℝ)) •
            iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) t =
        α ^ (2 : ℕ) *
          (∫ t in (0 : ℝ)..1,
            (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + t • (α • d))) d)) := by
    -- Replace the abstract second derivative in the remainder by the Hessian quadratic form.
    calc
      ∫ t in (0 : ℝ)..1,
          ((1 - t) ^ 1 / ((Nat.factorial 1 : ℕ) : ℝ)) •
            iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) t
          =
          ∫ t in (0 : ℝ)..1,
            α ^ (2 : ℕ) * ((1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + t • (α • d))) d)) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards with t ht
            have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
              simpa [Set.uIoc_of_le zero_le_one] using ht
            have ht' : t ∈ Set.uIcc (0 : ℝ) 1 :=
              Set.mem_uIcc_of_le htIoc.1.le htIoc.2
            rw [unit_interval_trace_second_iteratedDeriv f x d α t hD h_segment hC2 ht']
            ring
      _ = α ^ (2 : ℕ) * ∫ t in (0 : ℝ)..1,
            (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + t • (α • d))) d) := by
            rw [intervalIntegral.integral_const_mul]
  -- Assemble Taylor's theorem with the computed first- and second-derivative identities.
  rw [taylorWithinEval_succ, taylor_within_zero_eval] at hTaylor
  rw [unit_interval_trace_first_iteratedDeriv_zero f x d α hD h_segment hC2] at hTaylor
  rw [hIntegral] at hTaylor
  norm_num at hTaylor
  have hTaylorEq :
      φ 1 = φ 0 + α * inner ℝ (∇ f x) d +
        α ^ (2 : ℕ) * ∫ t in (0 : ℝ)..1,
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + t • (α • d))) d) := by
    rw [← inner_gradient_left (f := f) (x := x) (y := d)] at hTaylor
    have hTaylorEq' := (sub_eq_iff_eq_add).mp hTaylor
    simpa [add_assoc, add_left_comm, add_comm] using hTaylorEq'
  calc
    lineSearchObjective f x d α = φ 1 := by
      simpa [φ] using (lineSearchObjective_smul_direction_one_eq f x d α).symm
    _ = φ 0 + α * inner ℝ (∇ f x) d +
          α ^ (2 : ℕ) * ∫ t in (0 : ℝ)..1,
            (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + t • (α • d))) d) := hTaylorEq
    _ = f x + α * inner ℝ (∇ f x) d +
          α ^ (2 : ℕ) * ∫ t in (0 : ℝ)..1,
            (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + t • (α • d))) d) := by
          simp [φ, lineSearchObjective_zero]
    _ = f x + α * inner ℝ (∇ f x) d +
          α ^ (2 : ℕ) * ∫ t in 0..1,
            (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) := by
          simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc]

end
