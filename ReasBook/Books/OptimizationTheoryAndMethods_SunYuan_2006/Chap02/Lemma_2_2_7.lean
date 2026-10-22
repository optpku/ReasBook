/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Lemma_2_2_6
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.Extr

open Filter InnerProductSpace
open scoped Gradient

noncomputable section

section

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [CompleteSpace Point]

-- Domain sampling:
-- * core/canonical mathlib owners: `IsLocalMin`, `ContDiffOn ℝ 2 f s`, and
--   `StrongConvexOn s m f` for second-order convexity data on a set;
-- * nearby Chapter 2 bridge owner: `lineTaylorFormula_withIntegralHessianRemainder`, which uses
--   the same Hessian operator surface `fderiv ℝ (∇ f)` for local second-order estimates.
-- Primitive data here are the local minimizer, the local `C²` ball regularity, and the
-- one-sided Hessian quadratic bound needed for each estimate. The coordinate model `ℝⁿ`, the
-- positivity of `ε`, and the unused opposite-side Hessian bound are not primitive for these
-- three conclusions, so the public API is stated over the canonical real Hilbert-space owner
-- and only keeps the needed hypotheses.

variable (f : Point → ℝ) (xStar : Point) (ε : ℝ)

local notation "B" => Metric.ball xStar ε

/-- Helper for Chapter02 Lemma 2.2.7: a point in `Metric.ball xStar ε` determines a whole
segment from `xStar` that stays inside the same ball. -/
lemma segment_subset_ball_of_mem_ball
    {x : Point} (hx : x ∈ B) :
    segment ℝ xStar x ⊆ B := by
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg hx
  have hxStar : xStar ∈ B := Metric.mem_ball_self hε
  -- Convexity of the ball keeps the entire segment inside the neighborhood.
  exact (convex_ball xStar ε).segment_subset hxStar hx

/-- Helper for Chapter02 Lemma 2.2.7: the weight `1 - t` integrates to `1 / 2` on `[0, 1]`. -/
lemma unitInterval_integral_one_sub :
    ∫ t in (0 : ℝ)..1, (1 - t) = (1 / 2 : ℝ) := by
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hid : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  -- Evaluate the affine weight integral by splitting it into the constant and identity parts.
  rw [intervalIntegral.integral_sub hconst hid, intervalIntegral.integral_const, integral_id]
  norm_num

/-- Helper for Chapter02 Lemma 2.2.7: the traced Hessian quadratic form along the unit segment is
interval integrable. -/
lemma hessianQuadratic_intervalIntegrable
    (hC2 : ContDiffOn ℝ 2 f B)
    {x : Point} (hx : x ∈ B) :
    IntervalIntegrable
      (fun t : ℝ ↦
        inner ℝ (x - xStar)
          ((fderiv ℝ (∇ f) (xStar + t • (x - xStar))) (x - xStar)))
      MeasureTheory.volume 0 1 := by
  let d : Point := x - xStar
  let φ : ℝ → ℝ := lineSearchObjective f xStar d
  have h_segment : segment ℝ xStar x ⊆ B :=
    segment_subset_ball_of_mem_ball (xStar := xStar) (ε := ε) hx
  have h_segment_line : segment ℝ xStar (xStar + (1 : ℝ) • d) ⊆ B := by
    simpa [d, one_smul, sub_eq_add_neg, add_assoc] using h_segment
  have hφC2 : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) 1) := by
    -- The source profile is the line search restricted to the unit segment from `xStar` to `x`.
    simpa [φ, d] using unit_interval_trace_contDiffOn f xStar (x - xStar) 1 h_segment_line hC2
  have h_unique : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have hsecond_int :
      IntervalIntegrable
        (iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1))
        MeasureTheory.volume 0 1 :=
    (hφC2.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) h_unique).intervalIntegrable
  -- Replace the abstract second derivative by the concrete Hessian quadratic form on `(0, 1]`.
  refine hsecond_int.congr ?_
  intro t ht
  have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := by
    have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le zero_le_one] using ht
    exact Set.mem_uIcc_of_le htIoc.1.le htIoc.2
  simpa [φ, d] using
    unit_interval_trace_second_iteratedDeriv f xStar (x - xStar) 1 t Metric.isOpen_ball
      h_segment_line hC2 ht'

/-- Helper for Chapter02 Lemma 2.2.7: the weighted Hessian quadratic form along the unit segment
is interval integrable. -/
lemma weighted_hessianQuadratic_intervalIntegrable
    (hC2 : ContDiffOn ℝ 2 f B)
    {x : Point} (hx : x ∈ B) :
    IntervalIntegrable
      (fun t : ℝ ↦
        (1 - t) *
          inner ℝ (x - xStar)
            ((fderiv ℝ (∇ f) (xStar + t • (x - xStar))) (x - xStar)))
      MeasureTheory.volume 0 1 := by
  let d : Point := x - xStar
  let φ : ℝ → ℝ := lineSearchObjective f xStar d
  have h_segment : segment ℝ xStar x ⊆ B :=
    segment_subset_ball_of_mem_ball (xStar := xStar) (ε := ε) hx
  have h_segment_line : segment ℝ xStar (xStar + (1 : ℝ) • d) ⊆ B := by
    simpa [d, one_smul, sub_eq_add_neg, add_assoc] using h_segment
  have hφC2 : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) 1) := by
    -- The Taylor remainder is taken along the same unit-segment profile.
    simpa [φ, d] using unit_interval_trace_contDiffOn f xStar (x - xStar) 1 h_segment_line hC2
  have h_unique : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have hweighted_int :
      IntervalIntegrable
        (fun t : ℝ ↦ (1 - t) * iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) t)
        MeasureTheory.volume 0 1 := by
    have hcont :
        ContinuousOn
          (fun t : ℝ ↦ (1 - t) * iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) t)
          (Set.uIcc (0 : ℝ) 1) :=
      (continuous_const.sub continuous_id).continuousOn.mul
        (hφC2.continuousOn_iteratedDerivWithin (m := 2) (by norm_num) h_unique)
    exact hcont.intervalIntegrable
  -- Rewrite the weighted second derivative back to the weighted Hessian quadratic trace.
  refine hweighted_int.congr ?_
  intro t ht
  have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := by
    have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le zero_le_one] using ht
    exact Set.mem_uIcc_of_le htIoc.1.le htIoc.2
  change
    (1 - t) * iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) t =
      (1 - t) * inner ℝ (x - xStar)
        ((fderiv ℝ (∇ f) (xStar + t • (x - xStar))) (x - xStar))
  have hsecond :
      iteratedDerivWithin 2 φ (Set.uIcc (0 : ℝ) 1) t =
        inner ℝ (x - xStar)
          ((fderiv ℝ (∇ f) (xStar + t • (x - xStar))) (x - xStar)) := by
    simpa [φ, d] using
      unit_interval_trace_second_iteratedDeriv f xStar (x - xStar) 1 t Metric.isOpen_ball
        h_segment_line hC2 ht'
  rw [hsecond]

/-- Helper for Chapter02 Lemma 2.2.7: differentiating the traced gradient pairing along the unit
segment yields the Hessian quadratic form. -/
lemma gradient_trace_inner_hasDerivAt
    (hC2 : ContDiffOn ℝ 2 f B)
    {x : Point} (hx : x ∈ B)
    {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ ↦ inner ℝ (∇ f (xStar + s • (x - xStar))) (x - xStar))
      (inner ℝ (x - xStar)
        ((fderiv ℝ (∇ f) (xStar + t • (x - xStar))) (x - xStar)))
      t := by
  let d : Point := x - xStar
  let γ : ℝ → Point := fun s ↦ xStar + s • d
  have h_segment : segment ℝ xStar x ⊆ B :=
    segment_subset_ball_of_mem_ball (xStar := xStar) (ε := ε) hx
  have h_segment_line : segment ℝ xStar (xStar + (1 : ℝ) • d) ⊆ B := by
    simpa [d, one_smul, sub_eq_add_neg, add_assoc] using h_segment
  have hz : γ t ∈ B := by
    -- The traced point at parameter `t` stays inside the local neighborhood.
    simpa [γ, d] using unit_interval_trace_mapsTo_domain xStar (x - xStar) 1 h_segment_line ht
  have hf_contDiffAt : ContDiffAt ℝ 2 f (γ t) :=
    hC2.contDiffAt (Metric.isOpen_ball.mem_nhds hz)
  have htrace_deriv : HasDerivAt γ d t := by
    -- The affine trace has constant derivative `d`.
    simpa [γ, d] using unit_interval_trace_hasDerivAt xStar (x - xStar) 1 t
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
        ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) d) t := by
    -- Differentiate the traced gradient field first.
    exact hgrad_contDiffAt.differentiableAt_one.hasFDerivAt.comp_hasDerivAt t htrace_deriv
  have hinner_deriv :
      HasDerivAt
        (fun s : ℝ ↦ inner ℝ (((toDual ℝ Point).symm) (fderiv ℝ f (γ s))) d)
        (inner ℝ ((fderiv ℝ (fun z ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) (γ t)) d) d)
        t := by
    -- Pair the differentiated trace with the fixed displacement vector.
    simpa [Function.comp, γ, d] using
      hgrad_trace_deriv.inner ℝ (hasDerivAt_const t d)
  have hgradfun : (fun z : Point ↦ (toDual ℝ Point).symm (fderiv ℝ f z)) = ∇ f := by
    funext z
    simp [gradient]
  simpa [hgradfun, γ, d, real_inner_comm] using hinner_deriv

/-- Helper for Chapter02 Lemma 2.2.7: the function-value gap equals the weighted Hessian
quadratic integral along the segment from `xStar` to `x`. -/
lemma value_sub_eq_intervalIntegral_hessianQuadratic
    (hMin : IsLocalMin f xStar)
    (hC2 : ContDiffOn ℝ 2 f B)
    {x : Point} (hx : x ∈ B) :
    f x - f xStar =
      ∫ t in (0 : ℝ)..1,
        (1 - t) *
          inner ℝ (x - xStar)
            ((fderiv ℝ (∇ f) (xStar + t • (x - xStar))) (x - xStar)) := by
  let d : Point := x - xStar
  have h_segment : segment ℝ xStar x ⊆ B :=
    segment_subset_ball_of_mem_ball (xStar := xStar) (ε := ε) hx
  have h_segment_line : segment ℝ xStar (xStar + (1 : ℝ) • d) ⊆ B := by
    simpa [d, one_smul, sub_eq_add_neg, add_assoc] using h_segment
  have hgrad0 : ∇ f xStar = 0 := by
    -- A local minimizer has vanishing derivative, hence vanishing gradient.
    simpa [gradient] using congrArg ((toDual ℝ Point).symm) hMin.fderiv_eq_zero
  have hTaylor :=
    lineTaylorFormula_withIntegralHessianRemainder (D := B) f xStar d 1 Metric.isOpen_ball
      h_segment_line hC2
  have hTaylorEq :
      f x =
        f xStar +
          ∫ t in (0 : ℝ)..1,
            (1 - t) *
              inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) := by
    -- Specialize Lemma 2.2.6 to the unit segment and kill the linear term at the minimizer.
    simpa [d, lineSearchObjective_apply, lineSearchObjective_zero, hgrad0, one_smul,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hTaylor
  -- Move the value `f xStar` to the left-hand side to match the source identity.
  linarith

/-- Helper for Chapter02 Lemma 2.2.7: the gradient pairing at `x` equals the Hessian quadratic
integral along the segment from `xStar` to `x`. -/
lemma gradient_pairing_eq_intervalIntegral_hessianQuadratic
    (hMin : IsLocalMin f xStar)
    (hC2 : ContDiffOn ℝ 2 f B)
    {x : Point} (hx : x ∈ B) :
    inner ℝ (∇ f x) (x - xStar) =
      ∫ t in (0 : ℝ)..1,
        inner ℝ (x - xStar)
          ((fderiv ℝ (∇ f) (xStar + t • (x - xStar))) (x - xStar)) := by
  let d : Point := x - xStar
  let ψ : ℝ → ℝ := fun s ↦ inner ℝ (∇ f (xStar + s • d)) d
  have hψ_int :
      IntervalIntegrable
        (fun t : ℝ ↦ inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d))
        MeasureTheory.volume 0 1 :=
    hessianQuadratic_intervalIntegrable (f := f) (xStar := xStar) (ε := ε) hC2 hx
  have hftc :
      ∫ t in (0 : ℝ)..1,
        inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) =
        ψ 1 - ψ 0 := by
    -- Apply the scalar fundamental theorem of calculus to the traced gradient pairing.
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hψ_int
    intro t ht
    exact gradient_trace_inner_hasDerivAt f xStar ε hC2 hx ht
  have hgrad0 : ∇ f xStar = 0 := by
    -- The starting endpoint contributes no first-order term because `xStar` is a local minimizer.
    simpa [gradient] using congrArg ((toDual ℝ Point).symm) hMin.fderiv_eq_zero
  have hψ0 : ψ 0 = 0 := by
    calc
      ψ 0 = inner ℝ (∇ f xStar) d := by
        simp [ψ, d]
      _ = 0 := by
        simp [hgrad0]
  calc
    inner ℝ (∇ f x) d = ψ 1 := by
      simp [ψ, d]
    _ = ψ 1 - ψ 0 := by
      rw [hψ0, sub_zero]
    _ = ∫ t in (0 : ℝ)..1,
          inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) := by
      rw [← hftc]

/-- Chapter02 Lemma 2.2.7 (1): if `xStar` is a local minimizer of `f`, `f` is twice
continuously differentiable on `Metric.ball xStar ε`, and the Hessian quadratic form satisfies
`m * ‖y‖ ^ 2 ≤ inner ℝ y ((fderiv ℝ (∇ f) z) y)` for every `z ∈ Metric.ball xStar ε` and `y`,
then every `x ∈ Metric.ball xStar ε` satisfies
`(1 / 2 : ℝ) * m * ‖x - xStar‖ ^ 2 ≤ f x - f xStar`. -/
theorem minimizerValue_lowerBound_of_hessianQuadratic_bounds
    (hMin : IsLocalMin f xStar)
    (hC2 : ContDiffOn ℝ 2 f B)
    (x : Point) (m : ℝ)
    (hLower :
      ∀ z ∈ B, ∀ y : Point,
        m * ‖y‖ ^ 2 ≤ inner ℝ y ((fderiv ℝ (∇ f) z) y))
    (hx : x ∈ B) :
    (1 / 2 : ℝ) * m * ‖x - xStar‖ ^ 2 ≤ f x - f xStar := by
  let d : Point := x - xStar
  have h_segment : segment ℝ xStar x ⊆ B :=
    segment_subset_ball_of_mem_ball (xStar := xStar) (ε := ε) hx
  have h_segment_line : segment ℝ xStar (xStar + (1 : ℝ) • d) ⊆ B := by
    simpa [d, one_smul, sub_eq_add_neg, add_assoc] using h_segment
  have hweighted_int :=
    weighted_hessianQuadratic_intervalIntegrable (f := f) (xStar := xStar) (ε := ε) hC2 hx
  have hlower_int :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t) * (m * ‖d‖ ^ 2)) MeasureTheory.volume 0 1 :=
    (by continuity : Continuous fun t : ℝ ↦ (1 - t) * (m * ‖d‖ ^ 2)).intervalIntegrable 0 1
  have hmono :
      ∫ t in (0 : ℝ)..1, (1 - t) * (m * ‖d‖ ^ 2) ≤
        ∫ t in (0 : ℝ)..1,
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) := by
    -- Compare the Taylor remainder integrand against its pointwise lower quadratic bound.
    apply intervalIntegral.integral_mono_on zero_le_one hlower_int hweighted_int
    intro t ht
    have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := Set.mem_uIcc_of_le ht.1 ht.2
    have hz : xStar + t • d ∈ B := by
      simpa [d] using unit_interval_trace_mapsTo_domain xStar d 1 h_segment_line ht'
    have ht_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    exact mul_le_mul_of_nonneg_left (hLower _ hz d) ht_nonneg
  have hweight_eval :
      ∫ t in (0 : ℝ)..1, (1 - t) * (m * ‖d‖ ^ 2) =
        (1 / 2 : ℝ) * m * ‖d‖ ^ 2 := by
    -- Pull out the constant quadratic factor and evaluate the scalar weight integral.
    rw [intervalIntegral.integral_mul_const, unitInterval_integral_one_sub]
    ring
  have hvalue_eq :
      f x - f xStar =
        ∫ t in (0 : ℝ)..1,
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) :=
    value_sub_eq_intervalIntegral_hessianQuadratic (f := f) (xStar := xStar) (ε := ε) hMin hC2 hx
  calc
    (1 / 2 : ℝ) * m * ‖d‖ ^ 2 =
        ∫ t in (0 : ℝ)..1, (1 - t) * (m * ‖d‖ ^ 2) := by
          rw [hweight_eval]
    _ ≤ ∫ t in (0 : ℝ)..1,
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) := hmono
    _ = f x - f xStar := by
      symm
      exact hvalue_eq

/-- Chapter02 Lemma 2.2.7 (2): if `xStar` is a local minimizer of `f`, `f` is twice
continuously differentiable on `Metric.ball xStar ε`, and the Hessian quadratic form satisfies
`inner ℝ y ((fderiv ℝ (∇ f) z) y) ≤ M * ‖y‖ ^ 2` for every `z ∈ Metric.ball xStar ε` and `y`,
then every `x ∈ Metric.ball xStar ε` satisfies
`f x - f xStar ≤ (1 / 2 : ℝ) * M * ‖x - xStar‖ ^ 2`. -/
theorem minimizerValue_upperBound_of_hessianQuadratic_bounds
    (hMin : IsLocalMin f xStar)
    (hC2 : ContDiffOn ℝ 2 f B)
    (x : Point) (M : ℝ)
    (hUpper :
      ∀ z ∈ B, ∀ y : Point,
        inner ℝ y ((fderiv ℝ (∇ f) z) y) ≤ M * ‖y‖ ^ 2)
    (hx : x ∈ B) :
    f x - f xStar ≤ (1 / 2 : ℝ) * M * ‖x - xStar‖ ^ 2 := by
  let d : Point := x - xStar
  have h_segment : segment ℝ xStar x ⊆ B :=
    segment_subset_ball_of_mem_ball (xStar := xStar) (ε := ε) hx
  have h_segment_line : segment ℝ xStar (xStar + (1 : ℝ) • d) ⊆ B := by
    simpa [d, one_smul, sub_eq_add_neg, add_assoc] using h_segment
  have hweighted_int :=
    weighted_hessianQuadratic_intervalIntegrable (f := f) (xStar := xStar) (ε := ε) hC2 hx
  have hupper_int :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t) * (M * ‖d‖ ^ 2)) MeasureTheory.volume 0 1 :=
    (by continuity : Continuous fun t : ℝ ↦ (1 - t) * (M * ‖d‖ ^ 2)).intervalIntegrable 0 1
  have hmono :
      ∫ t in (0 : ℝ)..1,
        (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) ≤
      ∫ t in (0 : ℝ)..1, (1 - t) * (M * ‖d‖ ^ 2) := by
    -- Compare the Taylor remainder integrand against its pointwise upper quadratic bound.
    apply intervalIntegral.integral_mono_on zero_le_one hweighted_int hupper_int
    intro t ht
    have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := Set.mem_uIcc_of_le ht.1 ht.2
    have hz : xStar + t • d ∈ B := by
      simpa [d] using unit_interval_trace_mapsTo_domain xStar d 1 h_segment_line ht'
    have ht_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    exact mul_le_mul_of_nonneg_left (hUpper _ hz d) ht_nonneg
  have hweight_eval :
      ∫ t in (0 : ℝ)..1, (1 - t) * (M * ‖d‖ ^ 2) =
        (1 / 2 : ℝ) * M * ‖d‖ ^ 2 := by
    -- Pull out the constant quadratic factor and evaluate the scalar weight integral.
    rw [intervalIntegral.integral_mul_const, unitInterval_integral_one_sub]
    ring
  have hvalue_eq :
      f x - f xStar =
        ∫ t in (0 : ℝ)..1,
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) :=
    value_sub_eq_intervalIntegral_hessianQuadratic (f := f) (xStar := xStar) (ε := ε) hMin hC2 hx
  calc
    f x - f xStar =
        ∫ t in (0 : ℝ)..1,
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) := hvalue_eq
    _ ≤ ∫ t in (0 : ℝ)..1, (1 - t) * (M * ‖d‖ ^ 2) := hmono
    _ = (1 / 2 : ℝ) * M * ‖d‖ ^ 2 := hweight_eval

/-- Chapter02 Lemma 2.2.7 (3): if `xStar` is a local minimizer of `f`, `f` is twice
continuously differentiable on `Metric.ball xStar ε`, and the Hessian quadratic form satisfies
`m * ‖y‖ ^ 2 ≤ inner ℝ y ((fderiv ℝ (∇ f) z) y)` for every `z ∈ Metric.ball xStar ε` and `y`,
then every `x ∈ Metric.ball xStar ε` satisfies the gradient lower bound
`m * ‖x - xStar‖ ≤ ‖∇ f x‖`. -/
theorem minimizerGradientNorm_lowerBound_of_hessianQuadratic_bounds
    (hMin : IsLocalMin f xStar)
    (hC2 : ContDiffOn ℝ 2 f B)
    (x : Point) (m : ℝ)
    (hLower :
      ∀ z ∈ B, ∀ y : Point,
        m * ‖y‖ ^ 2 ≤ inner ℝ y ((fderiv ℝ (∇ f) z) y))
    (hx : x ∈ B) :
    m * ‖x - xStar‖ ≤ ‖∇ f x‖ := by
  let d : Point := x - xStar
  have h_segment : segment ℝ xStar x ⊆ B :=
    segment_subset_ball_of_mem_ball (xStar := xStar) (ε := ε) hx
  have h_segment_line : segment ℝ xStar (xStar + (1 : ℝ) • d) ⊆ B := by
    simpa [d, one_smul, sub_eq_add_neg, add_assoc] using h_segment
  have hquad_int :=
    hessianQuadratic_intervalIntegrable (f := f) (xStar := xStar) (ε := ε) hC2 hx
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ ↦ m * ‖d‖ ^ 2) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hpair_eq :
      inner ℝ (∇ f x) d =
        ∫ t in (0 : ℝ)..1, inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) :=
    gradient_pairing_eq_intervalIntegral_hessianQuadratic
      (f := f) (xStar := xStar) (ε := ε) hMin hC2 hx
  have hpair_lower :
      m * ‖d‖ ^ 2 ≤ inner ℝ (∇ f x) d := by
    have hmono :
        ∫ t in (0 : ℝ)..1, m * ‖d‖ ^ 2 ≤
          ∫ t in (0 : ℝ)..1, inner ℝ d ((fderiv ℝ (∇ f) (xStar + t • d)) d) := by
      -- Integrate the pointwise Hessian lower bound along the segment.
      apply intervalIntegral.integral_mono_on zero_le_one hconst_int hquad_int
      intro t ht
      have ht' : t ∈ Set.uIcc (0 : ℝ) 1 := Set.mem_uIcc_of_le ht.1 ht.2
      have hz : xStar + t • d ∈ B := by
        simpa [d] using unit_interval_trace_mapsTo_domain xStar d 1 h_segment_line ht'
      exact hLower _ hz d
    simpa [hpair_eq] using hmono
  by_cases hzero : x = xStar
  · -- At the minimizer itself, the claimed lower bound is the trivial inequality `0 ≤ ‖∇ f xStar‖`.
    subst hzero
    simp
  · have hd_nonzero : d ≠ 0 := by
      simpa [d, sub_eq_zero] using hzero
    have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_nonzero
    have hnorm_sq :
        ‖d‖ ^ 2 = ‖d‖ * ‖d‖ := by
      rw [pow_two]
    have hpair_upper : inner ℝ (∇ f x) d ≤ ‖∇ f x‖ * ‖d‖ :=
      real_inner_le_norm _ _
    have hmul :
        m * ‖d‖ * ‖d‖ ≤ ‖∇ f x‖ * ‖d‖ := by
      simpa [hnorm_sq, mul_assoc] using hpair_lower.trans hpair_upper
    -- Divide by the positive displacement norm to conclude the gradient lower bound.
    exact le_of_mul_le_mul_right hmul hd_pos

end
