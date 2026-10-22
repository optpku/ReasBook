/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Algorithm_2_5_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Lemma_2_2_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_9
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib
import Mathlib.Topology.Order.IntermediateValue

open scoped Gradient

-- Semantic recall: the Chapter 2 owner for the sufficient-decrease test is
-- `armijoBacktrackingAccepts`, and the existing bridge
-- `StrongConvexOn.gradientStrongMonotone_univ` already converts the canonical owner
-- `StrongConvexOn Set.univ η f` into the source-facing gradient strong-monotonicity
-- hypothesis used here. No mathlib theorem directly matches this inexact line-search
-- decrease estimate, so the main result stays source-facing while reusing those owners.

section Theorem258

variable {Point : Type} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [CompleteSpace Point]

/-- Helper for Chapter02 Theorem 2.5.8: the Hessian quadratic form exposed by
`iteratedFDeriv ℝ 2 f` matches the derivative of the gradient in the search direction. -/
lemma hessianQuadratic_eq_fderivGradient
    (f : Point → ℝ) (hContDiff : ContDiff ℝ 2 f) (x y : Point) :
    inner ℝ y ((fderiv ℝ (∇ f) x) y) = (iteratedFDeriv ℝ 2 f x) ![y, y] := by
  let T : StrongDual ℝ Point →L[ℝ] Point :=
    ((InnerProductSpace.toDual ℝ Point).symm).toContinuousLinearEquiv.toContinuousLinearMap
  -- Differentiate the bundled derivative once, then transport it through the Riesz isomorphism.
  have hfdContDiff : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    (hContDiff.contDiffAt : ContDiffAt ℝ 2 f x).fderiv_right (m := 1) (by norm_num)
  have hfderiv : HasFDerivAt (fun z ↦ fderiv ℝ f z) (fderiv ℝ (fderiv ℝ f) x) x :=
    (hfdContDiff.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp0 := T.hasFDerivAt.comp x hfderiv
  have hcomp :
      HasFDerivAt
        (fun z ↦ ((InnerProductSpace.toDual ℝ Point).symm) (fderiv ℝ f z))
        (T.comp (fderiv ℝ (fderiv ℝ f) x)) x := by
    convert hcomp0 using 1
    ext z
    rfl
  have hgradFn : (∇ f) = fun z ↦ ((InnerProductSpace.toDual ℝ Point).symm) (fderiv ℝ f z) := by
    funext z
    rfl
  have hgrad :
      fderiv ℝ (∇ f) x = T.comp (fderiv ℝ (fderiv ℝ f) x) := by
    rw [hgradFn]
    exact hcomp.fderiv
  rw [hgrad, iteratedFDeriv_two_apply]
  rw [ContinuousLinearMap.comp_apply, real_inner_comm]
  change inner ℝ (T ((fderiv ℝ (fderiv ℝ f) x) y)) y = ((fderiv ℝ (fderiv ℝ f) x) y) y
  -- Evaluating the inverse Riesz map inside an inner product recovers the original functional.
  show inner ℝ (((InnerProductSpace.toDual ℝ Point).symm) ((fderiv ℝ (fderiv ℝ f) x) y)) y =
      ((fderiv ℝ (fderiv ℝ f) x) y) y
  simpa using (InnerProductSpace.toDual ℝ Point).apply_symm_apply ((fderiv ℝ (fderiv ℝ f) x) y) y

/-- Helper for Chapter02 Theorem 2.5.8: the weight `1 - t` integrates to `1 / 2` on `[0, 1]`. -/
lemma unitIntervalIntegral_one_sub_eq_half :
    ∫ t in (0 : ℝ)..1, (1 - t) = (1 / 2 : ℝ) := by
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hid : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  -- Split the affine weight into its constant and identity parts.
  rw [intervalIntegral.integral_sub hconst hid, intervalIntegral.integral_const, integral_id]
  norm_num

/-- Helper for Chapter02 Theorem 2.5.8: a global lower Hessian bound yields the usual quadratic
Taylor lower model on every search ray. -/
lemma lineSearchObjective_ge_tangent_plus_halfMul_stepNormSq_of_hessianLowerBound
    (f : Point → ℝ) (m : ℝ)
    (hContDiff : ContDiff ℝ 2 f)
    (h_hessianLower :
      ∀ z y : Point, m * ‖y‖ ^ 2 ≤ (iteratedFDeriv ℝ 2 f z) ![y, y])
    (x d : Point) (α : ℝ) :
    f (x + α • d) ≥ f x + α * inner ℝ (∇ f x) d + (m / 2) * ‖α • d‖ ^ 2 := by
  have hTaylor :=
    lineTaylorFormula_withIntegralHessianRemainder
      (D := Set.univ) f x d α isOpen_univ (by simp) hContDiff.contDiffOn
  have hGradC1 : ContDiff ℝ 1 (∇ f) := by
    have hfderivC1 : ContDiff ℝ 1 (fderiv ℝ f) :=
      hContDiff.fderiv_right (m := 1) (by norm_num)
    -- Rewrite the gradient through the Riesz isomorphism to inherit `C¹` regularity.
    change ContDiff ℝ 1 (fun z ↦ ((InnerProductSpace.toDual ℝ Point).symm) (fderiv ℝ f z))
    exact (InnerProductSpace.toDual ℝ Point).symm.contDiff.comp hfderivC1
  have hquad_int :
      IntervalIntegrable
        (fun t : ℝ ↦
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d))
        MeasureTheory.volume 0 1 := by
    have hcont_apply :
        Continuous fun p : Point × Point ↦ (fderiv ℝ (∇ f) p.1 : Point →L[ℝ] Point) p.2 :=
      hGradC1.continuous_fderiv_apply (by norm_num)
    have hpair : Continuous fun t : ℝ ↦ (x + (t * α) • d, d) := by
      continuity
    have hcore :
        Continuous fun t : ℝ ↦ inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) :=
      continuous_const.inner (hcont_apply.comp hpair)
    exact ((continuous_const.sub continuous_id).mul hcore).intervalIntegrable 0 1
  have hlower_int :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t) * (m * ‖d‖ ^ 2)) MeasureTheory.volume 0 1 := by
    exact ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hpointwise :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (1 - t) * (m * ‖d‖ ^ 2) ≤
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) := by
    intro t ht
    have ht_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hbound := h_hessianLower (x + (t * α) • d) d
    have hbound' :
        m * ‖d‖ ^ 2 ≤ inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) := by
      simpa [hessianQuadratic_eq_fderivGradient f hContDiff (x + (t * α) • d) d] using hbound
    exact mul_le_mul_of_nonneg_left hbound' ht_nonneg
  have hmono :
      ∫ t in (0 : ℝ)..1, (1 - t) * (m * ‖d‖ ^ 2) ≤
        ∫ t in (0 : ℝ)..1,
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) :=
    intervalIntegral.integral_mono_on zero_le_one hlower_int hquad_int hpointwise
  have hweight_eval :
      ∫ t in (0 : ℝ)..1, (1 - t) * (m * ‖d‖ ^ 2) = (m / 2) * ‖d‖ ^ 2 := by
    -- Pull the constant quadratic term out of the unit-interval weight integral.
    rw [intervalIntegral.integral_mul_const, unitIntervalIntegral_one_sub_eq_half]
    ring
  have hscaled :
      α ^ (2 : ℕ) * ((m / 2) * ‖d‖ ^ 2) = (m / 2) * ‖α • d‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have habs : α ^ (2 : ℕ) * ‖d‖ ^ 2 = (|α| * ‖d‖) ^ (2 : ℕ) := by
      calc
        α ^ (2 : ℕ) * ‖d‖ ^ 2 = |α| ^ (2 : ℕ) * ‖d‖ ^ 2 := by rw [← sq_abs α]
        _ = (|α| * ‖d‖) ^ (2 : ℕ) := by ring
    rw [show α ^ (2 : ℕ) * ((m / 2) * ‖d‖ ^ 2) = (m / 2) * (α ^ (2 : ℕ) * ‖d‖ ^ 2) by ring,
      habs]
  -- Compare the Taylor remainder integral against the constant lower quadratic bound.
  calc
    f (x + α • d)
        = f x + α * inner ℝ (∇ f x) d +
            α ^ (2 : ℕ) *
              ∫ t in (0 : ℝ)..1,
                (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) := by
          simpa [lineSearchObjective_apply] using hTaylor
    _ ≥ f x + α * inner ℝ (∇ f x) d +
          α ^ (2 : ℕ) * ∫ t in (0 : ℝ)..1, (1 - t) * (m * ‖d‖ ^ 2) := by
          have hscaled_mono :
              α ^ (2 : ℕ) * ∫ t in (0 : ℝ)..1, (1 - t) * (m * ‖d‖ ^ 2) ≤
                α ^ (2 : ℕ) *
                  ∫ t in (0 : ℝ)..1,
                    (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) :=
            mul_le_mul_of_nonneg_left hmono (sq_nonneg α)
          linarith
    _ = f x + α * inner ℝ (∇ f x) d + (m / 2) * ‖α • d‖ ^ 2 := by
          rw [hweight_eval, hscaled]

/-- Helper for Chapter02 Theorem 2.5.8: a global upper Hessian bound yields the matching
quadratic Taylor upper model on every search ray. -/
lemma lineSearchObjective_le_tangent_plus_halfMul_stepNormSq_of_hessianUpperBound
    (f : Point → ℝ) (M : ℝ)
    (hContDiff : ContDiff ℝ 2 f)
    (h_hessianUpper :
      ∀ z y : Point, (iteratedFDeriv ℝ 2 f z) ![y, y] ≤ M * ‖y‖ ^ 2)
    (x d : Point) (α : ℝ) :
    f (x + α • d) ≤ f x + α * inner ℝ (∇ f x) d + (M / 2) * ‖α • d‖ ^ 2 := by
  have hTaylor :=
    lineTaylorFormula_withIntegralHessianRemainder
      (D := Set.univ) f x d α isOpen_univ (by simp) hContDiff.contDiffOn
  have hGradC1 : ContDiff ℝ 1 (∇ f) := by
    have hfderivC1 : ContDiff ℝ 1 (fderiv ℝ f) :=
      hContDiff.fderiv_right (m := 1) (by norm_num)
    -- Rewrite the gradient through the Riesz isomorphism to inherit `C¹` regularity.
    change ContDiff ℝ 1 (fun z ↦ ((InnerProductSpace.toDual ℝ Point).symm) (fderiv ℝ f z))
    exact (InnerProductSpace.toDual ℝ Point).symm.contDiff.comp hfderivC1
  have hquad_int :
      IntervalIntegrable
        (fun t : ℝ ↦
          (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d))
        MeasureTheory.volume 0 1 := by
    have hcont_apply :
        Continuous fun p : Point × Point ↦ (fderiv ℝ (∇ f) p.1 : Point →L[ℝ] Point) p.2 :=
      hGradC1.continuous_fderiv_apply (by norm_num)
    have hpair : Continuous fun t : ℝ ↦ (x + (t * α) • d, d) := by
      continuity
    have hcore :
        Continuous fun t : ℝ ↦ inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) :=
      continuous_const.inner (hcont_apply.comp hpair)
    exact ((continuous_const.sub continuous_id).mul hcore).intervalIntegrable 0 1
  have hupper_int :
      IntervalIntegrable (fun t : ℝ ↦ (1 - t) * (M * ‖d‖ ^ 2)) MeasureTheory.volume 0 1 := by
    exact ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hpointwise :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) ≤
          (1 - t) * (M * ‖d‖ ^ 2) := by
    intro t ht
    have ht_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hbound := h_hessianUpper (x + (t * α) • d) d
    have hbound' :
        inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) ≤ M * ‖d‖ ^ 2 := by
      simpa [hessianQuadratic_eq_fderivGradient f hContDiff (x + (t * α) • d) d] using hbound
    exact mul_le_mul_of_nonneg_left hbound' ht_nonneg
  have hmono :
      ∫ t in (0 : ℝ)..1,
        (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) ≤
      ∫ t in (0 : ℝ)..1, (1 - t) * (M * ‖d‖ ^ 2) :=
    intervalIntegral.integral_mono_on zero_le_one hquad_int hupper_int hpointwise
  have hweight_eval :
      ∫ t in (0 : ℝ)..1, (1 - t) * (M * ‖d‖ ^ 2) = (M / 2) * ‖d‖ ^ 2 := by
    -- Pull the constant quadratic term out of the unit-interval weight integral.
    rw [intervalIntegral.integral_mul_const, unitIntervalIntegral_one_sub_eq_half]
    ring
  have hscaled :
      α ^ (2 : ℕ) * ((M / 2) * ‖d‖ ^ 2) = (M / 2) * ‖α • d‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have habs : α ^ (2 : ℕ) * ‖d‖ ^ 2 = (|α| * ‖d‖) ^ (2 : ℕ) := by
      calc
        α ^ (2 : ℕ) * ‖d‖ ^ 2 = |α| ^ (2 : ℕ) * ‖d‖ ^ 2 := by rw [← sq_abs α]
        _ = (|α| * ‖d‖) ^ (2 : ℕ) := by ring
    rw [show α ^ (2 : ℕ) * ((M / 2) * ‖d‖ ^ 2) = (M / 2) * (α ^ (2 : ℕ) * ‖d‖ ^ 2) by ring,
      habs]
  -- Compare the Taylor remainder integral against the constant upper quadratic bound.
  calc
    f (x + α • d)
        = f x + α * inner ℝ (∇ f x) d +
            α ^ (2 : ℕ) *
              ∫ t in (0 : ℝ)..1,
                (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) := by
          simpa [lineSearchObjective_apply] using hTaylor
    _ ≤ f x + α * inner ℝ (∇ f x) d +
          α ^ (2 : ℕ) * ∫ t in (0 : ℝ)..1, (1 - t) * (M * ‖d‖ ^ 2) := by
          have hscaled_mono :
              α ^ (2 : ℕ) *
                  ∫ t in (0 : ℝ)..1,
                    (1 - t) * inner ℝ d ((fderiv ℝ (∇ f) (x + (t * α) • d)) d) ≤
                α ^ (2 : ℕ) * ∫ t in (0 : ℝ)..1, (1 - t) * (M * ‖d‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hmono (sq_nonneg α)
          linarith
    _ = f x + α * inner ℝ (∇ f x) d + (M / 2) * ‖α • d‖ ^ 2 := by
          rw [hweight_eval, hscaled]

/-- Helper for Chapter02 Theorem 2.5.8: Armijo acceptance and the lower quadratic model rule out
negative accepted steps, which is enough to isolate the trivial `αk = 0` branch. -/
lemma armijoAcceptedStep_nonneg_of_descent_and_hessianLowerTaylor
    (f : Point → ℝ) (xk dk : Point) (αk ρ m : ℝ)
    (hm_pos : 0 < m)
    (hρ_lt_one : ρ < 1)
    (h_descent : inner ℝ (∇ f xk) dk < 0)
    (h_armijo : armijoBacktrackingAccepts f ρ xk (∇ f xk) dk αk)
    (h_lowerTaylor :
      f (xk + αk • dk) ≥
        f xk + αk * inner ℝ (∇ f xk) dk + (m / 2) * ‖αk • dk‖ ^ 2) :
    0 ≤ αk := by
  by_contra hneg
  have hαk_neg : αk < 0 := lt_of_not_ge hneg
  have h_armijo' := (armijoBacktrackingAccepts_iff f ρ xk (∇ f xk) dk αk).mp h_armijo
  have hquad_nonneg : 0 ≤ (m / 2) * ‖αk • dk‖ ^ 2 := by
    positivity
  have hineq :
      (m / 2) * ‖αk • dk‖ ^ 2 ≤ (ρ - 1) * (αk * inner ℝ (∇ f xk) dk) := by
    linarith
  have hρm1_neg : ρ - 1 < 0 := by linarith
  have hprod_pos : 0 < αk * inner ℝ (∇ f xk) dk :=
    mul_pos_of_neg_of_neg hαk_neg h_descent
  have hrhs_neg : (ρ - 1) * (αk * inner ℝ (∇ f xk) dk) < 0 :=
    mul_neg_of_neg_of_pos hρm1_neg hprod_pos
  linarith

/-- Helper for Chapter02 Theorem 2.5.8: if the endpoint directional derivative is nonpositive,
the same integral comparison as in exact line search yields the half-`η` decrease bound. -/
lemma armijoDecrease_ge_halfEtaStepNormSq_of_endpointSlope_nonpos
    (f : Point → ℝ) (xk dk : Point) (αk η : ℝ)
    (hαk_nonneg : 0 ≤ αk)
    (h_hasGradient : ∀ x : Point, HasGradientAt f (∇ f x) x)
    (h_endpoint_nonpos : inner ℝ (∇ f (xk + αk • dk)) dk ≤ 0)
    (h_gradientStrongMonotone :
      ∀ x z : Point,
        inner ℝ (x - z) (∇ f x - ∇ f z) ≥ η * ‖x - z‖ ^ 2) :
    f xk - f (xk + αk • dk) ≥ (η / 2) * ‖αk • dk‖ ^ 2 := by
  have hψ_int :
      IntervalIntegrable (fun t : ℝ ↦ inner ℝ (∇ f (xk + t • dk)) dk) MeasureTheory.volume 0 αk :=
    ray_gradient_inner_intervalIntegrable f xk dk αk η h_gradientStrongMonotone
  have hnegψ_int :
      IntervalIntegrable (fun t : ℝ ↦ -inner ℝ (∇ f (xk + t • dk)) dk)
        MeasureTheory.volume 0 αk :=
    hψ_int.neg
  have hlower_int :
      IntervalIntegrable (fun t : ℝ ↦ η * (αk - t) * ‖dk‖ ^ 2) MeasureTheory.volume 0 αk := by
    exact (by
      continuity : Continuous fun t : ℝ ↦ η * (αk - t) * ‖dk‖ ^ 2).intervalIntegrable 0 αk
  -- Rewrite the achieved decrease as the integral of the negative ray derivative.
  have hdecrease_eq :
      f xk - f (xk + αk • dk) =
        ∫ t in 0..αk, -inner ℝ (∇ f (xk + t • dk)) dk := by
    have hftc :
        ∫ t in 0..αk, inner ℝ (∇ f (xk + t • dk)) dk =
          f (xk + αk • dk) - f xk := by
      have hftc' :
          ∫ t in 0..αk, inner ℝ (∇ f (xk + t • dk)) dk =
            lineSearchObjective f xk dk αk - lineSearchObjective f xk dk 0 := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := lineSearchObjective f xk dk) ?_ hψ_int
        intro t ht
        have hDiff :
            DifferentiableAt ℝ (lineSearchObjective f xk dk) t := by
          have hray :
              DifferentiableAt ℝ (fun s : ℝ ↦ xk + s • dk) t := by
            simpa using ((differentiableAt_id' t).smul_const dk).const_add xk
          change DifferentiableAt ℝ (fun s : ℝ ↦ f (xk + s • dk)) t
          exact (h_hasGradient (xk + t • dk)).differentiableAt.comp t hray
        have hDerivEq :
            deriv (lineSearchObjective f xk dk) t =
              inner ℝ (∇ f (xk + t • dk)) dk :=
          (h_hasGradient (xk + t • dk)).deriv_lineSearchObjective_apply
            (x := xk) (d := dk) (t := t)
        exact hDerivEq ▸ hDiff.hasDerivAt
      simpa [lineSearchObjective_apply, lineSearchObjective_zero] using hftc'
    calc
      f xk - f (xk + αk • dk) = -(f (xk + αk • dk) - f xk) := by ring
      _ = -(∫ t in 0..αk, inner ℝ (∇ f (xk + t • dk)) dk) := by rw [hftc]
      _ = ∫ t in 0..αk, -inner ℝ (∇ f (xk + t • dk)) dk := by
        rw [intervalIntegral.integral_neg]
  -- Strong monotonicity along the ray bounds each negative directional derivative from below.
  have hpointwise :
      ∀ t ∈ Set.Icc 0 αk,
        η * (αk - t) * ‖dk‖ ^ 2 ≤ -inner ℝ (∇ f (xk + t • dk)) dk := by
    intro t ht
    by_cases hEq : αk = t
    · subst hEq
      simpa using neg_nonneg.mpr h_endpoint_nonpos
    have hfac_nonneg : 0 ≤ αk - t := sub_nonneg.mpr ht.2
    have hfac_pos : 0 < αk - t := by
      refine lt_of_le_of_ne hfac_nonneg ?_
      simpa [sub_eq_zero, eq_comm] using hEq
    have hmono := h_gradientStrongMonotone (xk + αk • dk) (xk + t • dk)
    have hsub_ray : (xk + αk • dk) - (xk + t • dk) = (αk - t) • dk := by
      calc
        (xk + αk • dk) - (xk + t • dk) = xk + αk • dk + -(xk + t • dk) := by
          simp [sub_eq_add_neg]
        _ = αk • dk - t • dk := by abel
        _ = (αk - t) • dk := by rw [sub_smul]
    have hrewrite_left :
        inner ℝ ((xk + αk • dk) - (xk + t • dk))
          (∇ f (xk + αk • dk) - ∇ f (xk + t • dk)) =
            (αk - t) *
              (inner ℝ (∇ f (xk + αk • dk)) dk -
                inner ℝ (∇ f (xk + t • dk)) dk) := by
      rw [hsub_ray, real_inner_smul_left, inner_sub_right,
        real_inner_comm dk (∇ f (xk + αk • dk)), real_inner_comm dk (∇ f (xk + t • dk))]
    have hnorm_ray :
        ‖(xk + αk • dk) - (xk + t • dk)‖ ^ 2 =
          (αk - t) * ((αk - t) * ‖dk‖ ^ 2) := by
      rw [hsub_ray, norm_smul, Real.norm_eq_abs, abs_of_nonneg hfac_nonneg, pow_two]
      ring
    have hrewrite_right :
        η * ‖(xk + αk • dk) - (xk + t • dk)‖ ^ 2 =
          (αk - t) * (η * (αk - t) * ‖dk‖ ^ 2) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun r : ℝ ↦ η * r) hnorm_ray
    rw [hrewrite_left, hrewrite_right] at hmono
    have hscaled :
        (αk - t) * (η * (αk - t) * ‖dk‖ ^ 2) ≤
          (αk - t) *
            (inner ℝ (∇ f (xk + αk • dk)) dk -
              inner ℝ (∇ f (xk + t • dk)) dk) := by
      linarith
    have hstep :
        η * (αk - t) * ‖dk‖ ^ 2 ≤
          inner ℝ (∇ f (xk + αk • dk)) dk -
            inner ℝ (∇ f (xk + t • dk)) dk :=
      le_of_mul_le_mul_left hscaled hfac_pos
    linarith
  have hintegral_lower :
      ∫ t in 0..αk, η * (αk - t) * ‖dk‖ ^ 2 ≤
        ∫ t in 0..αk, -inner ℝ (∇ f (xk + t • dk)) dk :=
    intervalIntegral.integral_mono_on hαk_nonneg hlower_int hnegψ_int hpointwise
  calc
    f xk - f (xk + αk • dk) =
        ∫ t in 0..αk, -inner ℝ (∇ f (xk + t • dk)) dk := hdecrease_eq
    _ ≥ ∫ t in 0..αk, η * (αk - t) * ‖dk‖ ^ 2 := hintegral_lower
    _ = (η / 2) * ‖αk • dk‖ ^ 2 :=
      integral_affine_lineSearch_lowerBound dk αk η

/-- Helper for Chapter02 Theorem 2.5.8: a positive endpoint slope on the search ray forces an
interior stationary point by the intermediate value theorem. -/
lemma exists_stationaryRayPoint_between_of_endpointSlope_pos
    (f : Point → ℝ) (xk dk : Point) (αk : ℝ)
    (hαk_pos : 0 < αk)
    (hContDiff : ContDiff ℝ 2 f)
    (h_descent : inner ℝ (∇ f xk) dk < 0)
    (h_endpoint_pos : 0 < inner ℝ (∇ f (xk + αk • dk)) dk) :
    ∃ αStar ∈ Set.Ioo 0 αk, inner ℝ (∇ f (xk + αStar • dk)) dk = 0 := by
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (xk + t • dk)) dk
  -- The ray derivative is continuous because the bundled derivative of a `C²` function is.
  have hψ_eq :
      ψ = fun t : ℝ ↦ (fderiv ℝ f (xk + t • dk)) dk := by
    funext t
    simp [ψ, inner_gradient_left]
  have hψ_cont : Continuous ψ := by
    rw [hψ_eq]
    have hcont_apply :
        Continuous fun p : Point × Point ↦ (fderiv ℝ f p.1 : Point →L[ℝ] ℝ) p.2 :=
      hContDiff.continuous_fderiv_apply (by norm_num)
    have hpair :
        Continuous fun t : ℝ ↦ (xk + t • dk, dk) := by
      continuity
    exact hcont_apply.comp hpair
  have hzero_between : (0 : ℝ) ∈ Set.Ioo (ψ 0) (ψ αk) := by
    constructor
    · simpa [ψ] using h_descent
    · simpa [ψ] using h_endpoint_pos
  obtain ⟨αStar, hαStar_mem, hαStar_zero⟩ :=
    intermediate_value_Ioo hαk_pos.le hψ_cont.continuousOn hzero_between
  refine ⟨αStar, hαStar_mem, ?_⟩
  simpa [ψ] using hαStar_zero

/-- Helper for Chapter02 Theorem 2.5.8: the base point `xk` is the left endpoint when the ray
is recentered at the stationary point `xk + αStar • dk`. -/
lemma stationaryRayCenteredLeftEndpoint
    (xk dk : Point) (αStar : ℝ) :
    xk = (xk + αStar • dk) + αStar • (-dk) := by
  -- Recenter the left endpoint at the stationary point without changing the geometry.
  calc
    xk = xk + αStar • (dk + -dk) := by simp
    _ = xk + (αStar • dk + αStar • (-dk)) := by rw [smul_add]
    _ = (xk + αStar • dk) + αStar • (-dk) := by abel

/-- Helper for Chapter02 Theorem 2.5.8: the accepted point `xk + αk • dk` is the right endpoint
when the ray is recentered at `xk + αStar • dk`. -/
lemma stationaryRayCenteredRightEndpoint
    (xk dk : Point) (αk αStar : ℝ) :
    xk + αk • dk = (xk + αStar • dk) + (αk - αStar) • dk := by
  -- Split the accepted step into the stationary offset plus the remaining displacement.
  symm
  calc
    (xk + αStar • dk) + (αk - αStar) • dk = xk + (αStar • dk + (αk - αStar) • dk) := by
      abel
    _ = xk + (αStar + (αk - αStar)) • dk := by rw [← add_smul]
    _ = xk + αk • dk := by ring_nf

/-- Helper for Chapter02 Theorem 2.5.8: expanding around the stationary ray point converts the
two-sided Hessian bounds into the quadratic estimates used in the positive-endpoint branch. -/
lemma stationaryRayQuadraticBounds_of_hessianBounds
    (f : Point → ℝ) (xk dk : Point) (αk αStar m M : ℝ)
    (hContDiff : ContDiff ℝ 2 f)
    (hαStar_mem : αStar ∈ Set.Icc 0 αk)
    (h_stationary : inner ℝ (∇ f (xk + αStar • dk)) dk = 0)
    (h_hessianBounds :
      ∀ x y : Point,
        m * ‖y‖ ^ 2 ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ∧
          (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖ ^ 2) :
    f xk - f (xk + αStar • dk) ≤ (M / 2) * ‖αStar • dk‖ ^ 2 ∧
      (m / 2) * ‖(αk - αStar) • dk‖ ^ 2 ≤
        f (xk + αk • dk) - f (xk + αStar • dk) := by
  -- Route correction: the remaining work is to normalize the centered equalities
  -- `xk = (xk + αStar • dk) + αStar • (-dk)` and
  -- `xk + αk • dk = (xk + αStar • dk) + (αk - αStar) • dk`, then feed the already-proved
  -- lower/upper Taylor-model helpers through those normal forms.
  let xStar : Point := xk + αStar • dk
  have h_stationary_xStar : inner ℝ (∇ f xStar) dk = 0 := by
    simpa [xStar] using h_stationary
  have h_stationary_neg : inner ℝ (∇ f xStar) (-dk) = 0 := by
    simpa [xStar, inner_neg_right] using h_stationary
  have h_leftEndpoint : xk = xStar + αStar • (-dk) := by
    simpa [xStar] using stationaryRayCenteredLeftEndpoint xk dk αStar
  have h_rightEndpoint : xk + αk • dk = xStar + (αk - αStar) • dk := by
    simpa [xStar] using stationaryRayCenteredRightEndpoint xk dk αk αStar
  have h_upperTaylor :=
    lineSearchObjective_le_tangent_plus_halfMul_stepNormSq_of_hessianUpperBound
      f M hContDiff (fun x y ↦ (h_hessianBounds x y).2) xStar (-dk) αStar
  have h_lowerTaylor :=
    lineSearchObjective_ge_tangent_plus_halfMul_stepNormSq_of_hessianLowerBound
      f m hContDiff (fun x y ↦ (h_hessianBounds x y).1) xStar dk (αk - αStar)
  -- Apply the upper Taylor model to the recentered left endpoint and kill the linear term
  -- by the stationarity equation.
  have h_upperAux :
      f xk ≤ f xStar + (M / 2) * ‖αStar • dk‖ ^ 2 := by
    have h_upperAux0 :
        f xk ≤
          f xStar + αStar * inner ℝ (∇ f xStar) (-dk) +
            (M / 2) * ‖αStar • (-dk)‖ ^ 2 := by
      simpa [h_leftEndpoint] using h_upperTaylor
    simpa [h_stationary_neg, smul_neg] using h_upperAux0
  have h_upper :
      f xk - f xStar ≤ (M / 2) * ‖αStar • dk‖ ^ 2 := by
    linarith
  -- Apply the lower Taylor model to the recentered right endpoint and again use stationarity
  -- to remove the first-order term.
  have h_lowerAux :
      f (xk + αk • dk) ≥
        f xStar + (m / 2) * ‖(αk - αStar) • dk‖ ^ 2 := by
    have h_lowerAux0 :
        f (xk + αk • dk) ≥
          f xStar + (αk - αStar) * inner ℝ (∇ f xStar) dk +
            (m / 2) * ‖(αk - αStar) • dk‖ ^ 2 := by
      simpa [h_rightEndpoint] using h_lowerTaylor
    simpa [h_stationary_xStar] using h_lowerAux0
  have h_lower :
      (m / 2) * ‖(αk - αStar) • dk‖ ^ 2 ≤
        f (xk + αk • dk) - f xStar := by
    linarith
  exact ⟨by simpa [xStar] using h_upper, by simpa [xStar] using h_lower⟩

/-- Helper for Chapter02 Theorem 2.5.8: once the common nonzero direction norm is cancelled, the
strict quadratic comparison along the ray becomes a scalar square comparison in `αk` and `αStar`.
-/
lemma stationaryRayScalarSquareComparison_of_normSq
    (dk : Point) (αk αStar m M : ℝ)
    (hdk_ne : dk ≠ 0)
    (hαStar_nonneg : 0 ≤ αStar)
    (hαStar_le : αStar ≤ αk)
    (h_normSq :
      (m / 2) * ‖(αk - αStar) • dk‖ ^ 2 < (M / 2) * ‖αStar • dk‖ ^ 2) :
    m * (αk - αStar) ^ 2 < M * αStar ^ 2 := by
  have hαdiff_nonneg : 0 ≤ αk - αStar := sub_nonneg.mpr hαStar_le
  have hdk_norm_sq_pos : 0 < ‖dk‖ ^ 2 := by
    have hdk_norm_pos : 0 < ‖dk‖ := norm_pos_iff.mpr hdk_ne
    nlinarith
  -- Rewrite both norms as scalar factors times the same strictly positive `‖dk‖^2`.
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hαdiff_nonneg, abs_of_nonneg hαStar_nonneg] at h_normSq
  nlinarith

/-- Helper for Chapter02 Theorem 2.5.8: the scalar square comparison on the stationary and
accepted steps yields the condition-number control `αk ≤ (1 + √(M / m)) αStar`. -/
lemma stationaryRayConditionNumberBound
    (αk αStar m M : ℝ)
    (hm_pos : 0 < m)
    (hαStar_pos : 0 < αStar)
    (hαStar_lt : αStar < αk)
    (h_squareComparison : m * (αk - αStar) ^ 2 < M * αStar ^ 2) :
    αk ≤ (1 + Real.sqrt (M / m)) * αStar := by
  have hαdiff_pos : 0 < αk - αStar := sub_pos.mpr hαStar_lt
  have hleft_pos : 0 < m * (αk - αStar) ^ 2 := by
    have hsq_pos : 0 < (αk - αStar) ^ 2 := by nlinarith
    exact mul_pos hm_pos hsq_pos
  have hright_pos : 0 < M * αStar ^ 2 := by
    linarith
  have hM_pos : 0 < M := by
    by_contra hM_nonpos
    have hαStar_sq_pos : 0 < αStar ^ 2 := by nlinarith
    have : M * αStar ^ 2 ≤ 0 := by nlinarith
    linarith
  have hratio_nonneg : 0 ≤ M / m := by positivity
  have hdivComparison : (αk - αStar) ^ 2 < (M / m) * αStar ^ 2 := by
    have htmp : (αk - αStar) ^ 2 < (M * αStar ^ 2) / m := by
      exact (lt_div_iff₀ hm_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h_squareComparison)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hsqrtSquare :
      (Real.sqrt (M / m) * αStar) ^ 2 = (M / m) * αStar ^ 2 := by
    calc
      (Real.sqrt (M / m) * αStar) ^ 2 = (Real.sqrt (M / m)) ^ 2 * αStar ^ 2 := by ring
      _ = (M / m) * αStar ^ 2 := by rw [Real.sq_sqrt hratio_nonneg]
  have hsquare_lt :
      (αk - αStar) ^ 2 < (Real.sqrt (M / m) * αStar) ^ 2 := by
    rw [hsqrtSquare]
    exact hdivComparison
  -- Both sides are nonnegative, so the strict square comparison collapses to a linear one.
  have hlinear_lt : αk - αStar < Real.sqrt (M / m) * αStar := by
    have hsqrt_mul_nonneg : 0 ≤ Real.sqrt (M / m) * αStar := by
      positivity
    nlinarith
  nlinarith

/-- Chapter02 Theorem 2.5.8: in the inexact line-search setting, if `αk` satisfies the
sufficient-decrease condition `(2.5.3)` along a descent direction `dk`, formalized as
`armijoBacktrackingAccepts f ρ xk (∇ f xk) dk αk`, `ρ ∈ (0, 1 / 2)`, `f` is globally `C²`,
`∇ f` satisfies the uniform-convexity lower bound `(2.5.27)` with constant `η > 0`, and the
Hessian quadratic form of `f`, written via the canonical owner `iteratedFDeriv ℝ 2 f`,
satisfies the two-sided bounds `(2.5.28)` with `0 < m < M`, then the achieved decrease is
bounded below by `(ρ * η / (1 + Real.sqrt (M / m))) * ‖αk • dk‖^2`, which is `(2.5.29)`. -/
theorem armijoDecrease_ge_rho_mul_eta_div_one_add_sqrt_hessianRatio_mul_stepNormSq
    (f : Point → ℝ) (xk dk : Point) (αk ρ η m M : ℝ)
    (hρ_pos : 0 < ρ)
    (hρ_lt_half : ρ < (1 / 2 : ℝ))
    (hη_pos : 0 < η)
    (hm_pos : 0 < m)
    (hm_lt_M : m < M)
    (hContDiff : ContDiff ℝ 2 f)
    (h_descent : inner ℝ (∇ f xk) dk < 0)
    (h_armijo :
      armijoBacktrackingAccepts f ρ xk (∇ f xk) dk αk)
    (h_gradientStrongMonotone :
      ∀ y z : Point,
        inner ℝ (y - z) (∇ f y - ∇ f z) ≥ η * ‖y - z‖ ^ 2)
    (h_hessianBounds :
      ∀ x y : Point,
        m * ‖y‖ ^ 2 ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ∧
          (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖ ^ 2) :
    f xk - f (xk + αk • dk) ≥
      (ρ * η / (1 + Real.sqrt (M / m))) * ‖αk • dk‖ ^ 2 := by
  -- Route correction: the setup pivot succeeded. The accepted-step sign lemma is now established,
  -- so the remaining work is isolated to the positive-endpoint branch: convert
  -- `stationaryRayQuadraticBounds_of_hessianBounds` into the centered normal form,
  -- extract `αk ≤ (1 + √(M / m)) αStar`, and then combine that with strong monotonicity and
  -- Armijo decrease in the existing two-branch source skeleton.
  have hρ_lt_one : ρ < 1 := by linarith
  have hContDiff1 : ContDiff ℝ 1 f := hContDiff.of_le (by norm_num)
  have h_hasGradient : ∀ x : Point, HasGradientAt f (∇ f x) x := fun x ↦
    (hContDiff1.contDiffAt.differentiableAt_one).hasGradientAt
  have h_lowerTaylor :
      f (xk + αk • dk) ≥
        f xk + αk * inner ℝ (∇ f xk) dk + (m / 2) * ‖αk • dk‖ ^ 2 :=
    lineSearchObjective_ge_tangent_plus_halfMul_stepNormSq_of_hessianLowerBound
      f m hContDiff (fun x y ↦ (h_hessianBounds x y).1) xk dk αk
  have hαk_nonneg :
      0 ≤ αk :=
    armijoAcceptedStep_nonneg_of_descent_and_hessianLowerTaylor
      f xk dk αk ρ m hm_pos hρ_lt_one h_descent h_armijo h_lowerTaylor
  by_cases hαk_zero : αk = 0
  · -- The zero-step branch is the trivial equality case.
    simp [hαk_zero]
  have hαk_pos : 0 < αk := lt_of_le_of_ne hαk_nonneg (by simpa [eq_comm] using hαk_zero)
  by_cases h_endpoint_nonpos : inner ℝ (∇ f (xk + αk • dk)) dk ≤ 0
  · -- The nonpositive-endpoint branch is exactly the already-proved half-`η` estimate.
    have hhalfDecrease :
        (η / 2) * ‖αk • dk‖ ^ 2 ≤ f xk - f (xk + αk • dk) := by
      simpa using
        armijoDecrease_ge_halfEtaStepNormSq_of_endpointSlope_nonpos
          f xk dk αk η hαk_nonneg h_hasGradient h_endpoint_nonpos h_gradientStrongMonotone
    have hden_ge_one : 1 ≤ 1 + Real.sqrt (M / m) := by
      nlinarith [Real.sqrt_nonneg (M / m)]
    have hcoeff_nonneg : 0 ≤ ρ * η := by positivity
    have hcoeff_div_le :
        ρ * η / (1 + Real.sqrt (M / m)) ≤ ρ * η := by
      exact div_le_self hcoeff_nonneg hden_ge_one
    have hcoeff_le_half :
        ρ * η ≤ η / 2 := by
      nlinarith
    have hcoeff_step :
        (ρ * η / (1 + Real.sqrt (M / m))) * ‖αk • dk‖ ^ 2 ≤
          (η / 2) * ‖αk • dk‖ ^ 2 := by
      exact
        mul_le_mul_of_nonneg_right
          (le_trans hcoeff_div_le hcoeff_le_half)
          (sq_nonneg ‖αk • dk‖)
    exact le_trans hcoeff_step hhalfDecrease
  · -- In the positive-endpoint branch, recenter at the interior stationary point and use the
    -- stationary Taylor package plus the scalar condition-number comparison.
    have h_endpoint_pos : 0 < inner ℝ (∇ f (xk + αk • dk)) dk := lt_of_not_ge h_endpoint_nonpos
    obtain ⟨αStar, hαStar_mem, h_stationary⟩ :=
      exists_stationaryRayPoint_between_of_endpointSlope_pos
        f xk dk αk hαk_pos hContDiff h_descent h_endpoint_pos
    obtain ⟨h_upper, h_lower⟩ :=
      stationaryRayQuadraticBounds_of_hessianBounds
        f xk dk αk αStar m M hContDiff
        ⟨hαStar_mem.1.le, hαStar_mem.2.le⟩ h_stationary h_hessianBounds
    have h_armijo' :=
      (armijoBacktrackingAccepts_iff f ρ xk (∇ f xk) dk αk).mp h_armijo
    have h_strictDescent : f (xk + αk • dk) < f xk := by
      have hprod_neg : ρ * αk * inner ℝ (∇ f xk) dk < 0 := by
        exact mul_neg_of_pos_of_neg (mul_pos hρ_pos hαk_pos) h_descent
      have h_rhs_lt : f xk + ρ * αk * inner ℝ (∇ f xk) dk < f xk := by
        linarith
      exact lt_of_le_of_lt h_armijo' h_rhs_lt
    have h_gap_lt :
        f (xk + αk • dk) - f (xk + αStar • dk) <
          f xk - f (xk + αStar • dk) := by
      linarith
    have h_normSq_lt :
        (m / 2) * ‖(αk - αStar) • dk‖ ^ 2 < (M / 2) * ‖αStar • dk‖ ^ 2 := by
      linarith
    have hdk_ne : dk ≠ 0 := by
      intro hdk_zero
      subst hdk_zero
      simpa using h_descent
    have h_squareComparison :
        m * (αk - αStar) ^ 2 < M * αStar ^ 2 :=
      stationaryRayScalarSquareComparison_of_normSq
        dk αk αStar m M hdk_ne hαStar_mem.1.le hαStar_mem.2.le h_normSq_lt
    have h_conditionNumber :
        αk ≤ (1 + Real.sqrt (M / m)) * αStar :=
      stationaryRayConditionNumberBound
        αk αStar m M hm_pos hαStar_mem.1 hαStar_mem.2 h_squareComparison
    have hmono := h_gradientStrongMonotone (xk + αStar • dk) xk
    have hsub_ray : (xk + αStar • dk) - xk = αStar • dk := by
      abel
    have hmono_left :
        inner ℝ ((xk + αStar • dk) - xk)
          (∇ f (xk + αStar • dk) - ∇ f xk) =
            αStar * (-inner ℝ (∇ f xk) dk) := by
      calc
        inner ℝ ((xk + αStar • dk) - xk)
            (∇ f (xk + αStar • dk) - ∇ f xk) =
            αStar * inner ℝ dk (∇ f (xk + αStar • dk) - ∇ f xk) := by
              rw [hsub_ray, real_inner_smul_left]
        _ = αStar * (inner ℝ dk (∇ f (xk + αStar • dk)) - inner ℝ dk (∇ f xk)) := by
              rw [inner_sub_right]
        _ = αStar * (inner ℝ (∇ f (xk + αStar • dk)) dk - inner ℝ (∇ f xk) dk) := by
              rw [real_inner_comm dk (∇ f (xk + αStar • dk)), real_inner_comm dk (∇ f xk)]
        _ = αStar * (-inner ℝ (∇ f xk) dk) := by
              rw [h_stationary, zero_sub]
    have hmono_right :
        η * ‖(xk + αStar • dk) - xk‖ ^ 2 =
          αStar * (η * αStar * ‖dk‖ ^ 2) := by
      rw [hsub_ray, norm_smul, Real.norm_eq_abs, abs_of_nonneg hαStar_mem.1.le, pow_two]
      ring
    rw [hmono_left, hmono_right] at hmono
    have hgradient_lowerScaled :
        αStar * (η * αStar * ‖dk‖ ^ 2) ≤ αStar * (-inner ℝ (∇ f xk) dk) := by
      linarith
    have hgradient_lower :
        η * αStar * ‖dk‖ ^ 2 ≤ -inner ℝ (∇ f xk) dk :=
      le_of_mul_le_mul_left hgradient_lowerScaled hαStar_mem.1
    have harmijoDecrease :
        ρ * αk * (-inner ℝ (∇ f xk) dk) ≤
          f xk - f (xk + αk • dk) := by
      linarith
    have hραk_nonneg : 0 ≤ ρ * αk := by
      positivity
    have hscaledGradient0 :
        ρ * αk * (η * αStar * ‖dk‖ ^ 2) ≤
          ρ * αk * (-inner ℝ (∇ f xk) dk) :=
      mul_le_mul_of_nonneg_left hgradient_lower hραk_nonneg
    have hscaledGradient :
        ρ * η * (αk * αStar * ‖dk‖ ^ 2) ≤
          ρ * αk * (-inner ℝ (∇ f xk) dk) := by
      convert hscaledGradient0 using 1 <;> ring
    have hdecrease_ge_core :
        ρ * η * (αk * αStar * ‖dk‖ ^ 2) ≤ f xk - f (xk + αk • dk) := by
      linarith
    set C : ℝ := 1 + Real.sqrt (M / m)
    have hC_pos : 0 < C := by
      dsimp [C]
      positivity
    have hα_div_le : αk / C ≤ αStar := by
      exact (div_le_iff₀ hC_pos).2 (by simpa [C, mul_comm, mul_left_comm, mul_assoc] using h_conditionNumber)
    have hαsq_div_le : αk * (αk / C) ≤ αk * αStar := by
      exact mul_le_mul_of_nonneg_left hα_div_le hαk_pos.le
    have hnorm_sq :
        ‖αk • dk‖ ^ 2 = αk ^ 2 * ‖dk‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hαk_nonneg, pow_two]
      ring
    have hfactor_nonneg : 0 ≤ ρ * η * ‖dk‖ ^ 2 := by
      positivity
    have htransport0 :
        (ρ * η * ‖dk‖ ^ 2) * (αk * (αk / C)) ≤
          (ρ * η * ‖dk‖ ^ 2) * (αk * αStar) :=
      mul_le_mul_of_nonneg_left hαsq_div_le hfactor_nonneg
    have htransport :
        (ρ * η / C) * ‖αk • dk‖ ^ 2 ≤
          ρ * η * (αk * αStar * ‖dk‖ ^ 2) := by
      rw [hnorm_sq]
      convert htransport0 using 1 <;> ring
    exact le_trans htransport hdecrease_ge_core

/-- Canonical strong-convexity form of Chapter02 Theorem 2.5.8 with the global `C²`
regularity needed for the gradient and Hessian operators to represent the genuine first-
and second-order data of `f`. -/
theorem armijoDecrease_ge_rho_mul_eta_div_one_add_sqrt_hessianRatio_mul_stepNormSq_of_strongConvex
    (f : Point → ℝ) (xk dk : Point) (αk ρ η m M : ℝ)
    (hρ_pos : 0 < ρ)
    (hρ_lt_half : ρ < (1 / 2 : ℝ))
    (hη_pos : 0 < η)
    (hm_pos : 0 < m)
    (hm_lt_M : m < M)
    (hContDiff : ContDiff ℝ 2 f)
    (h_descent : inner ℝ (∇ f xk) dk < 0)
    (h_armijo :
      armijoBacktrackingAccepts f ρ xk (∇ f xk) dk αk)
    (hStrong : StrongConvexOn Set.univ η f)
    (h_hessianBounds :
      ∀ x y : Point,
        m * ‖y‖ ^ 2 ≤ (iteratedFDeriv ℝ 2 f x) ![y, y] ∧
          (iteratedFDeriv ℝ 2 f x) ![y, y] ≤ M * ‖y‖ ^ 2) :
    f xk - f (xk + αk • dk) ≥
      (ρ * η / (1 + Real.sqrt (M / m))) * ‖αk • dk‖ ^ 2 := by
  have hContDiff1 : ContDiff ℝ 1 f := hContDiff.of_le (by norm_num)
  have h_hasGradient : ∀ x : Point, HasGradientAt f (∇ f x) x := fun x ↦
    (hContDiff1.contDiffAt.differentiableAt_one).hasGradientAt
  exact
    armijoDecrease_ge_rho_mul_eta_div_one_add_sqrt_hessianRatio_mul_stepNormSq
      f xk dk αk ρ η m M hρ_pos hρ_lt_half hη_pos hm_pos hm_lt_M hContDiff h_descent
      h_armijo (StrongConvexOn.gradientStrongMonotone_univ hStrong h_hasGradient)
      h_hessianBounds

end Theorem258
