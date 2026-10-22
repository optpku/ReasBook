/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open Set

-- Semantic recall: `Convex.taylor_approx_two_segment` and the one-dimensional Taylor API
-- inform the remainder shape, but no direct multivariate cubic scalar remainder theorem
-- surfaced for this source-facing basepoint Hessian estimate, so the bridge theorem below is
-- stated directly and the canonical `LipschitzOnWith` owner is derived from it.

section Theorem123

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable
  (D : Set E)
  (f : E → ℝ)
  (x d : E)
  (γ : NNReal)

/-- Helper for Chapter01 Theorem 1.2.23: every point of the segment from `x` to `x + d`
belongs to the convex domain `D`. -/
lemma lineMap_mem_domain
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hxd : x + d ∈ D) :
    ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap x (x + d) t ∈ D := by
  intro t ht
  simpa using hD_convex.lineMap_mem hx hxd ht

/-- Helper for Chapter01 Theorem 1.2.23: the line parametrization
`AffineMap.lineMap x (x + d)` has constant derivative `d`. -/
lemma lineMap_deriv :
    deriv (AffineMap.lineMap x (x + d) : ℝ → E) = fun _ ↦ d := by
  funext t
  simpa using
    (AffineMap.hasDerivAt_lineMap (a := x) (b := x + d) (x := t)).deriv

/-- Helper for Chapter01 Theorem 1.2.23: the second derivative of the affine line
parametrization vanishes. -/
lemma lineMap_iteratedDeriv_two :
    iteratedDeriv 2 (AffineMap.lineMap x (x + d) : ℝ → E) = 0 := by
  funext t
  -- After one derivative, the line parametrization becomes the constant function `d`.
  rw [iteratedDeriv_succ, iteratedDeriv_one, lineMap_deriv]
  simp

/-- Helper for Chapter01 Theorem 1.2.23: the second derivative of the line restriction
`t ↦ f (AffineMap.lineMap x (x + d) t)` is the Hessian of `f` evaluated twice on `d`. -/
lemma lineRestriction_iteratedDerivWithin_two
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hf : ContDiffOn ℝ 2 f D)
    (hx : x ∈ D)
    (hxd : x + d ∈ D) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDerivWithin 2 (fun s ↦ f (AffineMap.lineMap x (x + d) s)) (Icc (0 : ℝ) 1) t =
        (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x (x + d) t)) ![d, d] := by
  intro t ht
  let φ : ℝ → E := AffineMap.lineMap x (x + d)
  have hy : φ t ∈ D := lineMap_mem_domain D x d hD_convex hx hxd t ht
  have hfAt : ContDiffAt ℝ 2 f (φ t) :=
    hf.contDiffAt (hD_open.mem_nhds hy)
  have hφAt : ContDiffAt ℝ 2 φ t := by
    simpa [φ] using
      (AffineMap.contDiff_lineMap x (x + d) : ContDiff ℝ 2 (AffineMap.lineMap x (x + d) : ℝ → E)).contDiffAt
  have hCompAt : ContDiffAt ℝ 2 (fun s ↦ f (φ s)) t :=
    hfAt.comp t hφAt
  -- Move from the interval derivative to the global derivative, then use the one-dimensional
  -- Faà di Bruno formula specialized to an affine inner map.
  calc
    iteratedDerivWithin 2 (fun s ↦ f (AffineMap.lineMap x (x + d) s)) (Icc (0 : ℝ) 1) t
        = iteratedDeriv 2 (fun s ↦ f (φ s)) t := by
            simpa [φ] using
              iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one hCompAt ht
    _ = iteratedDeriv 2 (f ∘ φ) t := by
            rfl
    _ = (iteratedFDeriv ℝ 2 f (φ t)) (fun _ ↦ deriv φ t)
          + fderiv ℝ f (φ t) (iteratedDeriv 2 φ t) := by
            simpa [φ, Function.comp] using iteratedDeriv_vcomp_two (g := f) (f := φ) hfAt hφAt
    _ = (iteratedFDeriv ℝ 2 f (φ t)) ![d, d] + fderiv ℝ f (φ t) (iteratedDeriv 2 φ t) := by
            have hφDeriv : deriv φ t = d := by
              simpa [φ] using congrFun (lineMap_deriv (x := x) (d := d)) t
            have hvec : (fun _ : Fin 2 => d) = ![d, d] := by
              funext i
              fin_cases i <;> rfl
            simp [hφDeriv, hvec]
    _ = (iteratedFDeriv ℝ 2 f (φ t)) ![d, d] := by
            have hφTwo : iteratedDeriv 2 φ t = 0 := by
              simpa [φ] using congrFun (lineMap_iteratedDeriv_two (x := x) (d := d)) t
            rw [hφTwo, map_zero, add_zero]

/-- Chapter01 Theorem 1.2.23, source-facing bridge: if `f : E → ℝ` is `C²` on an open convex set
`D` and its Hessian obeys the centered basepoint estimate at `x` on `D` with constant `γ`, then
the quadratic Taylor remainder at `x` is bounded by `((γ : ℝ) / 6) * ‖d‖ ^ 3` for any
`x + d ∈ D`. -/
theorem cubicRemainderBound_of_hessian_basepointLipschitzOn
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (hHessianBasepointLipschitz :
      ∀ y ∈ D,
        ‖iteratedFDeriv ℝ 2 f y - iteratedFDeriv ℝ 2 f x‖ ≤ (γ : ℝ) * ‖y - x‖)
    (hxd : x + d ∈ D) :
    |f (x + d) - (f x + fderiv ℝ f x d + (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![d, d])| ≤
      ((γ : ℝ) / 6) * ‖d‖ ^ 3 := by
  let I : Set ℝ := Icc (0 : ℝ) 1
  let g : ℝ → ℝ := f ∘ AffineMap.lineMap x (x + d)
  let H0 : ℝ := (iteratedFDeriv ℝ 2 f x) ![d, d]
  have hLineMem : ∀ t ∈ I, AffineMap.lineMap x (x + d) t ∈ D :=
    lineMap_mem_domain D x d hD_convex hx hxd
  have hLineContDiff : ContDiff ℝ 2 (AffineMap.lineMap x (x + d) : ℝ → E) := by
    simpa using
      (AffineMap.contDiff_lineMap x (x + d) : ContDiff ℝ 2 (AffineMap.lineMap x (x + d) : ℝ → E))
  have hgContDiff : ContDiffOn ℝ 2 g I := by
    -- Restrict `f` to the segment joining `x` and `x + d`.
    simpa [g] using hf.comp hLineContDiff.contDiffOn hLineMem
  have hgDerivAt0 : HasDerivAt g (fderiv ℝ f x d) 0 := by
    have hfAtx : HasFDerivAt f (fderiv ℝ f x) x :=
      ((hf.contDiffAt (hD_open.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
    -- Differentiate along the affine line at the left endpoint.
    simpa [g] using
      hfAtx.comp_hasDerivAt_of_eq 0
        (AffineMap.hasDerivAt_lineMap (a := x) (b := x + d) (x := 0))
        (AffineMap.lineMap_apply_zero x (x + d)).symm
  have hgTaylorEval :
      taylorWithinEval g 1 I 0 1 = f x + fderiv ℝ f x d := by
    have hgWithinDeriv0 :
        iteratedDerivWithin 1 g I 0 = fderiv ℝ f x d := by
      simpa [I, iteratedDerivWithin_one] using
        hgDerivAt0.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one 0 (by simp [I]))
    -- The order-one Taylor polynomial of `g` at `0` is just the value plus the first derivative.
    rw [taylorWithinEval_succ, taylor_within_zero_eval]
    simp [g, I, hgWithinDeriv0]
  have hgSecond :
      ∀ t ∈ I, iteratedDerivWithin 2 g I t =
        (iteratedFDeriv ℝ 2 f (AffineMap.lineMap x (x + d) t)) ![d, d] :=
    lineRestriction_iteratedDerivWithin_two D f x d hD_open hD_convex hf hx hxd
  have hSecondCont :
      ContinuousOn (iteratedDerivWithin 2 g I) I := by
    exact hgContDiff.continuousOn_iteratedDerivWithin (by norm_num) uniqueDiffOn_Icc_zero_one
  have hTaylorRemainder :
      g 1 - taylorWithinEval g 1 I 0 1 =
        ∫ t in 0..1, (1 - t) * iteratedDerivWithin 2 g I t := by
    -- Apply the integral remainder formula on the unit interval.
    have hgContDiff' : ContDiffOn ℝ (1 + 1) g (uIcc (0 : ℝ) 1) := by
      change ContDiffOn ℝ 2 g (uIcc (0 : ℝ) 1)
      simpa [I] using hgContDiff
    simpa [I, one_smul, pow_one] using
      (taylor_integral_remainder (f := g) (x := 1) (x₀ := 0) (n := 1) hgContDiff')
  have hWeightIntegral : ∫ t in (0 : ℝ)..1, (1 - t) = (1 / 2 : ℝ) := by
    rw [intervalIntegral.integral_sub]
    · norm_num [intervalIntegral.integral_const, integral_id]
    · simpa using
        (continuous_const : Continuous fun _ : ℝ ↦ (1 : ℝ)).intervalIntegrable (0 : ℝ) 1
    · simpa using continuous_id.intervalIntegrable (0 : ℝ) 1
  have hWeightedSquareIntegral : ∫ t in (0 : ℝ)..1, (1 - t) * t = (1 / 6 : ℝ) := by
    rw [show (fun t : ℝ ↦ (1 - t) * t) = fun t : ℝ ↦ t - t ^ 2 by
      funext t
      ring]
    rw [intervalIntegral.integral_sub]
    · norm_num [integral_id, integral_pow]
    · simpa using continuous_id.intervalIntegrable (0 : ℝ) 1
    · simpa using (continuous_id.pow 2).intervalIntegrable (0 : ℝ) 1
  have hRepresentation :
      g 1 - (f x + fderiv ℝ f x d + (1 / 2 : ℝ) * H0) =
        ∫ t in 0..1, (1 - t) * (iteratedDerivWithin 2 g I t - H0) := by
    have hFirstIntegrable :
        IntervalIntegrable (fun t : ℝ ↦ (1 - t) * iteratedDerivWithin 2 g I t)
          MeasureTheory.volume 0 1 := by
      exact ((continuousOn_const.sub continuousOn_id).mul hSecondCont).intervalIntegrable_of_Icc
        (by norm_num)
    have hSecondIntegrable :
        IntervalIntegrable (fun t : ℝ ↦ (1 - t) * H0) MeasureTheory.volume 0 1 := by
      exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).intervalIntegrable_of_Icc
        (by norm_num)
    have hIntSub :
        (∫ t in (0 : ℝ)..1, (1 - t) * iteratedDerivWithin 2 g I t) -
            ∫ t in (0 : ℝ)..1, (1 - t) * H0 =
          ∫ t in (0 : ℝ)..1, ((1 - t) * iteratedDerivWithin 2 g I t - (1 - t) * H0) := by
      rw [← intervalIntegral.integral_sub]
      · exact hFirstIntegrable
      · exact hSecondIntegrable
    -- Subtract the constant Hessian contribution from the integral remainder formula.
    calc
      g 1 - (f x + fderiv ℝ f x d + (1 / 2 : ℝ) * H0)
          = (g 1 - taylorWithinEval g 1 I 0 1) - (1 / 2 : ℝ) * H0 := by
              rw [hgTaylorEval]
              ring
      _ = (∫ t in 0..1, (1 - t) * iteratedDerivWithin 2 g I t) - (1 / 2 : ℝ) * H0 := by
              rw [hTaylorRemainder]
      _ = (∫ t in 0..1, (1 - t) * iteratedDerivWithin 2 g I t) -
            ∫ t in 0..1, (1 - t) * H0 := by
              rw [intervalIntegral.integral_mul_const, hWeightIntegral]
      _ = ∫ t in 0..1, ((1 - t) * iteratedDerivWithin 2 g I t - (1 - t) * H0) := hIntSub
      _ = ∫ t in 0..1, (1 - t) * (iteratedDerivWithin 2 g I t - H0) := by
              congr with t
              ring
  have hPointwiseBound :
      ∀ t ∈ I, |iteratedDerivWithin 2 g I t - H0| ≤ ((γ : ℝ) * ‖d‖ ^ 3) * t := by
    intro t ht
    have hy : AffineMap.lineMap x (x + d) t ∈ D := hLineMem t ht
    let A :
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
        iteratedFDeriv ℝ 2 f (AffineMap.lineMap x (x + d) t) - iteratedFDeriv ℝ 2 f x
    have hEvalBound :
        ‖A ![d, d]‖ ≤ ‖A‖ * ‖d‖ ^ 2 := by
      have hm : ∀ i : Fin 2, ‖(![d, d] : Fin 2 → E) i‖ ≤ ‖d‖ := by
        intro i
        fin_cases i <;> simp
      simpa [A, pow_two] using
        A.le_opNorm_mul_prod_of_le (m := ![d, d]) (b := fun _ : Fin 2 => ‖d‖) hm
    have hDist :
        ‖AffineMap.lineMap x (x + d) t - x‖ = t * ‖d‖ := by
      have ht0 : 0 ≤ t := ht.1
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg ht0, mul_comm] using
        (dist_lineMap_left x (x + d) t)
    -- Convert the scalar Hessian difference into the operator norm estimate supplied by the
    -- Lipschitz hypothesis at the basepoint `x`.
    calc
      |iteratedDerivWithin 2 g I t - H0|
          = ‖A ![d, d]‖ := by
              rw [hgSecond t ht]
              simp [A, H0, Real.norm_eq_abs]
      _ ≤ ‖A‖ * ‖d‖ ^ 2 := hEvalBound
      _ ≤ ((γ : ℝ) * ‖AffineMap.lineMap x (x + d) t - x‖) * ‖d‖ ^ 2 := by
              gcongr
              exact hHessianBasepointLipschitz _ hy
      _ = ((γ : ℝ) * ‖d‖ ^ 3) * t := by
              rw [hDist]
              ring
  have hIntegrandBound :
      ∀ t ∈ I,
        |(1 - t) * (iteratedDerivWithin 2 g I t - H0)| ≤
          (1 - t) * (((γ : ℝ) * ‖d‖ ^ 3) * t) := by
    intro t ht
    have hWeightNonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have := hPointwiseBound t ht
    rw [abs_mul, abs_of_nonneg hWeightNonneg]
    exact mul_le_mul_of_nonneg_left this hWeightNonneg
  have hBoundIntegral :
      |∫ t in 0..1, (1 - t) * (iteratedDerivWithin 2 g I t - H0)| ≤
        ∫ t in 0..1, (1 - t) * (((γ : ℝ) * ‖d‖ ^ 3) * t) := by
    have hAbsIntegrable :
        IntervalIntegrable (fun t : ℝ ↦ |(1 - t) * (iteratedDerivWithin 2 g I t - H0)|)
          MeasureTheory.volume 0 1 := by
      exact ((((continuousOn_const.sub continuousOn_id).mul
          (hSecondCont.sub continuousOn_const)).abs)).intervalIntegrable_of_Icc (by norm_num)
    have hUpperIntegrable :
        IntervalIntegrable (fun t : ℝ ↦ (1 - t) * (((γ : ℝ) * ‖d‖ ^ 3) * t))
          MeasureTheory.volume 0 1 := by
      exact ((continuousOn_const.sub continuousOn_id).mul
        ((continuousOn_const.mul continuousOn_id))).intervalIntegrable_of_Icc (by norm_num)
    calc
      |∫ t in 0..1, (1 - t) * (iteratedDerivWithin 2 g I t - H0)|
          ≤ ∫ t in 0..1, |(1 - t) * (iteratedDerivWithin 2 g I t - H0)| := by
              exact intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ t in 0..1, (1 - t) * (((γ : ℝ) * ‖d‖ ^ 3) * t) := by
              exact intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
                (f := fun t : ℝ ↦ |(1 - t) * (iteratedDerivWithin 2 g I t - H0)|)
                (g := fun t : ℝ ↦ (1 - t) * (((γ : ℝ) * ‖d‖ ^ 3) * t))
                (μ := MeasureTheory.volume)
                (by norm_num) hAbsIntegrable hUpperIntegrable hIntegrandBound
  -- Route correction: rather than building a separate residual function, rewrite the first-order
  -- integral remainder by subtracting the constant Hessian contribution inside the integral.
  calc
    |f (x + d) - (f x + fderiv ℝ f x d + (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![d, d])|
        = |∫ t in 0..1, (1 - t) * (iteratedDerivWithin 2 g I t - H0)| := by
            simpa [g, H0] using congrArg abs hRepresentation
    _ ≤ ∫ t in 0..1, (1 - t) * (((γ : ℝ) * ‖d‖ ^ 3) * t) := hBoundIntegral
    _ = ((γ : ℝ) / 6) * ‖d‖ ^ 3 := by
          rw [show (fun t : ℝ ↦ (1 - t) * (((γ : ℝ) * ‖d‖ ^ 3) * t)) =
              fun t : ℝ ↦ ((γ : ℝ) * ‖d‖ ^ 3) * ((1 - t) * t) by
                funext t
                ring]
          rw [intervalIntegral.integral_const_mul, hWeightedSquareIntegral]
          ring

/-- Chapter01 Theorem 1.2.23: if `f : E → ℝ` is `C²` on an open convex set `D` and its Hessian is
`γ`-Lipschitz on `D`, then the quadratic Taylor remainder at `x` is bounded by
`((γ : ℝ) / 6) * ‖d‖ ^ 3` for any `x + d ∈ D`. -/
theorem cubicRemainderBound_of_hessian_lipschitzOn
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hx : x ∈ D)
    (hf : ContDiffOn ℝ 2 f D)
    (hHessianLipschitz :
      LipschitzOnWith γ (fun y ↦ iteratedFDeriv ℝ 2 f y) D)
    (hxd : x + d ∈ D) :
    |f (x + d) - (f x + fderiv ℝ f x d + (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 f x) ![d, d])| ≤
      ((γ : ℝ) / 6) * ‖d‖ ^ 3 :=
  cubicRemainderBound_of_hessian_basepointLipschitzOn D f x d γ hD_open hD_convex hx hf
    (fun y hy ↦ by
      simpa [dist_eq_norm] using hHessianLipschitz.dist_le_mul y hy x hx)
    hxd

end Theorem123
