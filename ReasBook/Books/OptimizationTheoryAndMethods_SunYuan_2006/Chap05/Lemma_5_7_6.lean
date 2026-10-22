/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_13
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Theorem_2_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Lemma_5_7_5
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Strong
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

noncomputable section

open scoped Gradient
open InnerProductGeometry

section Chapter05Lemma576

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ) (m M : ℝ) (xk xkp1 dk : E) (αk ρ σ : ℝ)
variable (hC2 : ContDiff ℝ 2 f)
variable (hm : 0 < m)
variable (hM : 0 < M)
variable (hStrong : StrongConvexOn Set.univ m f)
variable
  (hUpperHessian :
    ∀ y u : E,
      (iteratedFDeriv ℝ 2 f y) ![u, u] ≤ M * ‖u‖ ^ (2 : ℕ))
variable (hStep : xkp1 = xk + αk • dk)
variable (hDescent : IsDescentDirectionAt f xk dk)

-- Domain sampling for this refine pass:
-- * primary domain: Wolfe-Powell line search on strongly convex objectives
-- * sampled canonical owners:
--   `lineSearchObjective`,
--   `HasGradientAt.deriv_lineSearchObjective_apply`,
--   `StrongConvexOn`,
--   `WolfePowellCondition`,
--   `InnerProductGeometry.angle`
-- * bridge/view reused from Chapter 2:
--   `deriv (lineSearchObjective f xk dk)`,
--   `cos_angle_searchDirection_negGradient`
-- * best owner abstraction: the intrinsic real inner-product-space layer, since no coordinate
--   data is used in the statements
-- Primitive data here is the strong-convexity owner, the global Hessian quadratic-form upper
-- bound, the accepted Wolfe-Powell step, and the descent-direction owner.
-- The cosine term is derived from the canonical angle owner rather than from a Euclidean
-- coordinate model.
-- The source-facing theorems should therefore use the Chapter 2 search-profile owner
-- `lineSearchObjective f xk dk`, its canonical derivative bridge
-- `deriv (lineSearchObjective f xk dk)`, the chapter owner `WolfePowellCondition` for the
-- accepted step, and the canonical cosine surface `Real.cos (angle dk
-- (-∇ f xk))`, rather than duplicating those one-dimensional surfaces as local raw lambdas.

local notation "φ" => lineSearchObjective f xk dk
local notation "cosθk" => Real.cos (angle dk (-∇ f xk))

/-- Helper for Chapter05 Lemma 5.7.6: the realized displacement equals the accepted step size
times the search direction. -/
lemma step_displacement_eq_smul_direction
    (hStep : xkp1 = xk + αk • dk) :
    xkp1 - xk = αk • dk := by
  -- Normalize the source step vector `s_k` to the actual displacement `xkp1 - xk`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    congrArg (fun z : E ↦ z - xk) hStep

/-- Helper for Chapter05 Lemma 5.7.6: once the Wolfe step size is known to be positive, the step
norm is `αk * ‖dk‖`. -/
lemma step_norm_eq_alpha_mul_direction_norm
    (hStep : xkp1 = xk + αk • dk)
    (hαk_nonneg : 0 ≤ αk) :
    ‖xkp1 - xk‖ = αk * ‖dk‖ := by
  -- Rewrite the displacement by `αk • dk` and then remove the absolute value on `αk`.
  simpa [step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk)
    (αk := αk) hStep, norm_smul, Real.norm_eq_abs, abs_of_nonneg hαk_nonneg]

/-- Helper for Chapter05 Lemma 5.7.6: the diagonal Hessian quadratic form written with
`fderiv ℝ (∇ f)` agrees with the diagonal value of `iteratedFDeriv ℝ 2 f`. -/
lemma inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt
    {y u v : E}
    (hC2y : ContDiffAt ℝ 2 f y) :
    inner ℝ v (hessianAt f y u) = (iteratedFDeriv ℝ 2 f y) ![u, v] := by
  -- Differentiate `fderiv ℝ f` once and transport through the Riesz isomorphism defining
  -- `gradient`.
  let e : StrongDual ℝ E ≃L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  have hfd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
    (hC2y.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hgrad := by
    simpa [gradient, Function.comp, e] using ((e.hasFDerivAt).comp y hfd)
  have hgrad' :
      fderiv ℝ (∇ f) y = e.toContinuousLinearMap ∘SL fderiv ℝ (fderiv ℝ f) y :=
    (show HasFDerivAt (∇ f) _ y from hgrad).fderiv
  have huEq :
      hessianAt f y u = e ((fderiv ℝ (fderiv ℝ f) y) u) := by
    simpa [hessianAt, e] using congrArg (fun T : E →L[ℝ] E ↦ T u) hgrad'
  calc
    inner ℝ v (hessianAt f y u) = inner ℝ v (e ((fderiv ℝ (fderiv ℝ f) y) u)) := by
      rw [huEq]
    _ = ((fderiv ℝ (fderiv ℝ f) y) u) v := by
      rw [real_inner_comm]
      change
        inner ℝ (((InnerProductSpace.toDual ℝ E).symm) ((fderiv ℝ (fderiv ℝ f) y) u)) v =
          ((fderiv ℝ (fderiv ℝ f) y) u) v
      simp
    _ = (iteratedFDeriv ℝ 2 f y) ![u, v] := by
      symm
      exact iteratedFDeriv_two_apply f y ![u, v]

/-- Helper for Chapter05 Lemma 5.7.6: the diagonal Hessian quadratic form written with
`fderiv ℝ (∇ f)` agrees with the diagonal value of `iteratedFDeriv ℝ 2 f`. -/
lemma iteratedFDeriv_diag_eq_inner_fderiv_gradient
    (hC2 : ContDiff ℝ 2 f)
    {y u : E} :
    (iteratedFDeriv ℝ 2 f y) ![u, u] = inner ℝ u ((fderiv ℝ (∇ f) y) u) := by
  -- Use the local Hessian bridge so the Chapter 2 trace theorem sees the current Hessian bound on
  -- the same `iteratedFDeriv` surface without importing later Chapter 3 infrastructure.
  have hC2y : ContDiffAt ℝ 2 f y := hC2.contDiffAt
  calc
    (iteratedFDeriv ℝ 2 f y) ![u, u] = inner ℝ u (hessianAt f y u) := by
      symm
      exact inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt (f := f) hC2y
    _ = inner ℝ u ((fderiv ℝ (∇ f) y) u) := by
      rfl

/-- Helper for Chapter05 Lemma 5.7.6: the secant pairing between the gradient difference and the
realized step is bounded above by `M * ‖xkp1 - xk‖²`. -/
lemma secant_inner_le_hessian_upper_mul_step_norm_sq
    (hC2 : ContDiff ℝ 2 f)
    (hUpperHessian :
      ∀ y u : E,
        (iteratedFDeriv ℝ 2 f y) ![u, u] ≤ M * ‖u‖ ^ (2 : ℕ)) :
    inner ℝ (∇ f xkp1 - ∇ f xk) (xkp1 - xk) ≤ M * ‖xkp1 - xk‖ ^ (2 : ℕ) := by
  -- Trace `f` along the realized step and apply the one-dimensional mean value theorem to the
  -- derivative profile on `[0, 1]`.
  let s : E := xkp1 - xk
  let ψ : ℝ → ℝ := lineSearchObjective f xk s
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let g : ℝ → ℝ := derivWithin ψ I
  have hs : UniqueDiffOn ℝ I := by
    simpa [I] using uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)
  have h_segment : segment ℝ xk (xk + (1 : ℝ) • s) ⊆ Set.univ := by
    intro y hy
    simp
  have hψC2 : ContDiffOn ℝ 2 ψ I := by
    -- The traced profile is `C²` because `f` is globally `C²`.
    simpa [ψ, I, Set.uIcc_of_le zero_le_one, one_smul] using
      unitIntervalTraceContDiffOn f xk s 1 h_segment hC2.contDiffOn
  have hDiff0_f : DifferentiableAt ℝ f xk :=
    ((hC2.of_le (by norm_num)).contDiffAt : ContDiffAt ℝ 1 f xk).differentiableAt (by norm_num)
  have hDiff1_f : DifferentiableAt ℝ f xkp1 :=
    ((hC2.of_le (by norm_num)).contDiffAt : ContDiffAt ℝ 1 f xkp1).differentiableAt (by norm_num)
  have hψDiff0 : DifferentiableAt ℝ ψ 0 := by
    -- The left endpoint of the trace is the base point `xk`.
    have hDiff0_trace : DifferentiableAt ℝ f (xk + (0 : ℝ) • ((1 : ℝ) • s)) := by
      simpa [zero_smul] using hDiff0_f
    change DifferentiableAt ℝ (f ∘ fun t : ℝ ↦ xk + t • s) 0
    simpa [ψ, s, zero_smul] using
      hDiff0_trace.comp 0 (unitIntervalTraceHasDerivAt xk s 1 0).differentiableAt
  have hψDiff1 : DifferentiableAt ℝ ψ 1 := by
    -- The right endpoint of the trace is the realized step point `xkp1`.
    have hDiff1_trace : DifferentiableAt ℝ f (xk + (1 : ℝ) • ((1 : ℝ) • s)) := by
      simpa [s, one_smul, add_sub_cancel] using hDiff1_f
    change DifferentiableAt ℝ (f ∘ fun t : ℝ ↦ xk + t • s) 1
    simpa [ψ, s, one_smul, add_sub_cancel] using
      hDiff1_trace.comp 1 (unitIntervalTraceHasDerivAt xk s 1 1).differentiableAt
  have hg_diff' : DifferentiableOn ℝ (iteratedDerivWithin 1 ψ I) I :=
    hψC2.differentiableOn_iteratedDerivWithin (by norm_num) hs
  have hg_diff : DifferentiableOn ℝ g I := by
    simpa [g, I, iteratedDerivWithin_one] using hg_diff'
  have hg_cont' : ContinuousOn (iteratedDerivWithin 1 ψ I) I :=
    hψC2.continuousOn_iteratedDerivWithin (by norm_num) hs
  have hg_cont : ContinuousOn g I := by
    simpa [g, I, iteratedDerivWithin_one] using hg_cont'
  have h0mem : (0 : ℝ) ∈ I := by simp [I]
  have h1mem : (1 : ℝ) ∈ I := by simp [I]
  have hDerivWithin0 : g 0 = deriv ψ 0 := by
    simpa [g] using hψDiff0.derivWithin (hs 0 h0mem)
  have hDerivWithin1 : g 1 = deriv ψ 1 := by
    simpa [g] using hψDiff1.derivWithin (hs 1 h1mem)
  obtain ⟨ξ, hξ, hMVT⟩ :=
    exists_deriv_eq_slope' g zero_lt_one hg_cont
      (hg_diff.mono (by
        intro t ht
        exact ⟨ht.1.le, ht.2.le⟩))
  have hξI : ξ ∈ I := by
    exact ⟨hξ.1.le, hξ.2.le⟩
  have hξu : ξ ∈ Set.uIcc (0 : ℝ) 1 := Set.mem_uIcc_of_le hξ.1.le hξ.2.le
  have hContDiffAtξ : ContDiffAt ℝ 2 ψ ξ :=
    hψC2.contDiffAt (Icc_mem_nhds hξ.1 hξ.2)
  have hDerivg : deriv g ξ = iteratedDeriv 2 ψ ξ := by
    calc
      deriv g ξ = derivWithin g I ξ := (derivWithin_of_mem_nhds (Icc_mem_nhds hξ.1 hξ.2)).symm
      _ = iteratedDerivWithin 2 ψ I ξ := by
        simp [g, I, iteratedDerivWithin_succ]
      _ = iteratedDeriv 2 ψ ξ := iteratedDerivWithin_eq_iteratedDeriv hs hContDiffAtξ hξI
  have hDeriv0 :
      deriv ψ 0 = inner ℝ (∇ f xk) s := by
    -- Differentiate the trace at the base point.
    have hDiff0_trace : DifferentiableAt ℝ f (xk + (0 : ℝ) • s) := by
      simpa [zero_smul] using hDiff0_f
    simpa [ψ, s, zero_smul, lineSearchObjective_apply] using
      deriv_lineSearchObjective_apply f xk s 0 hDiff0_trace
  have hDeriv1 :
      deriv ψ 1 = inner ℝ (∇ f xkp1) s := by
    -- Differentiate the trace at the realized endpoint.
    have hDiff1_trace : DifferentiableAt ℝ f (xk + (1 : ℝ) • s) := by
      simpa [s, one_smul, add_sub_cancel] using hDiff1_f
    simpa [ψ, s, one_smul, add_sub_cancel, lineSearchObjective_apply] using
      deriv_lineSearchObjective_apply f xk s 1 hDiff1_trace
  have hSecondWithin :
      iteratedDerivWithin 2 ψ (Set.uIcc (0 : ℝ) 1) ξ =
        inner ℝ s ((fderiv ℝ (∇ f) (xk + ξ • s)) s) := by
    have hTraceSecond :=
      unitIntervalTraceSecondIteratedDeriv f xk s 1 ξ isOpen_univ h_segment hC2.contDiffOn hξu
    calc
      iteratedDerivWithin 2 ψ (Set.uIcc (0 : ℝ) 1) ξ =
          iteratedDerivWithin 2 (lineSearchObjective f xk ((1 : ℝ) • s)) (Set.uIcc (0 : ℝ) 1) ξ := by
            simp [ψ]
      _ =
          1 ^ (2 : ℕ) *
            inner ℝ s
              ((fderiv ℝ
                  (fun z ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z))
                  (xk + ξ • ((1 : ℝ) • s))) s) := hTraceSecond
      _ =
          1 ^ (2 : ℕ) * inner ℝ s ((fderiv ℝ (∇ f) (xk + ξ • ((1 : ℝ) • s))) s) := by
            rw [show
              fderiv ℝ (fun z ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z))
                (xk + ξ • ((1 : ℝ) • s)) =
                fderiv ℝ (∇ f) (xk + ξ • ((1 : ℝ) • s)) by
                  rfl]
      _ = inner ℝ s ((fderiv ℝ (∇ f) (xk + ξ • s)) s) := by
        simp
  have hSecondEq :
      iteratedDeriv 2 ψ ξ = inner ℝ s ((fderiv ℝ (∇ f) (xk + ξ • s)) s) := by
    -- Identify the sampled second derivative with the Hessian quadratic form on the trace.
    calc
      iteratedDeriv 2 ψ ξ = iteratedDerivWithin 2 ψ (Set.uIcc (0 : ℝ) 1) ξ := by
        symm
        simpa [I, Set.uIcc_of_le zero_le_one] using
          (iteratedDerivWithin_eq_iteratedDeriv hs hContDiffAtξ hξI)
      _ = inner ℝ s ((fderiv ℝ (∇ f) (xk + ξ • s)) s) := hSecondWithin
  have hSecondBound : iteratedDeriv 2 ψ ξ ≤ M * ‖s‖ ^ (2 : ℕ) := by
    -- The global Hessian quadratic bound closes the mean-value remainder.
    rw [hSecondEq, ← iteratedFDeriv_diag_eq_inner_fderiv_gradient (f := f) (hC2 := hC2)]
    exact hUpperHessian (xk + ξ • s) s
  have hSecantEq :
      inner ℝ (∇ f xkp1 - ∇ f xk) s = deriv ψ 1 - deriv ψ 0 := by
    rw [hDeriv1, hDeriv0, inner_sub_left]
  calc
    inner ℝ (∇ f xkp1 - ∇ f xk) (xkp1 - xk)
        = deriv ψ 1 - deriv ψ 0 := by
          simpa [s] using hSecantEq
    _ = slope g 0 1 := by
          rw [← hDerivWithin1, ← hDerivWithin0]
          simp [g, slope_def_field]
    _ = deriv g ξ := hMVT.symm
    _ = iteratedDeriv 2 ψ ξ := hDerivg
    _ ≤ M * ‖s‖ ^ (2 : ℕ) := hSecondBound
    _ = M * ‖xkp1 - xk‖ ^ (2 : ℕ) := by
          simp [s]

/-- Helper for Chapter05 Lemma 5.7.6: strong convexity gives the tangent-plus-quadratic lower
support inequality at the accepted step. -/
lemma strongConvex_support_lower_at_step
    (hC2 : ContDiff ℝ 2 f)
    (hStrong : StrongConvexOn Set.univ m f) :
    f xkp1 ≥
      f xk + inner ℝ (∇ f xk) (xkp1 - xk) + (m / 2) * ‖xkp1 - xk‖ ^ (2 : ℕ) := by
  -- Repackage strong convexity as convexity of the shifted objective and apply the tangent bound.
  have hConvShift :
      ConvexOn ℝ Set.univ (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) := by
    simpa using (strongConvexOn_iff_convex (s := Set.univ) (m := m) (f := f)).1 hStrong
  have hxk_diff : DifferentiableAt ℝ f xk :=
    ((hC2.of_le (by norm_num)).contDiffAt : ContDiffAt ℝ 1 f xk).differentiableAt (by norm_num)
  have hNormSqDeriv :
      HasFDerivAt (fun z : E ↦ ‖z‖ ^ (2 : ℕ)) (2 • innerSL ℝ xk) xk := by
    simpa using (hasStrictFDerivAt_norm_sq xk).hasFDerivAt
  have hShiftDeriv :
      HasFDerivAt
        (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ))
        (fderiv ℝ f xk - (m / 2) • (2 • innerSL ℝ xk)) xk := by
    exact hxk_diff.hasFDerivAt.sub (hNormSqDeriv.const_mul (m / 2))
  have hShiftSupport :
      f xk - (m / 2) * ‖xk‖ ^ (2 : ℕ) +
          (fderiv ℝ f xk - (m / 2) • (2 • innerSL ℝ xk)) (xkp1 - xk) ≤
        f xkp1 - (m / 2) * ‖xkp1‖ ^ (2 : ℕ) :=
    convex_tangent_le_of_hasFDerivAt hConvShift (x := xk) (y := xkp1) hShiftDeriv
  have hDerivEval :
      (fderiv ℝ f xk - (m / 2) • (2 • innerSL ℝ xk)) (xkp1 - xk) =
        inner ℝ (∇ f xk) (xkp1 - xk) - m * inner ℝ xk (xkp1 - xk) := by
    rw [sub_apply, smul_apply, inner_gradient_left]
    simp [innerSL_apply_apply]
    ring
  have hQuadratic :
      -(m / 2) * ‖xk‖ ^ (2 : ℕ) - m * inner ℝ xk (xkp1 - xk) +
          (m / 2) * ‖xkp1‖ ^ (2 : ℕ) =
        (m / 2) * ‖xk - xkp1‖ ^ (2 : ℕ) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real]
    ring
  have hCore :
      f xk + inner ℝ (∇ f xk) (xkp1 - xk) + (m / 2) * ‖xk - xkp1‖ ^ (2 : ℕ) ≤ f xkp1 := by
    have hShiftSupport' :
        f xk - (m / 2) * ‖xk‖ ^ (2 : ℕ) +
            (inner ℝ (∇ f xk) (xkp1 - xk) - m * inner ℝ xk (xkp1 - xk)) ≤
          f xkp1 - (m / 2) * ‖xkp1‖ ^ (2 : ℕ) := by
      simpa [hDerivEval] using hShiftSupport
    linarith [hShiftSupport', hQuadratic]
  simpa [norm_sub_rev] using hCore

/-- Helper for Chapter05 Lemma 5.7.6: the normalized negative directional derivative along the
accepted displacement is exactly `‖∇ f xk‖ * cos θk`. -/
lemma neg_gradientInner_div_stepNorm_eq_gradientNorm_mul_cos
    (hStep : xkp1 = xk + αk • dk)
    (hDescent : IsDescentDirectionAt f xk dk)
    (hWolfe : WolfePowellCondition φ (deriv φ) ρ σ αk) :
    -(inner ℝ (∇ f xk) (xkp1 - xk)) / ‖xkp1 - xk‖ = ‖∇ f xk‖ * cosθk := by
  -- Transport the Chapter 2 cosine identity across the positive Wolfe step `xkp1 - xk = αk • dk`.
  rcases wolfePowellCondition_iff.mp hWolfe with ⟨_, hαk_pos, _, _⟩
  calc
    -(inner ℝ (∇ f xk) (xkp1 - xk)) / ‖xkp1 - xk‖
        = -(inner ℝ (∇ f xk) (αk • dk)) / ‖αk • dk‖ := by
            rw [step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk)
              (αk := αk) hStep]
    _ = -(inner ℝ (∇ f xk) (αk • dk)) / (αk * ‖dk‖) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hαk_pos.le]
    _ = -(αk * inner ℝ (∇ f xk) dk) / (αk * ‖dk‖) := by
          rw [inner_smul_right]
    _ = -(inner ℝ (∇ f xk) dk) / ‖dk‖ := by
          field_simp [hαk_pos.ne']
    _ = -(inner ℝ (∇ f xk) dk / ‖dk‖) := by
          ring
    _ = ‖∇ f xk‖ * cosθk := by
          simpa using
            (gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm
              f xk dk).symm

/-- Helper for Chapter05 Lemma 5.7.6: the negative gradient pairing with the realized step is
`‖∇ f xk‖ * ‖xkp1 - xk‖ * cos θk`. -/
lemma neg_gradientInner_step_eq_gradientNorm_mul_stepNorm_mul_cos
    (hStep : xkp1 = xk + αk • dk)
    (hDescent : IsDescentDirectionAt f xk dk)
    (hWolfe : WolfePowellCondition φ (deriv φ) ρ σ αk) :
    -(inner ℝ (∇ f xk) (xkp1 - xk)) =
      ‖∇ f xk‖ * ‖xkp1 - xk‖ * cosθk := by
  -- Clear the positive step norm denominator from the normalized cosine identity.
  rcases wolfePowellCondition_iff.mp hWolfe with ⟨_, hαk_pos, _, _⟩
  have hstep_ne : xkp1 - xk ≠ 0 := by
    rw [step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) hStep]
    exact smul_ne_zero hαk_pos.ne' hDescent.direction_ne
  have hratio :=
    neg_gradientInner_div_stepNorm_eq_gradientNorm_mul_cos
      (f := f) (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) (ρ := ρ) (σ := σ)
      hStep hDescent hWolfe
  have hclear :
      -(inner ℝ (∇ f xk) (xkp1 - xk)) =
        (‖∇ f xk‖ * cosθk) * ‖xkp1 - xk‖ := by
    exact (div_eq_iff (norm_ne_zero_iff.mpr hstep_ne)).mp hratio
  simpa [mul_assoc, mul_left_comm, mul_comm] using hclear

/-- Chapter05 Lemma 5.7.6 (1), stated on a real inner product space: let `f : E → ℝ` be twice
continuously differentiable and uniformly, equivalently strongly, convex with modulus `m > 0`,
assume the global upper Hessian bound `(iteratedFDeriv ℝ 2 f y) ![u, u] ≤ M * ‖u‖ ^ (2 : ℕ)`
for every `y` and `u`, and let `xkp1 = xk + αk • dk` be a Wolfe-Powell step for the ray profile
`lineSearchObjective f xk dk` with parameters `ρ, σ`. Writing
`cos θk = Real.cos (angle dk (-∇ f xk))`, the step displacement
`xkp1 - xk` satisfies
`((1 - σ) / M) * ‖∇ f xk‖ * cos θk ≤ ‖xkp1 - xk‖ ≤
  (2 * (1 - ρ) / m) * ‖∇ f xk‖ * cos θk`. -/
theorem stepNormBounds_of_wolfePowell_of_strongConvex
    (hC2 : ContDiff ℝ 2 f)
    (hm : 0 < m)
    (hM : 0 < M)
    (hStrong : StrongConvexOn Set.univ m f)
    (hUpperHessian :
      ∀ y u : E,
        (iteratedFDeriv ℝ 2 f y) ![u, u] ≤ M * ‖u‖ ^ (2 : ℕ))
    (hStep : xkp1 = xk + αk • dk)
    (hDescent : IsDescentDirectionAt f xk dk)
    (hWolfe : WolfePowellCondition φ (deriv φ) ρ σ αk) :
    ((1 - σ) / M) * ‖∇ f xk‖ * cosθk ≤
        ‖xkp1 - xk‖ ∧
      ‖xkp1 - xk‖ ≤
        (2 * (1 - ρ) / m) * ‖∇ f xk‖ * cosθk := by
  -- Follow the source proof: curvature plus the secant/Hessian trace bound gives the lower step
  -- estimate, and strong convex support plus sufficient decrease gives the upper estimate.
  rcases wolfePowellCondition_iff.mp hWolfe with ⟨hParams, hαk_pos, hDec, hCurv⟩
  rcases wolfePowellParameters_iff.mp hParams with ⟨hρ_pos, hρ_lt_sigma, hσ_lt_one⟩
  let s : E := xkp1 - xk
  have hDiff0_f : DifferentiableAt ℝ f xk := hDescent.differentiableAt
  have hDiffStep_f : DifferentiableAt ℝ f xkp1 :=
    ((hC2.of_le (by norm_num)).contDiffAt : ContDiffAt ℝ 1 f xkp1).differentiableAt (by norm_num)
  have hstep_ne : s ≠ 0 := by
    rw [show s = xkp1 - xk by rfl,
      step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) hStep]
    exact smul_ne_zero hαk_pos.ne' hDescent.direction_ne
  have hstep_norm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hstep_ne
  have hDeriv0 :
      deriv φ 0 = inner ℝ (∇ f xk) dk := by
    have hDiff0_line : DifferentiableAt ℝ f (xk + (0 : ℝ) • dk) := by
      simpa [zero_smul] using hDiff0_f
    simpa [lineSearchObjective_zero] using
      deriv_lineSearchObjective_apply f xk dk 0 hDiff0_line
  have hDerivα :
      deriv φ αk = inner ℝ (∇ f xkp1) dk := by
    have hDiffα_line : DifferentiableAt ℝ f (xk + αk • dk) := by
      simpa [hStep] using hDiffStep_f
    simpa [hStep] using
      deriv_lineSearchObjective_apply f xk dk αk hDiffα_line
  have hCurvScaled :
      σ * inner ℝ (∇ f xk) s ≤ inner ℝ (∇ f xkp1) s := by
    have hCurv' : σ * inner ℝ (∇ f xk) dk ≤ inner ℝ (∇ f xkp1) dk := by
      simpa [hDeriv0, hDerivα] using hCurv
    have hMul := mul_le_mul_of_nonneg_left hCurv' hαk_pos.le
    simpa [s,
      step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) hStep,
      inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using hMul
  have hCurvatureDiff :
      (1 - σ) * (-(inner ℝ (∇ f xk) s)) ≤ inner ℝ (∇ f xkp1 - ∇ f xk) s := by
    calc
      (1 - σ) * (-(inner ℝ (∇ f xk) s)) = (σ - 1) * inner ℝ (∇ f xk) s := by
        ring
      _ ≤ inner ℝ (∇ f xkp1) s - inner ℝ (∇ f xk) s := by
        linarith
      _ = inner ℝ (∇ f xkp1 - ∇ f xk) s := by
        rw [inner_sub_left]
  have hSecant :
      inner ℝ (∇ f xkp1 - ∇ f xk) s ≤ M * ‖s‖ ^ (2 : ℕ) :=
    secant_inner_le_hessian_upper_mul_step_norm_sq
      (f := f) (M := M) (xk := xk) (xkp1 := xkp1) hC2 hUpperHessian
  have hLowerCore :
      (1 - σ) * (-(inner ℝ (∇ f xk) s)) ≤ M * ‖s‖ ^ (2 : ℕ) := by
    exact le_trans hCurvatureDiff hSecant
  have hLowerDiv :
      ((1 - σ) * (-(inner ℝ (∇ f xk) s))) / (M * ‖s‖) ≤ ‖s‖ := by
    refine (div_le_iff₀ (mul_pos hM hstep_norm_pos)).2 ?_
    nlinarith [hLowerCore]
  have hLowerRatio :
      ((1 - σ) / M) * (-(inner ℝ (∇ f xk) s) / ‖s‖) ≤ ‖s‖ := by
    calc
      ((1 - σ) / M) * (-(inner ℝ (∇ f xk) s) / ‖s‖) =
          ((1 - σ) * (-(inner ℝ (∇ f xk) s))) / (M * ‖s‖) := by
            field_simp [hM.ne', hstep_norm_pos.ne']
      _ ≤ ‖s‖ := hLowerDiv
  have hLower :
      ((1 - σ) / M) * ‖∇ f xk‖ * cosθk ≤ ‖s‖ := by
    calc
      ((1 - σ) / M) * ‖∇ f xk‖ * cosθk =
          ((1 - σ) / M) * (-(inner ℝ (∇ f xk) s) / ‖s‖) := by
            simpa [s, mul_assoc, mul_left_comm, mul_comm] using
              congrArg (fun t : ℝ ↦ ((1 - σ) / M) * t)
                (neg_gradientInner_div_stepNorm_eq_gradientNorm_mul_cos
                  (f := f) (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) (ρ := ρ)
                  (σ := σ) hStep hDescent hWolfe).symm
      _ ≤ ‖s‖ := hLowerRatio
  have hDecStep :
      f xkp1 ≤ f xk + ρ * inner ℝ (∇ f xk) s := by
    have hDec' :
        f xkp1 ≤ f xk + ρ * αk * inner ℝ (∇ f xk) dk := by
      simpa [lineSearchObjective_apply, lineSearchObjective_zero, hStep, hDeriv0] using hDec
    simpa [s,
      step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) hStep,
      inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using hDec'
  have hSupport :
      f xkp1 ≥ f xk + inner ℝ (∇ f xk) s + (m / 2) * ‖s‖ ^ (2 : ℕ) := by
    simpa [s] using strongConvex_support_lower_at_step
      (f := f) (m := m) (xk := xk) (xkp1 := xkp1) hC2 hStrong
  have hUpperCore :
      (m / 2) * ‖s‖ ^ (2 : ℕ) ≤ (1 - ρ) * (-(inner ℝ (∇ f xk) s)) := by
    linarith
  have hUpperCos :
      (m / 2) * ‖s‖ ^ (2 : ℕ) ≤
        (1 - ρ) * (‖∇ f xk‖ * ‖s‖ * cosθk) := by
    have hUpperCore' :
        (m / 2) * ‖xkp1 - xk‖ ^ (2 : ℕ) ≤
          (1 - ρ) * (-(inner ℝ (∇ f xk) (xkp1 - xk))) := by
      simpa [s] using hUpperCore
    have hUpperCos' :
        (m / 2) * ‖xkp1 - xk‖ ^ (2 : ℕ) ≤
          (1 - ρ) * (‖∇ f xk‖ * ‖xkp1 - xk‖ * cosθk) := by
      rwa [neg_gradientInner_step_eq_gradientNorm_mul_stepNorm_mul_cos
        (f := f) (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) (ρ := ρ) (σ := σ)
        hStep hDescent hWolfe] at hUpperCore'
    simpa [s] using hUpperCos'
  have hUpper :
      ‖s‖ ≤ (2 * (1 - ρ) / m) * ‖∇ f xk‖ * cosθk := by
    have hUpperDiv :
        ‖s‖ ≤
          ((1 - ρ) * (‖∇ f xk‖ * ‖s‖ * cosθk)) / ((m / 2) * ‖s‖) := by
      refine (le_div_iff₀ ?_).2 ?_
      · positivity
      · simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hUpperCos
    calc
      ‖s‖ ≤ ((1 - ρ) * (‖∇ f xk‖ * ‖s‖ * cosθk)) / ((m / 2) * ‖s‖) := hUpperDiv
      _ = (2 * (1 - ρ) / m) * ‖∇ f xk‖ * cosθk := by
            field_simp [hm.ne', hstep_norm_pos.ne']
  exact ⟨by simpa [s] using hLower, by simpa [s, mul_assoc, mul_left_comm, mul_comm] using hUpper⟩

/-- Helper for Chapter05 Lemma 5.7.6: Wolfe sufficient decrease together with the lower step
bound produces the precise `-ρ * c₁ * ‖∇ f xk‖² * cos² θk` estimate used in the contraction
argument. -/
lemma wolfe_decrease_le_neg_rho_mul_c1_mul_gradient_norm_sq_mul_cos_sq
    (hC2 : ContDiff ℝ 2 f)
    (hm : 0 < m)
    (hM : 0 < M)
    (hStrong : StrongConvexOn Set.univ m f)
    (hUpperHessian :
      ∀ y u : E,
        (iteratedFDeriv ℝ 2 f y) ![u, u] ≤ M * ‖u‖ ^ (2 : ℕ))
    (hStep : xkp1 = xk + αk • dk)
    (hDescent : IsDescentDirectionAt f xk dk)
    (hWolfe : WolfePowellCondition φ (deriv φ) ρ σ αk) :
    f xkp1 - f xk ≤
      -ρ * ((1 - σ) / M) * ‖∇ f xk‖ ^ (2 : ℕ) * cosθk ^ (2 : ℕ) := by
  -- Combine sufficient decrease with the lower step bound from `(5.7.28)`.
  rcases wolfePowellCondition_iff.mp hWolfe with ⟨hParams, _, hDec, _⟩
  rcases wolfePowellParameters_iff.mp hParams with ⟨hρ_pos, _, hσ_lt_one⟩
  let s : E := xkp1 - xk
  have hBounds :=
    stepNormBounds_of_wolfePowell_of_strongConvex
      (f := f) (m := m) (M := M) (xk := xk) (xkp1 := xkp1) (dk := dk)
      (αk := αk) (ρ := ρ) (σ := σ) hC2 hm hM hStrong hUpperHessian hStep hDescent hWolfe
  have hLower :
      ((1 - σ) / M) * ‖∇ f xk‖ * cosθk ≤ ‖s‖ := by
    simpa [s] using hBounds.1
  have hDiff0_f : DifferentiableAt ℝ f xk := hDescent.differentiableAt
  have hDeriv0 :
      deriv φ 0 = inner ℝ (∇ f xk) dk := by
    have hDiff0_line : DifferentiableAt ℝ f (xk + (0 : ℝ) • dk) := by
      simpa [zero_smul] using hDiff0_f
    simpa [lineSearchObjective_zero] using
      deriv_lineSearchObjective_apply f xk dk 0 hDiff0_line
  have hDecStep :
      f xkp1 - f xk ≤ ρ * inner ℝ (∇ f xk) s := by
    have hDec' :
        f xkp1 ≤ f xk + ρ * αk * inner ℝ (∇ f xk) dk := by
      simpa [lineSearchObjective_apply, lineSearchObjective_zero, hStep, hDeriv0] using hDec
    have hStepInner :
        ρ * αk * inner ℝ (∇ f xk) dk = ρ * inner ℝ (∇ f xk) s := by
      rw [show s = xkp1 - xk by rfl,
        step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) hStep,
        inner_smul_right]
      ring
    linarith
  have hDecCos :
      f xkp1 - f xk ≤ -ρ * (‖∇ f xk‖ * ‖s‖ * cosθk) := by
    have hPair :
        inner ℝ (∇ f xk) (xkp1 - xk) =
          -(‖∇ f xk‖ * ‖xkp1 - xk‖ * cosθk) := by
      linarith
        [neg_gradientInner_step_eq_gradientNorm_mul_stepNorm_mul_cos
          (f := f) (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) (ρ := ρ) (σ := σ)
          hStep hDescent hWolfe]
    have hDecStep' :
        f xkp1 - f xk ≤ ρ * inner ℝ (∇ f xk) (xkp1 - xk) := by
      simpa [s] using hDecStep
    have hDecStep'' :
        f xkp1 - f xk ≤ -(ρ * (‖∇ f xk‖ * ‖xkp1 - xk‖ * cosθk)) := by
      rwa [hPair, mul_neg] at hDecStep'
    simpa [s, mul_assoc, mul_left_comm, mul_comm] using hDecStep''
  have hCosNonneg : 0 ≤ ‖∇ f xk‖ * cosθk := by
    have hRatio :=
      neg_gradientInner_div_stepNorm_eq_gradientNorm_mul_cos
        (f := f) (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) (ρ := ρ) (σ := σ)
        hStep hDescent hWolfe
    have hstep_ne : s ≠ 0 := by
      rw [show s = xkp1 - xk by rfl,
        step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) hStep]
      rcases wolfePowellCondition_iff.mp hWolfe with ⟨_, hαk_pos, _, _⟩
      exact smul_ne_zero hαk_pos.ne' hDescent.direction_ne
    have hInnerNeg :
        inner ℝ (∇ f xk) s < 0 := by
      rw [show s = xkp1 - xk by rfl,
        step_displacement_eq_smul_direction (xk := xk) (xkp1 := xkp1) (dk := dk) (αk := αk) hStep,
        inner_smul_right]
      rcases wolfePowellCondition_iff.mp hWolfe with ⟨_, hαk_pos, _, _⟩
      nlinarith [hDescent.inner_gradient_neg, hαk_pos]
    have hPos :
        0 < -(inner ℝ (∇ f xk) s) / ‖s‖ := by
      exact div_pos (by linarith) (norm_pos_iff.mpr hstep_ne)
    rw [← hRatio]
    linarith
  have hProduct :
      -ρ * (‖∇ f xk‖ * ‖s‖ * cosθk) ≤
        -ρ * (((1 - σ) / M) * ‖∇ f xk‖ ^ (2 : ℕ) * cosθk ^ (2 : ℕ)) := by
    have hCoeff_nonpos : -ρ * (‖∇ f xk‖ * cosθk) ≤ 0 := by
      nlinarith [hCosNonneg, hρ_pos]
    have hMul :
        (-ρ * (‖∇ f xk‖ * cosθk)) * ‖s‖ ≤
          (-ρ * (‖∇ f xk‖ * cosθk)) *
            (((1 - σ) / M) * ‖∇ f xk‖ * cosθk) := by
      exact mul_le_mul_of_nonpos_left hLower hCoeff_nonpos
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hMul
  calc
    f xkp1 - f xk ≤ -ρ * (‖∇ f xk‖ * ‖s‖ * cosθk) := hDecCos
    _ ≤ -ρ * (((1 - σ) / M) * ‖∇ f xk‖ ^ (2 : ℕ) * cosθk ^ (2 : ℕ)) := hProduct
    _ = -ρ * ((1 - σ) / M) * ‖∇ f xk‖ ^ (2 : ℕ) * cosθk ^ (2 : ℕ) := by
          ring

/-- Chapter05 Lemma 5.7.6 (2), stated on a real inner product space: under the same twice
continuously differentiable global strong-convexity and global Hessian upper-bound hypotheses,
if `xStar` is a global minimizer of `f`, then the Wolfe-Powell step suboptimality contracts
according to
`f xkp1 - f xStar ≤
  (1 - ρ * m * ((1 - σ) / M) * cos θk ^ 2) * (f xk - f xStar)`,
where `cos θk = Real.cos (angle dk (-∇ f xk))`. -/
theorem suboptimalityContraction_of_wolfePowell_of_strongConvex
    (xStar : E)
    (hC2 : ContDiff ℝ 2 f)
    (hm : 0 < m)
    (hM : 0 < M)
    (hStrong : StrongConvexOn Set.univ m f)
    (hUpperHessian :
      ∀ y u : E,
        (iteratedFDeriv ℝ 2 f y) ![u, u] ≤ M * ‖u‖ ^ (2 : ℕ))
    (hStep : xkp1 = xk + αk • dk)
    (hDescent : IsDescentDirectionAt f xk dk)
    (hWolfe : WolfePowellCondition φ (deriv φ) ρ σ αk)
    (hMin : IsMinOn f Set.univ xStar) :
    f xkp1 - f xStar ≤
      (1 - ρ * m * ((1 - σ) / M) * cosθk ^ (2 : ℕ)) *
        (f xk - f xStar) := by
  -- Combine the previous Wolfe decrease estimate with Lemma 5.7.5.
  rcases wolfePowellCondition_iff.mp hWolfe with ⟨hParams, _, _, _⟩
  rcases wolfePowellParameters_iff.mp hParams with ⟨hρ_pos, _, hσ_lt_one⟩
  have hDiffk : DifferentiableAt ℝ f xk :=
    ((hC2.of_le (by norm_num)).contDiffAt : ContDiffAt ℝ 1 f xk).differentiableAt (by norm_num)
  have hDecrease :=
    wolfe_decrease_le_neg_rho_mul_c1_mul_gradient_norm_sq_mul_cos_sq
      (f := f) (m := m) (M := M) (xk := xk) (xkp1 := xkp1) (dk := dk)
      (αk := αk) (ρ := ρ) (σ := σ) hC2 hm hM hStrong hUpperHessian hStep hDescent hWolfe
  have hGap :=
    sub_globalMin_le_inv_mul_norm_gradient_sq_of_strongConvex
      f m xk xStar hm hStrong hDiffk hMin
  have hGapMul :
      m * (f xk - f xStar) ≤ ‖∇ f xk‖ ^ (2 : ℕ) := by
    have hMul := mul_le_mul_of_nonneg_left hGap hm.le
    simpa [div_eq_mul_inv, hm.ne', mul_assoc, mul_left_comm, mul_comm] using hMul
  have hDecreaseGap :
      f xkp1 - f xk ≤
        -ρ * ((1 - σ) / M) * (m * (f xk - f xStar)) * cosθk ^ (2 : ℕ) := by
    have hCoeff_nonpos :
        -ρ * ((1 - σ) / M) * cosθk ^ (2 : ℕ) ≤ 0 := by
      have hσ_pos : 0 < 1 - σ := by linarith
      have hCoeff_nonneg : 0 ≤ ρ * ((1 - σ) / M) * cosθk ^ (2 : ℕ) := by
        positivity
      nlinarith
    have hScaled :
        (-ρ * ((1 - σ) / M) * cosθk ^ (2 : ℕ)) * ‖∇ f xk‖ ^ (2 : ℕ) ≤
          (-ρ * ((1 - σ) / M) * cosθk ^ (2 : ℕ)) * (m * (f xk - f xStar)) := by
      exact mul_le_mul_of_nonpos_left hGapMul hCoeff_nonpos
    have hScaled' :
        -ρ * ((1 - σ) / M) * ‖∇ f xk‖ ^ (2 : ℕ) * cosθk ^ (2 : ℕ) ≤
          -ρ * ((1 - σ) / M) * (m * (f xk - f xStar)) * cosθk ^ (2 : ℕ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hScaled
    exact le_trans hDecrease hScaled'
  have hFinal :
      f xkp1 - f xk ≤
        -(ρ * m * ((1 - σ) / M) * cosθk ^ (2 : ℕ)) * (f xk - f xStar) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hDecreaseGap
  linarith

end Chapter05Lemma576
