/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable {U : Set H} {β : NNReal} {f : H → ℝ}
private lemma norm_sub_gradientWithin_le
    (hgrad : LipschitzOnWith β (gradientWithin f U) U) {x y : H}
    (hx : x ∈ U) (hy : y ∈ U) :
    ‖gradientWithin f U x - gradientWithin f U y‖ ≤ (β : ℝ) * ‖x - y‖ := by
  have h' := hgrad hx hy
  have h'' := (ENNReal.toReal_le_toReal (edist_ne_top _ _) (by finiteness)).2 h'
  simpa [edist_dist, dist_eq_norm] using h''

section

variable (hU_open : IsOpen U) (hU_convex : Convex ℝ U)
variable (hf : DifferentiableOn ℝ f U)
variable (hgrad : LipschitzOnWith β (gradientWithin f U) U)

omit [CompleteSpace H] in
private lemma lineMap_mem (hU_convex : Convex ℝ U) {x y : H} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap x y t ∈ U :=
  hU_convex.lineMap_mem hx hy ht

private lemma hasDerivAt_comp_lineMap_gradientWithin
    (hU_open : IsOpen U) (hf : DifferentiableOn ℝ f U) {x y : H} {t : ℝ}
    (hz : AffineMap.lineMap x y t ∈ U) :
    HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s))
      (⟪gradientWithin f U (AffineMap.lineMap x y t), y - x⟫_ℝ) t := by
  let z := AffineMap.lineMap x y t
  have hfd : HasFDerivAt f (fderiv ℝ f z) z := by
    exact (hf.differentiableAt (hU_open.mem_nhds hz)).hasFDerivAt
  have hcomp :
      HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s)) ((fderiv ℝ f z) (y - x)) t := by
    simpa [z] using hfd.comp_hasDerivAt t (AffineMap.hasDerivAt (AffineMap.lineMap x y))
  have hinner : (fderiv ℝ f z) (y - x) = ⟪gradientWithin f U z, y - x⟫_ℝ := by
    rw [← fderivWithin_of_isOpen hU_open hz]
    exact (hf z hz).hasGradientWithinAt.fderivWithin_apply (hU_open.uniqueDiffWithinAt hz)
  simpa [z, hinner] using hcomp

private lemma gradientWithin_lineMap_continuousOn
    (hU_convex : Convex ℝ U) (hgrad : LipschitzOnWith β (gradientWithin f U) U)
    {x y : H} (hx : x ∈ U) (hy : y ∈ U) :
    ContinuousOn (fun t : ℝ ↦ gradientWithin f U (AffineMap.lineMap x y t))
      (Set.Icc (0 : ℝ) 1) := by
  have hcont : ContinuousOn (gradientWithin f U) U := hgrad.continuousOn
  refine hcont.comp AffineMap.lineMap_continuous.continuousOn ?_
  intro t ht
  exact lineMap_mem hU_convex hx hy ht

private lemma remainder_integrand_norm_bound
    (hU_convex : Convex ℝ U) (hgrad : LipschitzOnWith β (gradientWithin f U) U)
    {x y : H} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |⟪gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x, y - x⟫_ℝ|
      ≤ (β : ℝ) * ‖y - x‖ ^ 2 * t := by
  have hz : AffineMap.lineMap x y t ∈ U := lineMap_mem hU_convex hx hy ht
  have hgrad_norm :
      ‖gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x‖
        ≤ (β : ℝ) * ‖AffineMap.lineMap x y t - x‖ :=
    norm_sub_gradientWithin_le hgrad hz hx
  have hline : ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
    have hdist : dist x (AffineMap.lineMap x y t) = ‖t‖ * dist x y := dist_left_lineMap x y t
    have htnorm : ‖t‖ = t := abs_of_nonneg ht.1
    simpa [dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
  calc
    |⟪gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x, y - x⟫_ℝ|
        ≤ ‖gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x‖ * ‖y - x‖ := by
          exact abs_real_inner_le_norm _ _
    _ ≤ ((β : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ := by
      gcongr
    _ = ((β : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
      rw [hline]
    _ = (β : ℝ) * ‖y - x‖ ^ 2 * t := by
      ring

include hU_open hU_convex hf hgrad

/-- Lemma 2.64 (1): on an open convex set, a Fréchet differentiable function whose gradient
is `β`-Lipschitz has first-order Taylor remainder at most `(β / 2) * ‖y - x‖^2`. -/
theorem abs_sub_sub_inner_gradientWithin_le_half_mul
    {x y : H} (hx : x ∈ U) (hy : y ∈ U) :
    |f y - f x - ⟪y - x, gradientWithin f U x⟫_ℝ| ≤
      ((β : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  let φ : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  let ψ : ℝ → ℝ := fun t ↦ ⟪gradientWithin f U (AffineMap.lineMap x y t), y - x⟫_ℝ
  let ρ : ℝ → ℝ := fun t ↦
    ⟪gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x, y - x⟫_ℝ
  -- Differentiate `f` along the segment on the whole interval `[0,1]`.
  have hψ_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t ht
    have hz : AffineMap.lineMap x y t ∈ U := by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le zero_le_one] using ht
      exact lineMap_mem hU_convex hx hy ht'
    simpa [φ, ψ] using hasDerivAt_comp_lineMap_gradientWithin hU_open hf hz
  -- Continuity of the gradient along the segment gives interval integrability.
  have hgradCont :
      ContinuousOn (fun t : ℝ ↦ gradientWithin f U (AffineMap.lineMap x y t)) (Set.Icc (0 : ℝ) 1) :=
    gradientWithin_lineMap_continuousOn hU_convex hgrad hx hy
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    simpa [ψ] using hgradCont.inner continuousOn_const
  have hψ_int : IntervalIntegrable ψ MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one hψ_cont
  -- The fundamental theorem of calculus identifies the segment integral with `f y - f x`.
  have hFTC : ∫ t in 0..1, ψ t = f y - f x := by
    simpa [φ, ψ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hψ_deriv hψ_int
  have hρ_eq : (fun t : ℝ ↦ ψ t - ψ 0) = ρ := by
    funext t
    simp [ψ, ρ, AffineMap.lineMap_apply_zero, inner_sub_left]
  have hconst_int : IntervalIntegrable (fun _ : ℝ ↦ ψ 0) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one continuousOn_const
  have hρ_int : IntervalIntegrable ρ MeasureTheory.volume 0 1 := by
    have hρ_cont : ContinuousOn ρ (Set.Icc (0 : ℝ) 1) := by
      simpa [ρ] using (hgradCont.sub continuousOn_const).inner continuousOn_const
    exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one hρ_cont
  have hrem : f y - f x - ⟪gradientWithin f U x, y - x⟫_ℝ = ∫ t in 0..1, ρ t := by
    calc
      f y - f x - ⟪gradientWithin f U x, y - x⟫_ℝ = (∫ t in 0..1, ψ t) - ψ 0 := by
        rw [← hFTC]
        simp [ψ, AffineMap.lineMap_apply_zero]
      _ = (∫ t in 0..1, ψ t) - ∫ t in 0..1, ψ 0 := by
        simp [intervalIntegral.integral_const]
      _ = ∫ t in 0..1, (ψ t - ψ 0) := by
        rw [intervalIntegral.integral_sub hψ_int hconst_int]
      _ = ∫ t in 0..1, ρ t := by
        rw [hρ_eq]
  have hρ_abs_int : IntervalIntegrable (fun t : ℝ ↦ |ρ t|) MeasureTheory.volume 0 1 := hρ_int.abs
  have hbound_int :
      IntervalIntegrable (fun t : ℝ ↦ (β : ℝ) * ‖y - x‖ ^ 2 * t) MeasureTheory.volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    continuity
  have hbound_mono :
      (∫ t in 0..1, |ρ t|) ≤ ∫ t in 0..1, (β : ℝ) * ‖y - x‖ ^ 2 * t := by
    refine intervalIntegral.integral_mono_on zero_le_one hρ_abs_int hbound_int ?_
    intro t ht
    simpa [ρ] using remainder_integrand_norm_bound hU_convex hgrad hx hy ht
  calc
    |f y - f x - ⟪y - x, gradientWithin f U x⟫_ℝ|
        = |f y - f x - ⟪gradientWithin f U x, y - x⟫_ℝ| := by
          rw [real_inner_comm]
    _ = |∫ t in 0..1, ρ t| := by
      rw [hrem]
    _ ≤ ∫ t in 0..1, |ρ t| := by
      exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in 0..1, (β : ℝ) * ‖y - x‖ ^ 2 * t := hbound_mono
    _ = ((β : ℝ) / 2) * ‖y - x‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

end

section

variable (hgrad : LipschitzOnWith β (gradientWithin f U) U)

include hgrad

/-- Lemma 2.64 (2): for points of `U`, the gradient increment paired with `x - y` is bounded in
absolute value by `β * ‖y - x‖^2`. -/
theorem abs_inner_sub_gradientWithin_sub_le_mul
    {x y : H} (hx : x ∈ U) (hy : y ∈ U) :
    |⟪x - y, gradientWithin f U x - gradientWithin f U y⟫_ℝ| ≤
      (β : ℝ) * ‖y - x‖ ^ 2 := by
  have hgrad_norm : ‖gradientWithin f U x - gradientWithin f U y‖ ≤ (β : ℝ) * ‖x - y‖ :=
    norm_sub_gradientWithin_le hgrad hx hy
  calc
    |⟪x - y, gradientWithin f U x - gradientWithin f U y⟫_ℝ|
        ≤ ‖x - y‖ * ‖gradientWithin f U x - gradientWithin f U y‖ := by
          exact abs_real_inner_le_norm _ _
    _ ≤ ‖x - y‖ * ((β : ℝ) * ‖x - y‖) := by
      gcongr
    _ = (β : ℝ) * ‖x - y‖ ^ 2 := by
      ring
    _ = (β : ℝ) * ‖y - x‖ ^ 2 := by
      rw [norm_sub_rev]

end
