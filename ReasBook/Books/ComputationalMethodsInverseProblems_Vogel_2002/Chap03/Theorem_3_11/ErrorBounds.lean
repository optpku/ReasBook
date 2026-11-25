/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Theorem_3_11.Convergence
public import Mathlib.Analysis.Calculus.MeanValue

public section

noncomputable section

open Set

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A Lipschitz derivative bounds the first-order remainder by half the Lipschitz constant
times the squared displacement. -/
private lemma norm_remainder_le
    (g : H → H) (D : H → H →L[ℝ] H) {K : NNReal} {s : Set H}
    (hD : ∀ y ∈ s, HasFDerivAt g (D y) y) (hLip : LipschitzWith K D)
    (hs : Convex ℝ s) {x y : H} (hx : x ∈ s) (hy : y ∈ s) :
    ‖g y - g x - D x (y - x)‖ ≤ (K : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  let r : ℝ → H := fun t ↦ g (AffineMap.lineMap x y t) - g x - t • D x (y - x)
  have hdr : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt r ((D (AffineMap.lineMap x y t) - D x) (y - x)) t := by
    intro t ht
    have h := ((hD _ (hs.lineMap_mem hx hy ht)).comp_hasDerivAt t
      AffineMap.hasDerivAt_lineMap).sub_const (g x)
    simpa only [r, sub_apply, Function.comp_def, Pi.sub_apply, id_eq, one_smul] using!
      h.sub ((hasDerivAt_id t).smul_const (D x (y - x)))
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖(D (AffineMap.lineMap x y t) - D x) (y - x)‖ ≤
        (K : ℝ) * ‖y - x‖ ^ 2 * t := by
    intro t ht
    calc
      _ ≤ ‖D (AffineMap.lineMap x y t) - D x‖ * ‖y - x‖ :=
        (D (AffineMap.lineMap x y t) - D x).le_opNorm _
      _ ≤ ((K : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ :=
        mul_le_mul_of_nonneg_right (hLip.norm_sub_le _ _) (norm_nonneg _)
      _ = (K : ℝ) * ‖y - x‖ ^ 2 * t := by
        rw [AffineMap.lineMap_apply_module', add_sub_cancel_right, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t ht ↦ (hdr t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hdr t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (B := fun t ↦ ((K : ℝ) / 2 * ‖y - x‖ ^ 2) * t ^ 2)
    (B' := fun t ↦ (K : ℝ) * ‖y - x‖ ^ 2 * t)
    (by simp [r])
    (fun t ↦ by
      convert! ((hasDerivAt_id t).pow 2).const_mul ((K : ℝ) / 2 * ‖y - x‖ ^ 2) using 1
      dsimp
      ring)
    hbound (x := 1) (by norm_num)
  simpa only [r, AffineMap.lineMap_apply_one, one_smul, one_pow, mul_one] using h

/-- Strong positivity gives a lower bound for the norm of the Hessian image. -/
private lemma norm_hessian_lowerBound
    (J : H → ℝ) (fStar : H) {K : NNReal} {μ : ℝ}
    (hModel : HasQuadraticConvergenceModel J fStar K μ) (z : H) :
    μ * ‖z‖ ≤ ‖hessian J fStar z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn := norm_pos_iff.mpr hz
    have hi := (hModel.inner_lowerBound z).trans (real_inner_le_norm _ _)
    have hi' : (μ * ‖z‖) * ‖z‖ ≤ ‖hessian J fStar z‖ * ‖z‖ := by
      nlinarith [hi]
    exact (mul_le_mul_iff_left₀ hn).1 hi'

/-- The Newton equation and the Lipschitz remainder give the one-step quadratic bound. -/
private lemma newton_step_error
    (J : H → ℝ) (fStar : H) {K : NNReal} {μ r : ℝ}
    (hD : ∀ y ∈ Metric.ball fStar r, HasFDerivAt (gradient J) (hessian J y) y)
    (hModel : HasQuadraticConvergenceModel J fStar K μ)
    {x y : H} (hx : x ∈ Metric.ball fStar r)
    (hsmall : (K : ℝ) * ‖x - fStar‖ < μ / 2)
    (hstep : IsStep J x (y - x)) :
    ‖y - fStar‖ ≤ convergenceConstant K μ * ‖x - fStar‖ ^ 2 := by
  have hr : 0 < r := lt_of_le_of_lt (dist_nonneg : 0 ≤ dist x fStar) hx
  have hrem := norm_remainder_le (gradient J) (hessian J) hD hModel.hessian_lipschitz
    (convex_ball fStar r) hx (Metric.mem_ball_self hr)
  have hEq : hessian J x (y - fStar) =
      gradient J fStar - gradient J x - hessian J x (fStar - x) := by
    have hs := (isStep_iff J x (y - x)).1 hstep
    have hs' : hessian J x (y - x) = -gradient J x :=
      eq_neg_of_add_eq_zero_right hs
    calc
      _ = hessian J x (y - x) - hessian J x (fStar - x) := by
        rw [← map_sub]
        congr 1
        abel
      _ = _ := by rw [hs', hModel.gradient_eq_zero, zero_sub]
  have hrem' : ‖hessian J x (y - fStar)‖ ≤ (K : ℝ) / 2 * ‖x - fStar‖ ^ 2 := by
    rw [hEq, norm_sub_rev x fStar]
    exact hrem
  have hpert : ‖(hessian J fStar - hessian J x) (y - fStar)‖ ≤
      (K : ℝ) * ‖x - fStar‖ * ‖y - fStar‖ := by
    calc
      _ ≤ ‖hessian J fStar - hessian J x‖ * ‖y - fStar‖ :=
        (hessian J fStar - hessian J x).le_opNorm _
      _ ≤ ((K : ℝ) * ‖fStar - x‖) * ‖y - fStar‖ :=
        mul_le_mul_of_nonneg_right (hModel.hessian_lipschitz.norm_sub_le _ _) (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev fStar x]
  have hnorm : ‖hessian J fStar (y - fStar)‖ ≤
      (K : ℝ) * ‖x - fStar‖ * ‖y - fStar‖ + (K : ℝ) / 2 * ‖x - fStar‖ ^ 2 := by
    calc
      _ = ‖(hessian J fStar - hessian J x) (y - fStar) + hessian J x (y - fStar)‖ := by
        simp only [sub_apply, sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hpert hrem')
  have hlower := norm_hessian_lowerBound J fStar hModel (y - fStar)
  have hhalf : μ / 2 * ‖y - fStar‖ ≤ (K : ℝ) / 2 * ‖x - fStar‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall.le) (norm_nonneg (y - fStar))]
  rw [convergenceConstant_eq]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hModel.mu_pos).2
  nlinarith [hhalf]

/-- Genuine second derivatives throughout the convergence ball imply both the quadratic
Newton error estimate and a uniform halving of the errors. The halving bound also keeps all
iterates in this ball, so no regularity away from the ball is required. -/
theorem quadraticErrorBound_and_halfErrorBound
    (J : H → ℝ) (f : ℕ → H) (fStar : H) {K : NNReal} {μ : ℝ}
    (hSecondDerivative : ∀ y ∈ Metric.ball fStar (1 / (2 * convergenceConstant K μ)),
      HasFDerivAt J (fderiv ℝ J y) y ∧
        HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) y) y)
    (hModel : HasQuadraticConvergenceModel J fStar K μ)
    (hNewton : IsIterateSequence J f)
    (h0 : StartsInConvergenceBall f fStar K μ) :
    (∀ v : ℕ, ‖f (v + 1) - fStar‖ ≤ convergenceConstant K μ * ‖f v - fStar‖ ^ 2) ∧
      (∀ v : ℕ, ‖f (v + 1) - fStar‖ ≤ ‖f v - fStar‖ / 2) := by
  let c := convergenceConstant K μ
  have hstart : ‖f 0 - fStar‖ < 1 / (2 * c) :=
    (startsInConvergenceBall_iff f fStar K μ).1 h0
  have hc : 0 < c := by
    have hr := lt_of_le_of_lt (norm_nonneg _) hstart
    have hpos := (one_div_pos).1 hr
    linarith
  have hD : ∀ y ∈ Metric.ball fStar (1 / (2 * c)),
      HasFDerivAt (gradient J) (hessian J y) y := by
    intro y hy
    let R := (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have heq : R.comp (fderiv ℝ (fderiv ℝ J) y) = hessian J y := by
      ext h
      apply ext_inner_right ℝ
      intro k
      change inner ℝ ((InnerProductSpace.toDual ℝ H).symm
        ((fderiv ℝ (fderiv ℝ J) y) h)) k = inner ℝ (hessian J y h) k
      rw [InnerProductSpace.toDual_symm_apply, hessian_inner]
    rw [← heq]
    exact R.hasFDerivAt.comp y (hSecondDerivative y hy).2
  have hsmall : ∀ {x : H}, ‖x - fStar‖ < 1 / (2 * c) → c * ‖x - fStar‖ < 1 / 2 := by
    intro x hx
    have := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc)).1 hx
    nlinarith
  have hstep : ∀ v, ‖f v - fStar‖ < 1 / (2 * c) →
      ‖f (v + 1) - fStar‖ ≤ c * ‖f v - fStar‖ ^ 2 := by
    intro v hv
    have hs : (K : ℝ) * ‖f v - fStar‖ < μ / 2 := by
      have hs := hsmall hv
      change (K : ℝ) / μ * ‖f v - fStar‖ < 1 / 2 at hs
      rw [div_mul_eq_mul_div] at hs
      have := (div_lt_iff₀ hModel.mu_pos).1 hs
      nlinarith
    exact newton_step_error J fStar hD hModel (by simpa [Metric.mem_ball, dist_eq_norm] using hv)
      hs (hNewton v)
  have hhalf : ∀ v, ‖f v - fStar‖ < 1 / (2 * c) →
      ‖f (v + 1) - fStar‖ ≤ ‖f v - fStar‖ / 2 := by
    intro v hv
    have hq := hstep v hv
    have hs := hsmall hv
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.le) (norm_nonneg (f v - fStar))]
  have hball : ∀ v, ‖f v - fStar‖ < 1 / (2 * c) := by
    intro v
    induction v with
    | zero => exact hstart
    | succ v hv =>
      have hh := hhalf v hv
      have hn := norm_nonneg (f v - fStar)
      linarith
  exact ⟨fun v ↦ hstep v (hball v), fun v ↦ hhalf v (hball v)⟩

end Newton
