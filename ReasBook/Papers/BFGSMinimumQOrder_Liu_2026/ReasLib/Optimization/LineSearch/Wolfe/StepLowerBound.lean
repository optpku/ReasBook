module

public import ReasLib.Optimization.LineSearch.Wolfe.Gradient

public section

/-!
# Quantitative lower bounds for Wolfe steps

This file isolates the algebraic part of the standard Lipschitz-gradient line-search
estimate.  The hypotheses are phrased in terms of the endpoint gradient pairing and a
secant norm bound, so objective-specific adapters can reuse the result independently.
-/

noncomputable section

universe u

namespace LineSearch.Wolfe

/-- Weak-Wolfe curvature and a Lipschitz secant estimate imply the unnormalised step bound
`(1 - c₂) * (-⟪g,d⟫) ≤ L * α * ‖d‖ ^ 2`. -/
theorem alpha_mul_sq_le_of_weak_curvature
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c₂ α L : ℝ} {d g gNext : E}
    (hc₂ : c₂ < 1) (hα : 0 < α)
    (hcurv : c₂ * inner ℝ g (α • d) ≤ inner ℝ gNext (α • d))
    (hsec : ‖gNext - g‖ ≤ L * ‖α • d‖) :
    (1 - c₂) * (-inner ℝ g d) ≤ L * α * ‖d‖ ^ 2 := by
  have hcurvScaled : c₂ * inner ℝ g d ≤ inner ℝ gNext d := by
    have hscaled : α * (c₂ * inner ℝ g d) ≤ α * inner ℝ gNext d := by
      simpa only [real_inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using hcurv
    nlinarith [hscaled]
  have hcoeff : 0 < 1 - c₂ := sub_pos.mpr hc₂
  have hpair : (1 - c₂) * (-inner ℝ g d) ≤ inner ℝ (gNext - g) d := by
    rw [inner_sub_left]
    linarith [hcoeff]
  have hpairNorm : inner ℝ (gNext - g) d ≤ ‖gNext - g‖ * ‖d‖ :=
    real_inner_le_norm _ _
  have hnormStep : ‖α • d‖ = α * ‖d‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
  have hsecNorm : ‖gNext - g‖ ≤ L * (α * ‖d‖) := by
    simpa only [hnormStep] using hsec
  have hnormD : 0 ≤ ‖d‖ := norm_nonneg d
  have hupper : ‖gNext - g‖ * ‖d‖ ≤ L * α * ‖d‖ ^ 2 := by
    calc
      ‖gNext - g‖ * ‖d‖ ≤ (L * (α * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hsecNorm hnormD
      _ = L * α * ‖d‖ ^ 2 := by ring
  exact hpair.trans (hpairNorm.trans hupper)

/-- A positive weak-Wolfe step with a Lipschitz secant estimate has an explicit lower bound. -/
theorem alpha_lower_bound_of_weak_curvature
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {c₂ α L : ℝ} {d g gNext : E}
    (hc₂ : c₂ < 1) (hα : 0 < α) (hL : 0 < L) (hd : d ≠ 0)
    (hcurv : c₂ * inner ℝ g (α • d) ≤ inner ℝ gNext (α • d))
    (hsec : ‖gNext - g‖ ≤ L * ‖α • d‖) :
    ((1 - c₂) * (-inner ℝ g d)) / (L * ‖d‖ ^ 2) ≤ α := by
  have hmain := alpha_mul_sq_le_of_weak_curvature hc₂ hα hcurv hsec
  have hnormD : 0 < ‖d‖ := (norm_pos_iff.mpr hd)
  have hden : 0 < L * ‖d‖ ^ 2 := by
    exact mul_pos hL (sq_pos_of_pos hnormD)
  apply (div_le_iff₀ hden).2
  nlinarith [hmain]

/-- A gradient-based weak-Wolfe certificate with a global Lipschitz gradient has the same
quantitative lower bound for a positive step `α • d`. -/
theorem alpha_lower_bound_of_isWeakWolfe
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c₁ c₂ α L : ℝ} {f : E → ℝ} {x d : E}
    (h : LineSearch.IsWeakWolfe c₁ c₂ f x (α • d))
    (hα : 0 < α) (hL : 0 < L) (hd : d ≠ 0)
    (hLip : ∀ u v : E, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖) :
    ((1 - c₂) * (-inner ℝ (gradient f x) d)) / (L * ‖d‖ ^ 2) ≤ α := by
  have hsec : ‖gradient f (x + α • d) - gradient f x‖ ≤ L * ‖α • d‖ := by
    simpa only [add_sub_cancel_left] using hLip (x + α • d) x
  exact alpha_lower_bound_of_weak_curvature h.c₂_lt_one hα hL hd h.weakCurvature hsec

/-- For a steepest-descent direction, the general Wolfe step bound simplifies to
`(1 - c₂) / L`. -/
theorem alpha_lower_bound_of_isWeakWolfe_negGradient
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c₁ c₂ α L : ℝ} {f : E → ℝ} {x : E}
    (h : LineSearch.IsWeakWolfe c₁ c₂ f x (α • (-gradient f x)))
    (hα : 0 < α) (hL : 0 < L) (hgrad : gradient f x ≠ 0)
    (hLip : ∀ u v : E, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖) :
    (1 - c₂) / L ≤ α := by
  have hgeneral := alpha_lower_bound_of_isWeakWolfe h hα hL (neg_ne_zero.mpr hgrad) hLip
  have hnorm : 0 < ‖gradient f x‖ := norm_pos_iff.mpr hgrad
  have hsq : 0 < ‖gradient f x‖ ^ 2 := sq_pos_of_pos hnorm
  have hden : L * ‖gradient f x‖ ^ 2 ≠ 0 :=
    ne_of_gt (mul_pos hL hsq)
  have hcancel :
      ((1 - c₂) * (-inner ℝ (gradient f x) (-gradient f x))) /
          (L * ‖-gradient f x‖ ^ 2) = (1 - c₂) / L := by
    simp only [inner_neg_right, neg_neg, real_inner_self_eq_norm_sq, norm_neg]
    field_simp [hden]
  rw [hcancel] at hgeneral
  exact hgeneral

/-- A descent weak-Wolfe step decreases the objective by the usual one-step Zoutendijk
quantity when the gradient is globally Lipschitz. -/
theorem weakWolfe_decrease_lower_bound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c₁ c₂ α L : ℝ} {f : E → ℝ} {x d : E}
    (h : LineSearch.IsWeakWolfe c₁ c₂ f x (α • d))
    (hα : 0 < α) (hL : 0 < L) (hd : d ≠ 0)
    (hdescent : inner ℝ (gradient f x) d < 0)
    (hLip : ∀ u v : E, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖) :
    c₁ * (1 - c₂) * (inner ℝ (gradient f x) d) ^ 2 /
        (L * ‖d‖ ^ 2) ≤ f x - f (x + α • d) := by
  have hαlower := alpha_lower_bound_of_isWeakWolfe h hα hL hd hLip
  have hq : 0 < -inner ℝ (gradient f x) d := by
    linarith
  have hscale :
      c₁ * (-inner ℝ (gradient f x) d) *
          (((1 - c₂) * (-inner ℝ (gradient f x) d)) / (L * ‖d‖ ^ 2)) ≤
        c₁ * (-inner ℝ (gradient f x) d) * α := by
    exact mul_le_mul_of_nonneg_left hαlower (mul_nonneg h.c₁_pos.le hq.le)
  have hden : 0 < L * ‖d‖ ^ 2 := by
    exact mul_pos hL (sq_pos_of_pos (norm_pos_iff.mpr hd))
  have hratio :
      c₁ * (-inner ℝ (gradient f x) d) *
          (((1 - c₂) * (-inner ℝ (gradient f x) d)) / (L * ‖d‖ ^ 2)) =
        c₁ * (1 - c₂) * (inner ℝ (gradient f x) d) ^ 2 /
          (L * ‖d‖ ^ 2) := by
    field_simp [ne_of_gt hden]
  have hbound :
      c₁ * (1 - c₂) * (inner ℝ (gradient f x) d) ^ 2 /
          (L * ‖d‖ ^ 2) ≤
        c₁ * (-inner ℝ (gradient f x) d) * α := by
    rw [← hratio]
    exact hscale
  have hdecrease :
      c₁ * (-inner ℝ (gradient f x) d) * α ≤ f x - f (x + α • d) := by
    have harm := h.armijo
    rw [real_inner_smul_right] at harm
    nlinarith [harm]
  exact hbound.trans hdecrease

end LineSearch.Wolfe
