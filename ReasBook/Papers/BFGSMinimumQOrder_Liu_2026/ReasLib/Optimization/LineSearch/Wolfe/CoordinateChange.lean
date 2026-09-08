module

public import ReasLib.Analysis.Calculus.Gradient.CoordinateChange
public import ReasLib.Optimization.LineSearch.Wolfe.Map
public import ReasLib.Optimization.LineSearch.Wolfe.WeakLegacy

public section

/-!
# Wolfe conditions under invertible coordinate changes

The line-derivative API already transports along arbitrary linear maps.  This module gives the
common continuous-linear-equivalence spelling used by affine normalizations.
-/

noncomputable section

universe u v

namespace LineSearch.Wolfe

/-- Weak Wolfe satisfaction is unchanged by pulling an objective back along an equivalence. -/
theorem IsWeak.comp_continuousLinearEquiv_iff
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : Coefficients} {f : F → ℝ}
    (L : E ≃L[ℝ] F) (x s : E) :
    IsWeak p (f ∘ L) x s ↔ IsWeak p f (L x) (L s) := by
  symm
  apply IsWeak.map_iff (L := L.toLinearMap)
  intro z
  rfl

/-- Strong Wolfe satisfaction is unchanged by pulling an objective back along an equivalence. -/
theorem IsStrong.comp_continuousLinearEquiv_iff
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : Coefficients} {f : F → ℝ}
    (L : E ≃L[ℝ] F) (x s : E) :
    IsStrong p (f ∘ L) x s ↔ IsStrong p f (L x) (L s) := by
  symm
  apply IsStrong.map_iff (L := L.toLinearMap)
  intro z
  rfl

end LineSearch.Wolfe

namespace LineSearch.IsWeakWolfe

/-- The gradient-based weak Wolfe conditions are invariant under an isometric
linear change of coordinates. -/
theorem comp_linearIsometryEquiv
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {c₁ c₂ : ℝ} {f : F → ℝ} {x s : F}
    (h : LineSearch.IsWeakWolfe c₁ c₂ f x s) (Q : E ≃ₗᵢ[ℝ] F) :
    LineSearch.IsWeakWolfe c₁ c₂ (f ∘ Q) (Q.symm x) (Q.symm s) := by
  have hstart : Q (Q.symm x) = x := Q.apply_symm_apply x
  have hnext : Q (Q.symm x + Q.symm s) = x + s := by
    rw [map_add, Q.apply_symm_apply, Q.apply_symm_apply]
  have hgradientStart : gradient (f ∘ Q) (Q.symm x) = Q.symm (gradient f x) := by
    have hgradient := Q.toContinuousLinearEquiv.comp_right_gradient f (Q.symm x)
    simpa [Function.comp_def, hstart, Q.adjoint_eq_symm] using hgradient
  have hgradientNext : gradient (f ∘ Q) (Q.symm x + Q.symm s) =
      Q.symm (gradient f (x + s)) := by
    have hgradient :=
      Q.toContinuousLinearEquiv.comp_right_gradient f (Q.symm x + Q.symm s)
    simpa [Function.comp_def, hnext, Q.adjoint_eq_symm] using hgradient
  refine {
    c₁_pos := h.c₁_pos
    c₁_lt_c₂ := h.c₁_lt_c₂
    c₂_lt_one := h.c₂_lt_one
    differentiableAt := ?_
    differentiableAtNext := ?_
    armijo := ?_
    weakCurvature := ?_
  }
  · have hf : DifferentiableAt ℝ f (Q (Q.symm x)) := by
      simpa only [hstart] using h.differentiableAt
    exact hf.comp (Q.symm x) Q.differentiableAt
  · have hf : DifferentiableAt ℝ f (Q (Q.symm x + Q.symm s)) := by
      simpa only [hnext] using h.differentiableAtNext
    exact hf.comp (Q.symm x + Q.symm s) Q.differentiableAt
  · rw [Function.comp_apply, Function.comp_apply, hnext, hstart, hgradientStart]
    simpa only [Q.symm.inner_map_map] using h.armijo
  · rw [hgradientStart, hgradientNext]
    simpa only [Q.symm.inner_map_map] using h.weakCurvature

end LineSearch.IsWeakWolfe
