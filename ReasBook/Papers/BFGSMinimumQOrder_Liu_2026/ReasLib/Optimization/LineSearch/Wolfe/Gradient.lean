module

public import ReasLib.Optimization.LineSearch
public import ReasLib.Optimization.LineSearch.Wolfe

public section

/-!
# Gradient adapters for Wolfe conditions

The directional-derivative Wolfe API is canonical.  This module connects it to certified
gradients and to the earlier gradient-based weak-Wolfe predicate.
-/

noncomputable section

universe u

namespace LineSearch.Wolfe

/-- Certified endpoint gradients construct weak Wolfe satisfaction. -/
theorem IsWeak.ofHasGradientAt {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {p : Coefficients} {f : E → ℝ}
    {x s g gNext : E} (atStart : HasGradientAt f g x)
    (atNext : HasGradientAt f gNext (x + s))
    (armijo : IsArmijo p.c₁ (f x) (f (x + s)) (inner ℝ g s))
    (curvature : IsWeakCurvature p.c₂ (inner ℝ g s) (inner ℝ gNext s)) :
    IsWeak p f x s := by
  have startLine : HasLineDerivAt ℝ f (inner ℝ g s) x s := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      atStart.hasFDerivAt.hasLineDerivAt s
  have nextLine : HasLineDerivAt ℝ f (inner ℝ gNext s) (x + s) s := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      atNext.hasFDerivAt.hasLineDerivAt s
  exact IsWeak.ofHasLineDerivAt startLine nextLine armijo curvature

/-- Certified endpoint gradients construct strong Wolfe satisfaction. -/
theorem IsStrong.ofHasGradientAt {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {p : Coefficients} {f : E → ℝ}
    {x s g gNext : E} (atStart : HasGradientAt f g x)
    (atNext : HasGradientAt f gNext (x + s))
    (armijo : IsArmijo p.c₁ (f x) (f (x + s)) (inner ℝ g s))
    (curvature : IsStrongCurvature p.c₂ (inner ℝ g s) (inner ℝ gNext s)) :
    IsStrong p f x s := by
  have startLine : HasLineDerivAt ℝ f (inner ℝ g s) x s := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      atStart.hasFDerivAt.hasLineDerivAt s
  have nextLine : HasLineDerivAt ℝ f (inner ℝ gNext s) (x + s) s := by
    simpa only [InnerProductSpace.toDual_apply_apply] using
      atNext.hasFDerivAt.hasLineDerivAt s
  exact IsStrong.ofHasLineDerivAt startLine nextLine armijo curvature

/-- A gradient-based weak-Wolfe certificate yields the directional-derivative formulation. -/
theorem IsWeak.ofIsWeakWolfe {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {p : Coefficients} {f : E → ℝ}
    {x s : E} (h : LineSearch.IsWeakWolfe p.c₁ p.c₂ f x s) :
    IsWeak p f x s := by
  exact IsWeak.ofHasGradientAt h.differentiableAt.hasGradientAt
    h.differentiableAtNext.hasGradientAt (isArmijo_iff.mpr h.armijo)
      (isWeakCurvature_iff.mpr h.weakCurvature)

/-- A strong directional-derivative certificate with certified endpoint gradients yields the
legacy gradient-based weak-Wolfe predicate along a nonascending direction. -/
theorem IsStrong.toIsWeakWolfe {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {p : Coefficients} {f : E → ℝ}
    {x s g gNext : E} (h : IsStrong p f x s) (atStart : HasGradientAt f g x)
    (atNext : HasGradientAt f gNext (x + s)) (descent : inner ℝ g s ≤ 0) :
    LineSearch.IsWeakWolfe p.c₁ p.c₂ f x s := by
  have startLine : lineDeriv ℝ f x s = inner ℝ g s := by
    rw [atStart.differentiableAt.lineDeriv_eq_fderiv, atStart.fderiv_apply]
  have nextLine : lineDeriv ℝ f (x + s) s = inner ℝ gNext s := by
    rw [atNext.differentiableAt.lineDeriv_eq_fderiv, atNext.fderiv_apply]
  have weak := h.toWeak (startLine.trans_le descent)
  apply LineSearch.IsWeakWolfe.ofHasGradientAt p.c₁_pos p.c₁_lt_c₂ p.c₂_lt_one
    atStart atNext
  · apply isArmijo_iff.mp
    simpa only [startLine] using weak.armijo
  · apply isWeakCurvature_iff.mp
    simpa only [startLine, nextLine] using weak.weakCurvature

end LineSearch.Wolfe
