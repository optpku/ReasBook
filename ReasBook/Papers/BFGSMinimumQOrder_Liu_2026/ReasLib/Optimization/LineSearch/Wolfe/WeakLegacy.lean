module

public import ReasLib.Optimization.LineSearch.Wolfe.Gradient

public section

/-!
# Gradient bridge for directional weak Wolfe certificates

The directional Wolfe predicates are convenient for line-search arguments, while the legacy
predicate records canonical gradients at the two endpoints.  This module provides the bridge in
the direction needed by endpoint-gradient consumers.
-/

noncomputable section

universe u

namespace LineSearch.Wolfe

/-- A directional weak-Wolfe certificate and certified endpoint gradients yield the legacy
gradient-based weak-Wolfe predicate. -/
theorem IsWeak.toIsWeakWolfe {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {p : Coefficients} {f : E → ℝ}
    {x s g gNext : E} (h : IsWeak p f x s)
    (atStart : HasGradientAt f g x)
    (atNext : HasGradientAt f gNext (x + s)) :
    LineSearch.IsWeakWolfe p.c₁ p.c₂ f x s := by
  have startLine : lineDeriv ℝ f x s = inner ℝ g s := by
    rw [atStart.differentiableAt.lineDeriv_eq_fderiv, atStart.fderiv_apply]
  have nextLine : lineDeriv ℝ f (x + s) s = inner ℝ gNext s := by
    rw [atNext.differentiableAt.lineDeriv_eq_fderiv, atNext.fderiv_apply]
  apply LineSearch.IsWeakWolfe.ofHasGradientAt p.c₁_pos p.c₁_lt_c₂ p.c₂_lt_one
    atStart atNext
  · apply isArmijo_iff.mp
    simpa only [startLine] using h.armijo
  · apply isWeakCurvature_iff.mp
    simpa only [startLine, nextLine] using h.weakCurvature

end LineSearch.Wolfe
