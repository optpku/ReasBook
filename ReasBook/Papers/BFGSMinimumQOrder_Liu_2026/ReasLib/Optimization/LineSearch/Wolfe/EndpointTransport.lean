module

public import ReasLib.Optimization.LineSearch.Wolfe

public section

/-!
# Endpoint transport for directional Wolfe certificates

The directional Wolfe predicates inspect only endpoint values and endpoint line derivatives.
This module packages the corresponding transport principle without requiring equality of the
two objectives on the whole search line.
-/

noncomputable section

universe u

namespace LineSearch.Wolfe

/-- Endpoint values and line derivatives transport a weak Wolfe certificate to a second
objective, provided the second objective is line-differentiable at both endpoints. -/
theorem IsWeak.transfer_of_endpoint_data {E : Type u} [AddCommGroup E] [Module ℝ E]
    {p : Coefficients} {f g : E → ℝ} {x s : E} (h : IsWeak p f x s)
    (hstart : LineDifferentiableAt ℝ g x s)
    (hnext : LineDifferentiableAt ℝ g (x + s) s)
    (hvalue_start : g x = f x)
    (hvalue_next : g (x + s) = f (x + s))
    (hline_start : lineDeriv ℝ g x s = lineDeriv ℝ f x s)
    (hline_next : lineDeriv ℝ g (x + s) s = lineDeriv ℝ f (x + s) s) :
    IsWeak p g x s := by
  refine {
    lineDifferentiableAt := hstart
    lineDifferentiableAtNext := hnext
    armijo := ?_
    weakCurvature := ?_ }
  · rw [hvalue_start, hvalue_next, hline_start]
    exact h.armijo
  · rw [hline_start, hline_next]
    exact h.weakCurvature

/-- Endpoint values and line derivatives transport a strong Wolfe certificate to a second
objective, provided the second objective is line-differentiable at both endpoints. -/
theorem IsStrong.transfer_of_endpoint_data {E : Type u} [AddCommGroup E] [Module ℝ E]
    {p : Coefficients} {f g : E → ℝ} {x s : E} (h : IsStrong p f x s)
    (hstart : LineDifferentiableAt ℝ g x s)
    (hnext : LineDifferentiableAt ℝ g (x + s) s)
    (hvalue_start : g x = f x)
    (hvalue_next : g (x + s) = f (x + s))
    (hline_start : lineDeriv ℝ g x s = lineDeriv ℝ f x s)
    (hline_next : lineDeriv ℝ g (x + s) s = lineDeriv ℝ f (x + s) s) :
    IsStrong p g x s := by
  refine {
    lineDifferentiableAt := hstart
    lineDifferentiableAtNext := hnext
    armijo := ?_
    strongCurvature := ?_ }
  · rw [hvalue_start, hvalue_next, hline_start]
    exact h.armijo
  · rw [hline_start, hline_next]
    exact h.strongCurvature

end LineSearch.Wolfe
