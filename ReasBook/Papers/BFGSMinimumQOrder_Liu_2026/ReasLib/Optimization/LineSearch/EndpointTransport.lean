module

public import ReasLib.Optimization.LineSearch

public section

universe u

namespace LineSearch

/-- Endpoint values and canonical gradients transfer a weak-Wolfe certificate to a second
objective whose endpoint differentiability is known. -/
theorem IsWeakWolfe.transfer_of_endpoint_value_gradient_eq
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c₁ c₂ : ℝ} {f g : E → ℝ} {x s : E}
    (h : IsWeakWolfe c₁ c₂ f x s)
    (hstart : DifferentiableAt ℝ g x)
    (hnext : DifferentiableAt ℝ g (x + s))
    (hvalue_start : g x = f x)
    (hvalue_next : g (x + s) = f (x + s))
    (hgradient_start : gradient g x = gradient f x)
    (hgradient_next : gradient g (x + s) = gradient f (x + s)) :
    IsWeakWolfe c₁ c₂ g x s := by
  refine
    { c₁_pos := h.c₁_pos
      c₁_lt_c₂ := h.c₁_lt_c₂
      c₂_lt_one := h.c₂_lt_one
      differentiableAt := hstart
      differentiableAtNext := hnext
      armijo := ?_
      weakCurvature := ?_ }
  · rw [hvalue_next, hvalue_start, hgradient_start]
    exact h.armijo
  · rw [hgradient_start, hgradient_next]
    exact h.weakCurvature

/-- Certified endpoint gradients provide the canonical-gradient hypotheses needed to transfer a
weak-Wolfe certificate between objectives with matching endpoint data. -/
theorem IsWeakWolfe.transfer_of_endpoint_value_hasGradientAt
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {c₁ c₂ : ℝ} {f g : E → ℝ} {x s gStart gNext : E}
    (h : IsWeakWolfe c₁ c₂ f x s)
    (hstart : HasGradientAt g gStart x)
    (hnext : HasGradientAt g gNext (x + s))
    (hvalue_start : g x = f x)
    (hvalue_next : g (x + s) = f (x + s))
    (hgradient_start : gStart = gradient f x)
    (hgradient_next : gNext = gradient f (x + s)) :
    IsWeakWolfe c₁ c₂ g x s := by
  apply h.transfer_of_endpoint_value_gradient_eq hstart.differentiableAt hnext.differentiableAt
    hvalue_start hvalue_next
  · exact hstart.gradient.trans hgradient_start
  · exact hnext.gradient.trans hgradient_next

end LineSearch
