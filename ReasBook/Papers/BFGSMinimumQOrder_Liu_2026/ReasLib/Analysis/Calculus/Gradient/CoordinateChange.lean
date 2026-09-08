module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import ReasLib.Analysis.InnerProductSpace.Congruence

public section

/-!
# Gradients under linear coordinate changes
-/

noncomputable section

universe u v

open scoped InnerProduct

/-- A certified gradient pulls back by the adjoint of a continuous linear equivalence. -/
theorem HasGradientAt.comp_continuousLinearEquiv
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} {g : F} {x : E} (L : E ≃L[ℝ] F) (hf : HasGradientAt f g (L x)) :
    HasGradientAt (f ∘ L) ((L.toContinuousLinearMap†) g) x := by
  rw [hasGradientAt_iff_hasFDerivAt, L.toContinuousLinearMap.toDual_adjoint]
  exact L.comp_right_hasFDerivAt_iff.mpr hf.hasFDerivAt

/-- The gradient of a pullback is the adjoint pullback of the original gradient. -/
theorem ContinuousLinearEquiv.comp_right_gradient
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E ≃L[ℝ] F) (f : F → ℝ) (x : E) :
    gradient (f ∘ L) x = (L.toContinuousLinearMap†) (gradient f (L x)) := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, L.toContinuousLinearMap.toDual_adjoint, toDual_gradient]
  exact L.comp_right_fderiv

end
