module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

universe u

/-- Passing from the derivative covector to its Riesz-representing gradient preserves the
operator norm of the second Fréchet derivative. -/
theorem norm_fderiv_gradient_eq_norm_fderiv_fderiv
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  unfold gradient
  have hRiesz :
      fderiv ℝ
          (fun y ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) x =
        ((InnerProductSpace.toDual ℝ E).symm : StrongDual ℝ E →L[ℝ] E) ∘L
          fderiv ℝ (fderiv ℝ f) x := by
    have hfun :
        (fun y ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)) =
          (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f := rfl
    rw [hfun]
    exact LinearIsometryEquiv.comp_fderiv (InnerProductSpace.toDual ℝ E).symm
  rw [hRiesz]
  exact LinearIsometry.norm_toContinuousLinearMap_comp
    (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry

/-- The Hessian operator norm also agrees with the norm of the order-two iterated
Fréchet derivative. -/
theorem norm_fderiv_gradient_eq_norm_iteratedFDeriv_two
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x : E) :
    ‖fderiv ℝ (gradient f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  calc
    ‖fderiv ℝ (gradient f) x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ :=
      norm_fderiv_gradient_eq_norm_fderiv_fderiv f x
    _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ f) x‖ :=
      (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ f)).symm
    _ = ‖iteratedFDeriv ℝ 2 f x‖ :=
      norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (n := 1)
