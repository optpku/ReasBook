module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.MeanValue

public section

universe u

/-- A uniform operator-norm bound on the derivative of a gradient controls gradient
differences along every chord. -/
theorem norm_gradient_sub_le_of_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {M : ℝ} (hgradient : Differentiable ℝ (gradient f))
    (hbound : ∀ z : E, ‖fderiv ℝ (gradient f) z‖ ≤ M) (x y : E) :
    ‖gradient f y - gradient f x‖ ≤ M * ‖y - x‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (f := gradient f) (C := M) (x := x) (y := y)
    (fun z _ ↦ hgradient z) (fun z _ ↦ hbound z) convex_univ
    (Set.mem_univ x) (Set.mem_univ y)

/-- The same Hessian-norm bound gives an absolute quadratic-form estimate for the
gradient secant in the displacement direction. -/
theorem abs_inner_gradient_sub_le_of_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {M : ℝ} (hgradient : Differentiable ℝ (gradient f))
    (hbound : ∀ z : E, ‖fderiv ℝ (gradient f) z‖ ≤ M) (x y : E) :
    |inner ℝ (gradient f y - gradient f x) (y - x)| ≤ M * ‖y - x‖ ^ 2 := by
  have hsecant := norm_gradient_sub_le_of_hessian_norm_le hgradient hbound x y
  calc
    |inner ℝ (gradient f y - gradient f x) (y - x)| ≤
        ‖gradient f y - gradient f x‖ * ‖y - x‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (M * ‖y - x‖) * ‖y - x‖ :=
      mul_le_mul_of_nonneg_right hsecant (norm_nonneg (y - x))
    _ = M * ‖y - x‖ ^ 2 := by
      rw [pow_two, mul_assoc]

/-- The secant quadratic form lies between the signed bounds supplied by a uniform
Hessian operator-norm estimate. -/
theorem inner_gradient_sub_bounds_of_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {M : ℝ} (hgradient : Differentiable ℝ (gradient f))
    (hbound : ∀ z : E, ‖fderiv ℝ (gradient f) z‖ ≤ M) (x y : E) :
    -M * ‖y - x‖ ^ 2 ≤ inner ℝ (gradient f y - gradient f x) (y - x) ∧
      inner ℝ (gradient f y - gradient f x) (y - x) ≤ M * ‖y - x‖ ^ 2 := by
  have habs := abs_inner_gradient_sub_le_of_hessian_norm_le hgradient hbound x y
  constructor
  · simpa only [neg_mul] using neg_le_of_abs_le habs
  · exact le_of_abs_le habs

/-- A globally C2 function with a uniform Hessian norm bound satisfies the gradient
secant estimate without requiring a separate differentiability hypothesis for its gradient. -/
theorem norm_gradient_sub_le_of_contDiff_hessian_norm_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {M : ℝ} (hf : ContDiff ℝ 2 f)
    (hbound : ∀ z : E, ‖fderiv ℝ (gradient f) z‖ ≤ M) (x y : E) :
    ‖gradient f y - gradient f x‖ ≤ M * ‖y - x‖ := by
  have horder : 1 + 1 ≤ (2 : WithTop ℕ∞) := by norm_num
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right horder
  have hgradientContDiff : ContDiff ℝ 1 (gradient f) := by
    have hgradient_eq : gradient f = fun z ↦
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
          (fderiv ℝ f z) := by
      funext z
      rfl
    rw [hgradient_eq]
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hfderiv
  exact norm_gradient_sub_le_of_hessian_norm_le
    hgradientContDiff.differentiable_one hbound x y
