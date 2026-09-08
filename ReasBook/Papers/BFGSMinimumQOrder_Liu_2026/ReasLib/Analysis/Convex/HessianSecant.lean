module

public import ReasLib.Analysis.Convex.Hessian

public section

universe u

/-- A positive global Hessian lower bound makes the gradient strongly monotone along
every displacement. -/
theorem inner_gradient_sub_ge_of_hessian_lower_bound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f) (hm : 0 < m)
    (h_lower : ∀ x v : E,
      m * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) x v) v)
    (x y : E) :
    m * ‖y - x‖ ^ 2 ≤ inner ℝ (gradient f y - gradient f x) (y - x) := by
  have hxy := hf.firstOrderOfHessianLowerBound f m hm h_lower x y
  have hyx := hf.firstOrderOfHessianLowerBound f m hm h_lower y x
  have hdisplacement : x - y = -(y - x) := by
    abel
  rw [hdisplacement, inner_neg_right, norm_neg] at hyx
  rw [inner_sub_left]
  nlinarith

/-- A positive Hessian lower bound gives strict gradient-secant curvature for distinct
points. -/
theorem inner_gradient_sub_pos_of_hessian_lower_bound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f) (hm : 0 < m)
    (h_lower : ∀ x v : E,
      m * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) x v) v)
    {x y : E} (hxy : x ≠ y) :
    0 < inner ℝ (gradient f y - gradient f x) (y - x) := by
  have hnorm : 0 < ‖y - x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have hquadratic : 0 < ‖y - x‖ ^ 2 := sq_pos_of_pos hnorm
  have hleft : 0 < m * ‖y - x‖ ^ 2 := mul_pos hm hquadratic
  exact lt_of_lt_of_le hleft
    (inner_gradient_sub_ge_of_hessian_lower_bound f m hf hm h_lower x y)
