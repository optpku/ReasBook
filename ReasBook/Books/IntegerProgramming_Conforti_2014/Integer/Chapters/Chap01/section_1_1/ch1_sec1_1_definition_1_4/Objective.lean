module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace

open scoped Matrix

public section

/-- The linear objective `(x, y) ↦ c ⬝ᵥ x + h ⬝ᵥ y` on the ambient mixed space. -/
def mixed_linear_objective
    {n p : ℕ}
    (c : Fin n → ℝ) (h : Fin p → ℝ) (xy : MixedRealPoint n p) : ℝ :=
  c ⬝ᵥ xy.1 + h ⬝ᵥ xy.2

/-- Unfolding equation for `mixed_linear_objective`. -/
theorem mixed_linear_objective_def
    {n p : ℕ}
    (c : Fin n → ℝ) (h : Fin p → ℝ) (xy : MixedRealPoint n p) :
    mixed_linear_objective c h xy = c ⬝ᵥ xy.1 + h ⬝ᵥ xy.2 := by
  rfl

end
