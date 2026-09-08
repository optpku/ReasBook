module

public import ReasLib.Optimization.DFP.InverseUpdate

open scoped Matrix

universe u

/- A compatibility check for the reusable inverse-form DFP update. -/
#check (Matrix.inverseDFPUpdate :
  ∀ {n : Type u} [Fintype n], Matrix n n ℝ → (n → ℝ) → (n → ℝ) → Matrix n n ℝ)
