module

public import ReasLib.Optimization.DFP.AbstractSecantStep

public section

open scoped Matrix

section

variable {n : Type u} [Fintype n]

/- This forwarding bridge exposes the shared abstract secant-step constructor
to existing importers. -/
#check (DFP.AbstractSecantStep.ofMatrices :
  (H : Matrix n n ℝ) → (g : n → ℝ) → (A : Matrix n n ℝ) → (τ : ℝ) →
    H.PosDef → A.PosDef → 0 < τ → g ≠ 0 → DFP.AbstractSecantStep n)

end
