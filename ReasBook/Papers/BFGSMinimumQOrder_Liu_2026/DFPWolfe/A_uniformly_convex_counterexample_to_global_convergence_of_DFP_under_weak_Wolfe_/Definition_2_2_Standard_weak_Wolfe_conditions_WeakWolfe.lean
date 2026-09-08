module

public import ReasLib.Optimization.LineSearch

universe u

/- Compatibility bridge for the former weak-Wolfe owner. -/
#check (LineSearch.IsWeakWolfe :
  {E : Type u} → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] → [CompleteSpace E] →
    ℝ → ℝ → (E → ℝ) → E → E → Prop)
