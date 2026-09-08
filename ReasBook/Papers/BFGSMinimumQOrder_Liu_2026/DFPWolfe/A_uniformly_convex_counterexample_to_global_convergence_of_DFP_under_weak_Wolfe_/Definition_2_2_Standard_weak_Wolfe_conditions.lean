module

import ReasLib.Optimization.LineSearch

universe u

/- Definition 2.2 (Standard weak Wolfe conditions) -/
#check (LineSearch.IsWeakWolfe :
  {E : Type u} → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] → [CompleteSpace E] →
    ℝ → ℝ → (E → ℝ) → E → E → Prop)
