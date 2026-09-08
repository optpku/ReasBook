module

public import ReasLib.Optimization.LineSearch

public section

/- Lemma 6.0 (The selected weak Wolfe constants are admissible): the constants
`c₁ = 1 / 4` and `c₂ = 3 / 4` satisfy the weak Wolfe coefficient bounds. -/
#check (LineSearch.IsWeakWolfe.selectedConstantsAdmissible :
  0 < (1 / 4 : ℝ) ∧ (1 / 4 : ℝ) < (3 / 4 : ℝ) ∧ (3 / 4 : ℝ) < 1)
