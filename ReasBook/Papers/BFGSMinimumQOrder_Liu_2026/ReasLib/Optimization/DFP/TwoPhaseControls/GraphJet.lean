module

public import Mathlib.Data.Real.Basic

public section

namespace DFP.TwoLeg

/-- The polynomial graph path with independently specified cubic and quartic
coefficients in the shape and high-eigenvalue coordinates. -/
def graphJetPath (P₃ H₃ P₄ H₄ ε : ℝ) : ℝ × ℝ × ℝ :=
  (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4, 1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)

/-- The three coordinates of the polynomial graph path. -/
theorem graphJetPath_apply (P₃ H₃ P₄ H₄ ε : ℝ) :
    graphJetPath P₃ H₃ P₄ H₄ ε =
      (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4, 1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) := by
  rfl

/-- The polynomial approximation to the invariant slow graph through degree four. -/
noncomputable def slowGraphJetPath (ε : ℝ) : ℝ × ℝ × ℝ :=
  graphJetPath (198 / 5) 8 (-9 / 5) 0 ε

/-- The three coordinates of the polynomial slow-graph approximation. -/
theorem slowGraphJetPath_apply (ε : ℝ) :
    slowGraphJetPath ε =
      (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3) := by
  simp [slowGraphJetPath, graphJetPath, sub_eq_add_neg, neg_div, neg_mul]

end DFP.TwoLeg
