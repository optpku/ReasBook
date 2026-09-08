module

public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet

public section

/-!
# Basic interfaces for polynomial graph jets

This companion exposes the coordinate formulas without depending on the original
placeholder proofs.
-/

namespace DFP.TwoLeg

/-- The graph jet path unfolds to its three polynomial coordinates. -/
theorem graphJetPath_eq (P₃ H₃ P₄ H₄ ε : ℝ) :
    graphJetPath P₃ H₃ P₄ H₄ ε =
      (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4, 1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) := by
  exact graphJetPath_apply P₃ H₃ P₄ H₄ ε

/-- The slow graph jet has the displayed fixed polynomial coefficients. -/
theorem slowGraphJetPath_eq (ε : ℝ) :
    slowGraphJetPath ε =
      (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3) := by
  exact slowGraphJetPath_apply ε

end DFP.TwoLeg
