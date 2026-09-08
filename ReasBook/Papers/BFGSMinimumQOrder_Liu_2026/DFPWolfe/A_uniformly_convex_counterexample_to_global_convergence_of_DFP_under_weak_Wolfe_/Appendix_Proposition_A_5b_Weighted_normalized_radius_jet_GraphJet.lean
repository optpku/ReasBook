module

public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet

public section

/- The polynomial graph path is shared DFP two-leg data. -/
#check (DFP.TwoLeg.graphJetPath :
  ℝ → ℝ → ℝ → ℝ → ℝ → ℝ × ℝ × ℝ)

/- Its computation theorem gives all three path coordinates. -/
#check (DFP.TwoLeg.graphJetPath_apply :
  ∀ P₃ H₃ P₄ H₄ ε : ℝ,
    DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε =
      (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4, 1 + H₃ * ε ^ 3 + H₄ * ε ^ 4))

/- The slow-graph polynomial is the specialized shared path. -/
#check (DFP.TwoLeg.slowGraphJetPath : ℝ → ℝ × ℝ × ℝ)

/- Its computation theorem records the exact slow-graph coefficients. -/
#check (DFP.TwoLeg.slowGraphJetPath_apply :
  ∀ ε : ℝ,
    DFP.TwoLeg.slowGraphJetPath ε =
      (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3))
