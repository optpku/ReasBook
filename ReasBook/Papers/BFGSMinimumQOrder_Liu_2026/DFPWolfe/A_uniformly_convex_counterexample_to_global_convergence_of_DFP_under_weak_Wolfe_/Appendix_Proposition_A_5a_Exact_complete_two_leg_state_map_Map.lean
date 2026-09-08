module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

/- Appendix Proposition A.5a (Exact complete two-leg state map): the explicit
signed factored map on the common two-leg state space. -/
#check (DFP.TwoLeg.stateMap :
  (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ))
