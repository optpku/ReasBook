module

public import ReasLib.Optimization.DFP.Polar.Normalized.Dynamics

/- Compatibility surface for source-facing consumers of normalized polar dynamics. -/
#check (DFP.Polar.Normalized.leadingStage :
  ℝ → (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)
#check (DFP.Polar.Normalized.slope : (ℝ × ℝ × ℝ) → ℝ)
