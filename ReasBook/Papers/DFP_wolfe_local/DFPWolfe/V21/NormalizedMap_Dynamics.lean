/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.Normalized.Dynamics

/- Compatibility surface for source-facing consumers of normalized polar dynamics. -/
#check (DFP.Polar.Normalized.leadingStage :
  ℝ → (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ)
#check (DFP.Polar.Normalized.slope : (ℝ × ℝ × ℝ) → ℝ)
