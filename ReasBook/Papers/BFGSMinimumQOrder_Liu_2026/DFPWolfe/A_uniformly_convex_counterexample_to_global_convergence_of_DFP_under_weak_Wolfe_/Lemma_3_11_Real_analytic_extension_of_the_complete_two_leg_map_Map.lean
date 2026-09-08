module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

noncomputable section

namespace DFP.TwoLeg

/-- The complete two-leg coordinate map after removing the singular powers of `ε`. -/
abbrev extendedMap : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ) :=
  stateMap

/-- The analytically extended complete map fixes the factored base point. -/
theorem extendedMap_base :
    extendedMap ((0, 2, 1) : ℝ × ℝ × ℝ) = (0, 2, 1) :=
  stateMap_base

end DFP.TwoLeg
