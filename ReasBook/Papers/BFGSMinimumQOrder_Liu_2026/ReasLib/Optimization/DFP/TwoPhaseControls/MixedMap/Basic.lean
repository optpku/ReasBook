module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap

public section

/-!
# Basic interfaces for the mixed two-leg map

This companion records the definitional interfaces of the mixed parameter set, canonical
input, and removable base value.  It is separate from the pipeline-owned `MixedMap.lean`.
-/

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- Membership in the mixed parameter set is componentwise membership in its two factors. -/
theorem mem_parameterSet_iff (θ : ℝ × ℝ × ℝ) (β B : ℝ) :
    θ ∈ parameterSet β B ↔
      θ.1 ∈ Set.Icc (-β) β ∧ θ.2 ∈ Metric.closedBall (0 : ℝ × ℝ) B := by
  exact mem_parameterSet θ β B

/-- The canonical mixed input evaluates to its three explicit coordinates. -/
theorem input_eq (b P J r : ℝ) :
    input (b, P, J) r = (r, 2 + P * b * r, 1 + J * b * r) := by
  exact input_apply b P J r

/-- The removable mixed map sends zero radius to the canonical base state. -/
theorem map_base (b : ℝ) : map b (0, 2, 1) = (0, 2, 1) := by
  exact map_zero b

end DFP.TwoLeg.Mixed
