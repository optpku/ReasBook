/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Data.Real.Basic

@[expose] public section

namespace ConsensusADMM

/-- The critical multiplier step size for the period-48 consensus ADMM counterexamples. -/
noncomputable def criticalFactor : ℝ :=
  542407991247 / 287451196000

/-- The critical multiplier factor equals its defining rational quotient. -/
theorem criticalFactor_eq :
    criticalFactor = 542407991247 / 287451196000 := by
  -- Unfold the named threshold to its defining rational quotient.
  rfl

/-- The critical multiplier factor is positive. -/
theorem criticalFactor_pos : 0 < criticalFactor := by
  -- Rewrite to the explicit quotient, whose numerator and denominator are positive.
  rw [criticalFactor_eq]
  norm_num

end ConsensusADMM
