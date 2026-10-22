/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump

public section

noncomputable section

namespace DFP.TwoPhaseOrbit

/-- The objective obtained by adding the translated squared norm to a two-phase orbit's
global bump correction. -/
noncomputable def realizedObjective (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z

/-- Evaluation of the realized objective at a point. -/
theorem realizedObjective_apply (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    orbit.realizedObjective C G z =
      (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z := by
  rw [realizedObjective]

end DFP.TwoPhaseOrbit
