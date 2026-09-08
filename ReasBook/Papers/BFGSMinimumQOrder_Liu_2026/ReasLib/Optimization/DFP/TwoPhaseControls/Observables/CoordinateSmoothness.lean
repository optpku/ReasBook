module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.EndpointAngleSmoothness
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.EndpointAngleSmoothness

/-!
# Joint smoothness of the complete scalar observable vector
-/

public section

noncomputable section

open scoped EuclideanSpace Nat ContDiff

namespace DFP.TwoLeg

/-- The explicitly ordered vector of all thirteen real observable coordinates is smooth to every
order at the common canceled base state. -/
theorem observableCoordinateVector_contDiffAt (k : ℕ∞ω) : ContDiffAt ℝ k
    (fun x : ℝ × ℝ × ℝ ↦
      let observable := observableMap x
      ![observable.amplitudeRatio, observable.frameAngleIncrement,
        observable.halfCenterDisplacement 0, observable.halfCenterDisplacement 1,
        observable.fullCenterDisplacement 0, observable.fullCenterDisplacement 1,
        observable.firstEndpointAngleIncrement.toReal,
        observable.secondEndpointAngleIncrement.toReal,
        observable.firstStepNorm, observable.secondStepNorm,
        observable.initialGradientNorm, observable.intermediateGradientNorm,
        observable.finalGradientNorm]) (0, 2, 1) := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · simpa using amplitudeRatio_contDiffAt k
  · simpa using frameAngleIncrement_contDiffAt k
  · simpa using CenterCancellation.halfCenterDisplacement_contDiffAt k 0
  · simpa using CenterCancellation.halfCenterDisplacement_contDiffAt k 1
  · simpa using CenterCancellation.fullCenterDisplacement_contDiffAt k 0
  · simpa using CenterCancellation.fullCenterDisplacement_contDiffAt k 1
  · simpa using firstEndpointAngleIncrement_toReal_contDiffAt k
  · simpa using secondEndpointAngleIncrement_toReal_contDiffAt k
  · simpa using CenterCancellation.firstStepNorm_contDiffAt k
  · simpa using CenterCancellation.secondStepNorm_contDiffAt k
  · simpa using initialGradientNorm_contDiffAt k
  · simpa using intermediateGradientNorm_contDiffAt k
  · simpa using finalGradientNorm_contDiffAt k

end DFP.TwoLeg
