module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

noncomputable section

open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg.Mixed

/- The derivative calculations only use three scalar/vector projections of the complete
   observable record.  Keeping this package separate avoids repeatedly unfolding the
   thirteen-field evaluator in the mixed-radius proofs. -/

/-- The amplitude, relative-frame angle, and low full-center projections of a mixed cycle. -/
def independentPhysicalProjectionData (b : ℝ) (state : ℝ × ℝ × ℝ) :
    ℝ × ℝ × EuclideanSpace ℝ (Fin 2) :=
  observableMap_projectionData b state

/-- The projection evaluator is pointwise equal to the corresponding observable fields. -/
lemma independentPhysicalProjectionData_eq_target (b : ℝ) (state : ℝ × ℝ × ℝ) :
    independentPhysicalProjectionData b state =
      ((observableMap b state).amplitudeRatio,
        (observableMap b state).frameAngleIncrement,
        (observableMap b state).fullCenterDisplacement) := by
  -- Consume the owner projection theorem without unfolding the complete record here.
  exact observableMap_projectionData_eq_fields b state

end DFP.TwoLeg.Mixed
