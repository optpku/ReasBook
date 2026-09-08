module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngleLift

public section

open scoped EuclideanSpace

namespace DFP.TwoPhaseOrbit

/- Lemma 4.8c1 (Compatible real lifts of the physical endpoint polar angles) -/
#check (DFP.TwoPhaseOrbit.endpointPolarAngleLift :
  DFP.TwoPhaseOrbit → EuclideanSpace ℝ (Fin 2) → ℕ → ℝ)

#check (DFP.TwoPhaseOrbit.endpointPolarAngleLift_zero :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)),
    orbit.endpointPolarAngleLift C 0 = (orbit.endpointPolarAngle C 0).toReal)

#check (DFP.TwoPhaseOrbit.endpointPolarAngleLift_succ :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    orbit.endpointPolarAngleLift C (k + 1) = orbit.endpointPolarAngleLift C k +
      (orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k).toReal)

#check (DFP.TwoPhaseOrbit.endpointPolarAngleLift_succ_sub :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    orbit.endpointPolarAngleLift C (k + 1) - orbit.endpointPolarAngleLift C k =
      (orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k).toReal)

#check (DFP.TwoPhaseOrbit.endpointPolarAngleLift_coe :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    (orbit.endpointPolarAngleLift C k : Real.Angle) = orbit.endpointPolarAngle C k)

#check (DFP.TwoPhaseOrbit.endpointPolarAngleLift_succ_sub_unique :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    ∀ (δ : ℝ), δ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) →
      ((δ : Real.Angle) =
          orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k ↔
        δ = orbit.endpointPolarAngleLift C (k + 1) - orbit.endpointPolarAngleLift C k))

end DFP.TwoPhaseOrbit
