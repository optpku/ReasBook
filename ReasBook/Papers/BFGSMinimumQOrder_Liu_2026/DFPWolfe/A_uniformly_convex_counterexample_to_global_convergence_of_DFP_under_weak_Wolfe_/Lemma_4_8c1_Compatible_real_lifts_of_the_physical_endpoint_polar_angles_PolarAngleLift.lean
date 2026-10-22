/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_4_8c1_Compatible_real_lifts_of_the_physical_endpoint_polar_angles_PolarAngleLift.lean
-/

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
