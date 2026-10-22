/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_4_8c0_Quotient_valued_physical_endpoint_polar_angles_PolarAngle.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngle

public section

noncomputable section

open scoped EuclideanSpace

/- Definition 4.8c0 (Quotient-valued physical endpoint polar angles) (2):
the canonical quotient-valued oriented angle assigned to every endpoint displacement. -/
#check (DFP.TwoPhaseOrbit.endpointPolarAngle :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ), Real.Angle)

#check (DFP.TwoPhaseOrbit.endpointPolarAngle_def :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    orbit.endpointPolarAngle C k =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (orbit.endpoint k - C))

#check (DFP.TwoPhaseOrbit.endpointPolarAngle_even :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ),
    orbit.endpointPolarAngle C (2 * j) =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        ((orbit.state j).point - C))

#check (DFP.TwoPhaseOrbit.endpointPolarAngle_odd :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ),
    orbit.endpointPolarAngle C (2 * j + 1) =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        ((orbit.state j).middlePoint - C))

#check (DFP.TwoPhaseOrbit.endpointPolarAngle_spec :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    orbit.endpoint k - C ≠ 0 →
      orbit.endpoint k - C =
        ‖orbit.endpoint k - C‖ •
          EuclideanPlane.rotation (orbit.endpointPolarAngle C k)
            (EuclideanSpace.basisFun (Fin 2) ℝ 0))
