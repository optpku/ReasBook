module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_5_1_Isolation_radii_and_pairwise_disjoint_interpolation_balls_Isolation
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_5_2_Decay_of_the_endpoint_correction_vectors_Correction
public import DFPWolfe.Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample.Infrastructure_I_26_Derivative_formulas_and_scale_bounds_for_affine_cutoff_bumps_AffineBump
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump

#check (DFP.TwoPhaseOrbit.endpointBump :
  (orbit : DFP.TwoPhaseOrbit) → EuclideanSpace ℝ (Fin 2) → ℝ → ℕ →
    EuclideanSpace ℝ (Fin 2) → ℝ)

#check (DFP.TwoPhaseOrbit.endpointBump_eq_scaledLinearBump :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ),
    orbit.endpointBump C G k =
      AffineBump.scaledLinearBump EuclideanPlane.smoothCutoff (orbit.endpoint k)
        (orbit.interpolationRadius C G k) (orbit.endpointCorrection C k))

#check (DFP.TwoPhaseOrbit.endpointBump_apply :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ) (k : ℕ)
      (z : EuclideanSpace ℝ (Fin 2)),
    orbit.endpointBump C G k z =
      EuclideanPlane.smoothCutoff
          ((orbit.interpolationRadius C G k)⁻¹ • (z - orbit.endpoint k)) *
        inner ℝ (orbit.endpointCorrection C k) (z - orbit.endpoint k))

#check (DFP.TwoPhaseOrbit.bumpCorrection :
  (orbit : DFP.TwoPhaseOrbit) → EuclideanSpace ℝ (Fin 2) → ℝ →
    EuclideanSpace ℝ (Fin 2) → ℝ)

#check (DFP.TwoPhaseOrbit.bumpCorrection_apply :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
      (z : EuclideanSpace ℝ (Fin 2)),
    orbit.bumpCorrection C G z = ∑ᶠ k, orbit.endpointBump C G k z)

#check (DFP.TwoPhaseOrbit.bumpCorrection_eq_finsum_scaledLinearBump :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ),
    orbit.bumpCorrection C G = fun z ↦ ∑ᶠ k,
      AffineBump.scaledLinearBump EuclideanPlane.smoothCutoff (orbit.endpoint k)
        (orbit.interpolationRadius C G k) (orbit.endpointCorrection C k) z)
