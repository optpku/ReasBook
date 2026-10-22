/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_5_3_Disjoint_endpoint_bump_corrections.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump

#check (EuclideanPlane.smoothCutoff : EuclideanSpace ℝ (Fin 2) → ℝ)

/- Definition 5.3 (Disjoint endpoint bump corrections):
`EuclideanPlane.smoothCutoff` is the fixed planar plateau cutoff,
`DFP.TwoPhaseOrbit.endpointBump` is the correction `ψₖ` at endpoint `k`, and
`DFP.TwoPhaseOrbit.bumpCorrection` is their pointwise finsum `Ψ`. -/
#check (DFP.TwoPhaseOrbit.endpointBump :
  (orbit : DFP.TwoPhaseOrbit) → EuclideanSpace ℝ (Fin 2) → ℝ → ℕ →
    EuclideanSpace ℝ (Fin 2) → ℝ)

#check (DFP.TwoPhaseOrbit.bumpCorrection :
  (orbit : DFP.TwoPhaseOrbit) → EuclideanSpace ℝ (Fin 2) → ℝ →
    EuclideanSpace ℝ (Fin 2) → ℝ)
