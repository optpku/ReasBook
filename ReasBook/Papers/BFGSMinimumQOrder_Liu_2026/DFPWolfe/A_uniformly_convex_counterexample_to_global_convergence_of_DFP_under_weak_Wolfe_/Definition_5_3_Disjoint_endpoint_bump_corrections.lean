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
