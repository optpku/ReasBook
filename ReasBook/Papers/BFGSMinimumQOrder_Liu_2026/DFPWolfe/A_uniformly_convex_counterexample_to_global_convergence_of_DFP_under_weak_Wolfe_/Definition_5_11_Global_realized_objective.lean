module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.RealizedObjective

/- Definition 5.11 (Global realized objective):
`DFP.TwoPhaseOrbit.realizedObjective orbit C G` is the function
`fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z`. -/
#check (DFP.TwoPhaseOrbit.realizedObjective :
  DFP.TwoPhaseOrbit → EuclideanSpace ℝ (Fin 2) → ℝ →
    EuclideanSpace ℝ (Fin 2) → ℝ)

#check (DFP.TwoPhaseOrbit.realizedObjective_apply :
  ∀ (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
      (z : EuclideanSpace ℝ (Fin 2)),
    orbit.realizedObjective C G z =
      (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z)
