module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement

public section

open scoped Matrix

#check (DFP.TwoPhaseOrbit.State.middleCenter :
  DFP.TwoPhaseOrbit.State → EuclideanSpace ℝ (Fin 2))

#check (DFP.TwoPhaseOrbit.State.middleCenter_def :
  ∀ s : DFP.TwoPhaseOrbit.State,
    s.middleCenter = s.middlePoint - s.middleGradient)

#check (DFP.TwoPhaseOrbit.State.halfCenterDisplacement :
  DFP.TwoPhaseOrbit.State → EuclideanSpace ℝ (Fin 2))

#check (DFP.TwoPhaseOrbit.State.halfCenterDisplacement_def :
  ∀ s : DFP.TwoPhaseOrbit.State,
    s.halfCenterDisplacement = s.middleCenter - s.center)

#check (DFP.TwoPhaseOrbit.State.halfCenterDisplacement_observable :
  ∀ s : DFP.TwoPhaseOrbit.State,
    s.halfCenterDisplacement = s.amplitude • WithLp.toLp 2
      (s.frame *ᵥ (DFP.TwoLeg.observableMap s.coordinates).halfCenterDisplacement))

#check (DFP.TwoPhaseOrbit.State.norm_halfCenterDisplacement :
  ∀ s : DFP.TwoPhaseOrbit.State, DFP.TwoPhaseOrbit.State.PhaseValidity s →
    ‖s.halfCenterDisplacement‖ =
      s.amplitude * ‖(DFP.TwoLeg.observableMap s.coordinates).halfCenterDisplacement‖)
