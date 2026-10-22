/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_23_Half_cycle_center_displacement_Center.lean
-/

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
