module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngle

open scoped EuclideanSpace Matrix

/- Lemma 3.19d (Recursive unwrapped frame angle represents the physical frame):
the recursively accumulated angle represents the physical low vector of any orbit
whose relative frames remain in the signed-angle chart. -/
#check (DFP.TwoPhaseOrbit.frameAngleRepresentsLowVector :
  ∀ (orbit : DFP.TwoPhaseOrbit),
    (orbit.state 0).frame = 1 →
      (∀ j, (orbit.state j).relativeFrame ∈
        Matrix.specialOrthogonalGroup (Fin 2) ℝ) →
        (∀ j, (orbit.state j).relativeFrame ∈
          EuclideanPlane.SignedAngle.chart) →
          ∀ j : ℕ, (orbit.state j).lowVector =
            EuclideanPlane.rotation (orbit.frameAngle j) (orbit.state 0).lowVector)

#check (DFP.TwoPhaseOrbit.State.lowVector :
  DFP.TwoPhaseOrbit.State → EuclideanSpace ℝ (Fin 2))

#check (DFP.TwoPhaseOrbit.State.lowVector_apply :
  ∀ (s : DFP.TwoPhaseOrbit.State) (i : Fin 2),
    s.lowVector i = s.frame i 0)

#check (DFP.TwoPhaseOrbit.State.relativeFrame :
  DFP.TwoPhaseOrbit.State → Matrix (Fin 2) (Fin 2) ℝ)

#check (DFP.TwoPhaseOrbit.State.next_frame_eq_frame_mul_relativeFrame :
  ∀ s : DFP.TwoPhaseOrbit.State, s.next.frame = s.frame * s.relativeFrame)

#check (DFP.TwoPhaseOrbit.State.angleIncrement : DFP.TwoPhaseOrbit.State → ℝ)

#check (DFP.TwoPhaseOrbit.State.angleIncrement_mem_interval :
  ∀ s : DFP.TwoPhaseOrbit.State,
    s.angleIncrement ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))

#check (DFP.TwoPhaseOrbit.State.angleIncrement_unique :
  ∀ (s : DFP.TwoPhaseOrbit.State),
    s.relativeFrame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ →
      s.relativeFrame ∈ EuclideanPlane.SignedAngle.chart →
        ∀ (θ : ℝ), θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) →
          (EuclideanPlane.rotationMatrix θ = s.relativeFrame ↔ θ = s.angleIncrement))

#check (DFP.TwoPhaseOrbit.frameAngle : DFP.TwoPhaseOrbit → ℕ → ℝ)

#check (DFP.TwoPhaseOrbit.frameAngle_zero :
  ∀ orbit : DFP.TwoPhaseOrbit, orbit.frameAngle 0 = 0)

#check (DFP.TwoPhaseOrbit.frameAngle_succ :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.frameAngle (j + 1) =
      orbit.frameAngle j + (orbit.state j).angleIncrement)
