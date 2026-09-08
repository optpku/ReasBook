module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngle

open Filter
open scoped EuclideanSpace Topology

/- Lemma 3.19d (Recursive unwrapped frame angle represents the physical frame):
for sufficiently small initial scale on the invariant slow curve, the recursively
unwrapped angle rotates the initial physical low eigenvector to the low eigenvector
at every cycle boundary. -/
#check (DFP.TwoPhaseOrbit.slowCurveFrameAngleRepresentsLowVector :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) →
        (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 5) →
          ∀ (εbar : ℝ), εbar ∈ Set.Ioo 0 (1 / 4) →
            ∃ εmax ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 εmax, ∀ j : ℕ,
              let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
              (orbit.state j).lowVector =
                EuclideanPlane.rotation (orbit.frameAngle j) (orbit.state 0).lowVector)

/- The recursive frame-angle difference is the local analytic observable of the
current normalized two-leg state. -/
#check (DFP.TwoPhaseOrbit.frameAngleIncrement_eq_observable :
  ∀ (orbit : DFP.TwoPhaseOrbit) (j : ℕ),
    orbit.frameAngle (j + 1) - orbit.frameAngle j =
      (DFP.TwoLeg.observableMap (orbit.state j).coordinates).frameAngleIncrement)

/- On every sufficiently small invariant slow-curve orbit, each recursive difference
is the unique angle in `(-(π / 2), π / 2)` representing the relative frame. -/
#check (DFP.TwoPhaseOrbit.slowCurveFrameAngleIncrementUnique :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) →
        (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 5) →
          ∀ (εbar : ℝ), εbar ∈ Set.Ioo 0 (1 / 4) →
            ∃ εmax ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 εmax, ∀ j : ℕ,
              let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
              let δ := orbit.frameAngle (j + 1) - orbit.frameAngle j
              δ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
                ∀ θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
                  EuclideanPlane.rotationMatrix θ = (orbit.state j).relativeFrame ↔
                    θ = δ)
