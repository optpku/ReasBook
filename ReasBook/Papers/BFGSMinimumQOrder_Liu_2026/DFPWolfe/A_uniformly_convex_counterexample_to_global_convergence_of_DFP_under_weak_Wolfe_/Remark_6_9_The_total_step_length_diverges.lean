module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepLength

public section

open Filter
open scoped Asymptotics Topology

/- Remark 6.9 (The total step length diverges) (1): along every sufficiently
small canonical slow-curve orbit, the first normalized physical displacement
has remainder `o(ε_j ^ 2)` after subtracting `2 * ε_j ^ 2`. -/
#check (DFP.TwoPhaseOrbit.slowCurveFirstStepNormRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      (fun j : ℕ ↦
        ‖(orbit.state j).firstDisplacement‖ / (orbit.state j).amplitude -
          2 * (orbit.state j).ε ^ 2) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2))

/- Remark 6.9 (The total step length diverges) (2): along every sufficiently
small canonical slow-curve orbit, the second normalized physical displacement
has remainder `o(ε_j ^ 2)` after subtracting `ε_j ^ 2`. -/
#check (DFP.TwoPhaseOrbit.slowCurveSecondStepNormRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      (fun j : ℕ ↦
        ‖(orbit.state j).secondDisplacement‖ / (orbit.state j).amplitude -
          (orbit.state j).ε ^ 2) =o[atTop]
        (fun j : ℕ ↦ (orbit.state j).ε ^ 2))

/- Remark 6.9 (The total step length diverges) (3): along every sufficiently
small canonical slow-curve orbit, the series of the two physical displacement
norms in each cycle is not summable. -/
#check (DFP.TwoPhaseOrbit.slowCurveTotalStepLengthNotSummable :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ¬ Summable (fun j : ℕ ↦
        ‖(orbit.state j).firstDisplacement‖ +
          ‖(orbit.state j).secondDisplacement‖))
