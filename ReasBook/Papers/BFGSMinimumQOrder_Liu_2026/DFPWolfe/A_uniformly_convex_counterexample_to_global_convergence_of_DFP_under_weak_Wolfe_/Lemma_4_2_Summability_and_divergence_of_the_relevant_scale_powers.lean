module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleSummability

public section

open Filter
open scoped Asymptotics Topology

export DFP.TwoLeg (slowCurveScaleFourthPowerSummable slowCurveScaleSquareNotSummable)

/- Lemma 4.2 (Summability and divergence of the relevant scale powers) (1):
the fourth powers of the singular scales along every sufficiently small positive
exact coordinate orbit on the invariant slow curve form a summable series. -/
#check (DFP.TwoLeg.slowCurveScaleFourthPowerSummable :
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
      let ε n := (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
      Summable (fun j : ℕ ↦ ε j ^ 4))

/- Lemma 4.2 (Summability and divergence of the relevant scale powers) (2):
the square powers of the singular scales along every sufficiently small positive
exact coordinate orbit on the invariant slow curve do not form a summable series. -/
#check (DFP.TwoLeg.slowCurveScaleSquareNotSummable :
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
      let ε n := (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
      ¬ Summable (fun j : ℕ ↦ ε j ^ 2))
