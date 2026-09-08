module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics

public section

open Filter
open scoped Asymptotics Topology

export DFP.TwoLeg (slowCurveScaleAsymptotic)

/- Lemma 4.1 (Asymptotic decay of the singular scale): the scale along every
sufficiently small positive exact coordinate orbit on the invariant slow curve
is asymptotic to `((9 / 2) * j) ^ (-1 / 3)` at `atTop`. -/
#check (DFP.TwoLeg.slowCurveScaleAsymptotic :
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
      (fun j : ℕ ↦ (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) ~[atTop]
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)))
