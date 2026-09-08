module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.PowerTail

public section

open Filter
open scoped Asymptotics BigOperators Topology

/- Lemma 4.3 (Tail estimates for fourth and sixth powers) (1): the shifted
fourth-power tail along every sufficiently small positive exact slow-curve orbit
is asymptotic to `(2 / 3) * ε j`. -/
#check (DFP.TwoLeg.slowCurveFourthPowerTailIsEquivalent :
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
      (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ 4) ~[atTop]
        (fun j : ℕ ↦ (2 / 3 : ℝ) * ε j))

/- Lemma 4.3 (Tail estimates for fourth and sixth powers) (2): the shifted
sixth-power tail along every sufficiently small positive exact slow-curve orbit
is `O(ε j ^ 3)` at `atTop`. -/
#check (DFP.TwoLeg.slowCurveSixthPowerTailIsBigO :
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
      (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ 6) =O[atTop]
        (fun j : ℕ ↦ ε j ^ 3))
