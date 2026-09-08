module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.PowerTail

public section

open Filter
open scoped BigOperators Topology

/- Lemma 4.3b (Uniform first-order fourth-power tail asymptotic): uniformly over
all sufficiently small positive slow-curve orbits, the fourth-power tail differs
from `(2 / 3) * ε j` by a relative error whose modulus tends to zero. -/
#check (DFP.TwoLeg.slowCurveFourthPowerTailAsymptotic :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∃ ω₄ : ℝ → ℝ,
      ((∀ η ∈ Set.Ioc 0 εbar, 0 ≤ ω₄ η) ∧
          MonotoneOn ω₄ (Set.Ioc 0 εbar) ∧ Tendsto ω₄ (𝓝[>] 0) (𝓝 0)) ∧
        ∀ η ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 η,
          let ε n := (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
          ∀ j : ℕ,
            |(∑' k : ℕ, ε (j + k) ^ 4) - (2 / 3) * ε j| ≤ ω₄ η * ε j)
