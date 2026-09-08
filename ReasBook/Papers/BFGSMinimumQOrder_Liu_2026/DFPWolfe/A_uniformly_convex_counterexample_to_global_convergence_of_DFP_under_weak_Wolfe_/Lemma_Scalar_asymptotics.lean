module

import ReasLib.Optimization.DFP.TwoPhaseOrbit.ScalarAsymptotics

public section

open Filter
open scoped Asymptotics Topology

/- Lemma (Scalar asymptotics) -/
#check (DFP.TwoPhaseOrbit.slowCurveScalarAsymptotics :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∃ Glim > 0, ∃ Clim : EuclideanSpace ℝ (Fin 2),
        (fun j : ℕ ↦ (orbit.state j).ε) ~[atTop]
          (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) ∧
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
        (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
          (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε) ∧
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) ∧
        (fun j : ℕ ↦ ‖(orbit.state j).center - Clim‖) =O[atTop]
          (fun j : ℕ ↦ (orbit.state j).ε ^ 3) ∧
        (fun j : ℕ ↦ ‖(orbit.state j).middleCenter - Clim‖) =O[atTop]
          (fun j : ℕ ↦ (orbit.state j).ε ^ 3) ∧
        Tendsto orbit.frameAngle atTop atBot ∧
        {x : EuclideanSpace ℝ (Fin 2) | MapClusterPt x atTop orbit.endpoint} =
          DFP.TwoPhaseOrbit.limitCircle Clim Glim)

#check (DFP.TwoPhaseOrbit.mem_limitCircle :
  ∀ {C x : EuclideanSpace ℝ (Fin 2)} {G : ℝ},
    x ∈ DFP.TwoPhaseOrbit.limitCircle C G ↔
      ∃ v, ‖v‖ = 1 ∧ C + G • v = x)
