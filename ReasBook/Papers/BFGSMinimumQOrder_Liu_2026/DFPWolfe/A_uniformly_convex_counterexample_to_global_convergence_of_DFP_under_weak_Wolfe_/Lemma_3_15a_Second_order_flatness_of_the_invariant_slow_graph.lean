module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Flatness

public section

open Filter
open scoped Topology

/- Lemma 3.15a (Second-order flatness of the invariant slow graph)
For an invariant graph through `(2, 1)` tangent to the signed-scale axis, the
first and second derivatives of both transverse coordinates vanish at `0`.
-/
#check (DFP.TwoLeg.invariantSlowGraphSecondOrderFlatness :
  ∀ (p h : ℝ → ℝ),
    ContDiffAt ℝ 2 (fun ε ↦ (p ε, h ε)) 0 →
      (p 0, h 0) = (2, 1) →
        HasFDerivAt (fun ε ↦ (p ε, h ε))
          (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 →
          (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
            (fun ε ↦
              let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
              (ε', p ε', h ε')) →
            iteratedDeriv 1 p 0 = 0 ∧
              iteratedDeriv 1 h 0 = 0 ∧
                iteratedDeriv 2 p 0 = 0 ∧
                  iteratedDeriv 2 h 0 = 0)
