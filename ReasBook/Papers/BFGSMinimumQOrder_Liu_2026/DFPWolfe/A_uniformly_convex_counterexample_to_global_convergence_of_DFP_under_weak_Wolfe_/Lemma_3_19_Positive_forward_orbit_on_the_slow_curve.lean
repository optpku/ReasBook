/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_19_Positive_forward_orbit_on_the_slow_curve.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity

public section

open Filter
open scoped Topology

/- Lemma 3.19 (Positive forward orbit on the slow curve) (1): fixed
fifth-order slow-graph jets make the signed next center coordinate positive and
strictly smaller than the current one at every sufficiently small positive
scale. -/
#check (DFP.TwoLeg.slowCurveNextPosLt :
  ∀ (p h : ℝ → ℝ),
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
      0 < DFP.TwoLeg.signedEpsilon ε (p ε) (h ε) ∧
        DFP.TwoLeg.signedEpsilon ε (p ε) (h ε) < ε)

/- Lemma 3.19 (Positive forward orbit on the slow curve) (2): eventual
invariance of the slow graph makes every forward iterate of a sufficiently
small positive point have positive center and graph coordinates. -/
#check (DFP.TwoLeg.slowCurveForwardOrbitPos :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      let xₙ := DFP.TwoLeg.stateMap^[n] (ε, p ε, h ε)
      0 < xₙ.1 ∧ 0 < xₙ.2.1 ∧ 0 < xₙ.2.2)
