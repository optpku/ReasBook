/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_4_8c0_Quotient_valued_physical_endpoint_polar_angles.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngle
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointNonzero

public section

noncomputable section

open Filter
open scoped Topology

/- Definition 4.8c0 (Quotient-valued physical endpoint polar angles) (1):
after one common restriction on the initial scale, every physical endpoint
differs from any stated limit of the corresponding center sequence. -/
#check (DFP.TwoPhaseOrbit.slowCurveEndpointSubCenterLimit_ne_zero :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, orbit.endpoint k - Clim ≠ 0)

/- Definition 4.8c0 (Quotient-valued physical endpoint polar angles) (2):
the canonical quotient-valued oriented angle assigned to every endpoint displacement. -/
#check (DFP.TwoPhaseOrbit.endpointPolarAngle :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ), Real.Angle)
