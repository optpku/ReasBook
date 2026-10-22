/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Remark_6_8_Gradient_norms_are_not_eventually_monotone.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.NormJet.Monotonicity

public section

open Filter
open scoped Asymptotics Topology

#check (DFP.TwoLeg.NormJet.firstLegGradientNormDrop :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) ~[𝓝[>] 0]
      (fun ε : ℝ ↦ 2 * ε ^ 3))

#check (DFP.TwoLeg.NormJet.secondLegGradientNormRise :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5) →
    (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0] (fun ε ↦ ε ^ 5) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm) ~[𝓝[>] 0]
      (fun ε : ℝ ↦ 2 * ε ^ 3))

/- Remark 6.8 (Gradient norms are not eventually monotone): every sufficiently small
positive point has a strict gradient-norm valley, preserved by multiplication by any
positive cycle amplitude. -/
#check (DFP.TwoLeg.NormJet.eventuallyStrictGradientNormValley :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5) →
    (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0] (fun ε ↦ ε ^ 5) →
    ∀ᶠ ε in 𝓝[>] 0, ∀ G : ℝ, 0 < G →
      G * (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm <
          G * (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm ∧
        G * (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm <
          G * (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm)
