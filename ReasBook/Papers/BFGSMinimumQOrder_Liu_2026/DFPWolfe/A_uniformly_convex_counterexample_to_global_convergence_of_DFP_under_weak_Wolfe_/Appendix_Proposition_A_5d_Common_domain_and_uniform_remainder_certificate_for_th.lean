/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_5d_Common_domain_and_uniform_remainder_certificate_for_th.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet

public section

/- Appendix Proposition A.5d (Common-domain and uniform-remainder certificate for the state jets):
on every bounded coefficient ball, one radius simultaneously controls all three
order-five residuals and keeps every factored divisor uniformly positive. -/
#check (DFP.TwoLeg.StateJet.stateJetsCommonDomain :
  ∀ (B : ℝ), 0 ≤ B →
    ∃ C > 0, ∃ m > 0, ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          ‖DFP.TwoLeg.StateJet.remainder θ ε‖ ≤ C * |ε| ^ 5 ∧
            ∀ i : Fin 13, m ≤ DFP.TwoLeg.StateJet.domainFactors θ ε i)
