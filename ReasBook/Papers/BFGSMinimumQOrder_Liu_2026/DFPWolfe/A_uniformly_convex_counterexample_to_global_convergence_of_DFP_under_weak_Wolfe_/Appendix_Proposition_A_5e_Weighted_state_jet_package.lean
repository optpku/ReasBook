/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_5e_Weighted_state_jet_package.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet

public section

/- Appendix Proposition A.5e (Weighted state-jet package) (1): for every
weighted graph coefficient tuple, the joint order-four state residual jet is
the zero `ℝ × ℝ × ℝ`-valued jet. -/
#check (DFP.TwoLeg.StateJet.weightedStateJet :
  ∀ θ : (ℝ × ℝ) × (ℝ × ℝ),
    FiniteTaylorJet.ofFunction ℝ 4 (DFP.TwoLeg.StateJet.remainder θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun _ : ℝ ↦ ((0, 0, 0) : ℝ × ℝ × ℝ)) 0)

/- Appendix Proposition A.5e (Weighted state-jet package) (2): one common
parameter neighborhood supplies the order-five remainder bound and positivity
of every domain factor. -/
#check (DFP.TwoLeg.StateJet.stateJetsCommonDomain :
  ∀ (B : ℝ), 0 ≤ B →
    ∃ C > 0, ∃ m > 0, ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          ‖DFP.TwoLeg.StateJet.remainder θ ε‖ ≤ C * |ε| ^ 5 ∧
            ∀ i : Fin 13, m ≤ DFP.TwoLeg.StateJet.domainFactors θ ε i)
