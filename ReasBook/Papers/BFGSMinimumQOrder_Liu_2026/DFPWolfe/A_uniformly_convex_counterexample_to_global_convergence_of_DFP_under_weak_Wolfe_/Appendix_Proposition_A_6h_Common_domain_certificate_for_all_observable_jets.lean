/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_6h_Common_domain_certificate_for_all_observable_jets.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.ObservableJet

public section

noncomputable section

export DFP.TwoLeg.ObservableJet (observableJetsCommonDomain)

/- Appendix Proposition A.6h (Common-domain certificate for all observable jets):
on every bounded slow-graph coefficient set, one radius simultaneously keeps
all factored and branch conditions uniformly positive and controls the common
order-nine remainder of all thirteen observable coordinates. -/
#check (DFP.TwoLeg.ObservableJet.observableJetsCommonDomain :
  ∀ (B : ℝ), 0 ≤ B →
    let f := fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
      DFP.TwoLeg.ObservableJet.coordinates (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε))
    let J := fun θ ↦ FiniteTaylorJet.ofFunction ℝ 9 (f θ) 0
    ∃ m > 0, ∀ C > 0, ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          (∀ i : Fin 18, m ≤ DFP.TwoLeg.ObservableJet.domainFactors θ ε i) ∧
            ‖(J θ).remainder (f θ) 0 ε‖ ≤ C * |ε| ^ 9)
