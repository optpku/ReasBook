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
