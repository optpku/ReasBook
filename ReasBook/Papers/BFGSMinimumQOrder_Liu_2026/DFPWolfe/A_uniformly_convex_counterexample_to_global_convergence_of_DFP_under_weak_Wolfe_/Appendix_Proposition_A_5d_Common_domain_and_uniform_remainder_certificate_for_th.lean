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
