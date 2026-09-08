module

public import ReasLib.Optimization.DFP.TwoPhaseControls.ObservableJet.Specialization

public section

noncomputable section

/- Appendix Proposition A.6g (Weighted observable-jet package): every coordinate
of the complete two-leg observable along the polynomial slow-graph path has the
displayed polynomial jet at its strongest certified order. -/
#check (DFP.TwoLeg.ObservableJet.slowGraphJets :
  ∀ i : Fin 13,
    FiniteTaylorJet.ofFunction ℝ (DFP.TwoLeg.ObservableJet.slowOrder i)
        (fun ε : ℝ ↦ DFP.TwoLeg.ObservableJet.coordinates
          (DFP.TwoLeg.observableMap (DFP.TwoLeg.slowGraphJetPath ε)) i) 0 =
      FiniteTaylorJet.ofFunction ℝ (DFP.TwoLeg.ObservableJet.slowOrder i)
        (fun ε : ℝ ↦ DFP.TwoLeg.ObservableJet.slowPolynomial ε i) 0)

#check (DFP.TwoLeg.ObservableJet.slowOrder_apply :
  ∀ i : Fin 13,
    DFP.TwoLeg.ObservableJet.slowOrder i =
      ![7, 6, 3, 5, 7, 8, 6, 6, 6, 6, 5, 6, 6] i)

#check (DFP.TwoLeg.ObservableJet.slowPolynomial_apply :
  ∀ (ε : ℝ) (i : Fin 13),
    DFP.TwoLeg.ObservableJet.slowPolynomial ε i =
      ![1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7,
        -3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6,
        2 * ε ^ 3,
        2 * ε ^ 5,
        -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7,
        -(508 / 5) * ε ^ 8,
        -2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6,
        -ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6,
        2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6,
        ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6,
        1 + 2 * ε ^ 4,
        1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6,
        1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6] i)

#check (DFP.TwoLeg.ObservableJet.observableJetsCommonDomain :
  ∀ (B : ℝ), 0 ≤ B →
    let f := fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
      DFP.TwoLeg.ObservableJet.coordinates (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε))
    let J := fun θ ↦ FiniteTaylorJet.ofFunction ℝ 9 (f θ) 0
    ∃ m > 0, ∀ C > 0, ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          (∀ i : Fin 18,
              m ≤ DFP.TwoLeg.ObservableJet.domainFactors θ ε i) ∧
            ‖(J θ).remainder (f θ) 0 ε‖ ≤ C * |ε| ^ 9)
