module

public import ReasLib.Optimization.DFP.TwoPhaseControls.TransverseJet

public section

/- Appendix Proposition A.5c (Weighted transverse-shape jet) (1): the order-four
jet of the updated shape coordinate along an arbitrary polynomial graph path. -/
#check
  (DFP.TwoLeg.weightedTransversePJet :
    ∀ (P₃ H₃ P₄ H₄ : ℝ),
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
            (DFP.TwoLeg.stateMap x).2.1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
              ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) 0)

/- Appendix Proposition A.5c (Weighted transverse-shape jet) (2): the order-four
jet of the updated high-eigenvalue coordinate along an arbitrary polynomial graph path. -/
#check
  (DFP.TwoLeg.weightedTransverseHJet :
    ∀ (P₃ H₃ P₄ H₄ : ℝ),
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
            (DFP.TwoLeg.stateMap x).2.2) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦ 1 + 8 * ε ^ 3) 0)

/- Appendix Proposition A.5c (Weighted transverse-shape jet) (3): the order-four
shape-coordinate invariance defect has the two displayed transverse coefficients. -/
#check
  (DFP.TwoLeg.weightedTransversePDefectJet :
    ∀ (P₃ H₃ P₄ H₄ : ℝ),
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
            let y := DFP.TwoLeg.stateMap x
            let nextGraph := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ y.1
            y.2.1 - nextGraph.2.1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3 +
              ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) 0)

/- Appendix Proposition A.5c (Weighted transverse-shape jet) (4): the order-four
high-coordinate invariance defect has the two displayed transverse coefficients. -/
#check
  (DFP.TwoLeg.weightedTransverseHDefectJet :
    ∀ (P₃ H₃ P₄ H₄ : ℝ),
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
            let y := DFP.TwoLeg.stateMap x
            let nextGraph := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ y.1
            y.2.2 - nextGraph.2.2) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3 - H₄ * ε ^ 4) 0)

/- Appendix Proposition A.5c (Weighted transverse-shape jet) (5): on every
closed ball of graph coefficients, both exact invariance defects have one joint
uniform remainder of order five after subtracting their displayed jets. -/
#check
  (DFP.TwoLeg.weightedTransverseRemainder :
    ∀ (B : ℝ), 0 ≤ B →
      ∃ C > 0,
        Asymptotics.IsUniformRemainderOn
          (fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
            let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
            let y := DFP.TwoLeg.stateMap x
            let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
            (y.2.1 - nextGraph.2.1 -
                (((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
                  ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4),
              y.2.2 - nextGraph.2.2 -
                ((8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4)))
          (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) C 5)
