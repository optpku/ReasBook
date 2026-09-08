module

public import ReasLib.Optimization.DFP.TwoPhaseControls.RadiusJet

public section

open Filter
open scoped Topology

/- Appendix Proposition A.5b (Weighted normalized-radius jet) (1): along a
polynomial graph with arbitrary cubic and quartic coefficients, the order-four
jet of `r̂₊ / ε ^ 2` has the displayed weighted coefficients. -/
#check (DFP.TwoLeg.weightedNormalizedRadiusJet :
  ∀ P₃ H₃ P₄ H₄ : ℝ,
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
          DFP.TwoLeg.radiusFactor x.1 x.2.1 x.2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
            ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0)

/- At the slow-graph coefficients, the normalized radius jet is
`1 - 3 * ε ^ 3 + (5 / 2) * ε ^ 4`. -/
#check (DFP.TwoLeg.slowGraphNormalizedRadiusJet :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := DFP.TwoLeg.slowGraphJetPath ε
          DFP.TwoLeg.radiusFactor x.1 x.2.1 x.2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦ 1 - 3 * ε ^ 3 + (5 / 2) * ε ^ 4) 0)

/- Appendix Proposition A.5b (Weighted normalized-radius jet) (2): an
`O(ε ^ 5)` perturbation of the polynomial slow graph yields the signed
recurrence `ε₊ = ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5 + O(ε ^ 6)`. -/
#check (DFP.TwoLeg.slowGraphSignedRecurrence :
  ∀ (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)),
    (fun ε : ℝ ↦
      DFP.TwoLeg.signedEpsilon ε (p ε) (h ε) -
        (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 6))
