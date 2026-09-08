module

public import ReasLib.Optimization.DFP.TwoPhaseControls.ObservableJet

public section

open Filter
open scoped Topology

/- Appendix Lemma A.12 (Gradient-norm expansions) (1): along a path with the
fixed shape jet, the initial normalized gradient norm is
`1 + 2 * ε ^ 4 + O(ε ^ 6)`. -/
#check (DFP.TwoLeg.NormJet.slowInitialGradientRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).initialGradientNorm -
        (1 + 2 * ε ^ 4)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6))

/- The intermediate normalized gradient norm along the same path is
`1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6 + O(ε ^ 7)`. -/
#check (DFP.TwoLeg.NormJet.slowIntermediateGradientRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).intermediateGradientNorm -
        (1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7))

/- When both coordinate paths have the fixed shape jets, the final normalized
gradient norm is
`1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 + O(ε ^ 7)`. -/
#check (DFP.TwoLeg.NormJet.slowFinalGradientRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).finalGradientNorm -
        (1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7))

/- The fixed common slow-curve neighborhood simultaneously controls all
observable-jet remainders. -/
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
