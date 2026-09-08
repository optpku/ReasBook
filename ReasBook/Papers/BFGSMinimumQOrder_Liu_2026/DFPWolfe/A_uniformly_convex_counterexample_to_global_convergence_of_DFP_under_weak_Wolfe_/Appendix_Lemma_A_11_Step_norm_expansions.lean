module

public import ReasLib.Optimization.DFP.TwoPhaseControls.NormJet
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Appendix_Proposition_A_6h_Common_domain_certificate_for_all_observable_jets

public section

open Filter
open scoped Topology

/- Appendix Lemma A.11 (Step-norm expansions): the two normalized step norms
have the displayed order-six expansions with order-seven remainders along any
path carrying the fixed slow-graph coordinate jets.  The observable jets also
share one uniform neighborhood on every bounded coefficient set. -/
#check (DFP.TwoLeg.NormJet.slowCurveFirstStepRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstStepNorm -
        (2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7))

#check (DFP.TwoLeg.NormJet.slowCurveSecondStepRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondStepNorm -
        (ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7))

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
