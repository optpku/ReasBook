/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_6f_Weighted_step_and_gradient_norm_jets.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.NormJet

public section

noncomputable section

/- Appendix Proposition A.6f (Weighted step- and gradient-norm jets): along the polynomial
slow-graph path, the first normalized step norm has the displayed order-six jet. -/
#check (DFP.TwoLeg.NormJet.slowFirstStep :
    FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).firstStepNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          2 * ε ^ 2 + (112 / 5) * ε ^ 5 - (11 / 5) * ε ^ 6) 0)

-- The second normalized step norm has the displayed order-six jet.
#check (DFP.TwoLeg.NormJet.slowSecondStep :
    FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).secondStepNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          ε ^ 2 + (114 / 5) * ε ^ 5 - (49 / 10) * ε ^ 6) 0)

-- The initial normalized gradient norm has the displayed order-five jet.
#check (DFP.TwoLeg.NormJet.slowInitialGradient :
    FiniteTaylorJet.ofFunction ℝ 5
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).initialGradientNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 5
        (fun ε : ℝ ↦ 1 + 2 * ε ^ 4) 0)

-- The intermediate normalized gradient norm has the displayed order-six jet.
#check (DFP.TwoLeg.NormJet.slowIntermediateGradient :
    FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).intermediateGradientNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          1 - 2 * ε ^ 3 - 2 * ε ^ 4 - (112 / 5) * ε ^ 6) 0)

-- The final normalized gradient norm has the displayed order-six jet.
#check (DFP.TwoLeg.NormJet.slowFinalGradient :
    FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).finalGradientNorm) 0 =
      FiniteTaylorJet.ofFunction ℝ 6
        (fun ε : ℝ ↦
          1 - (9 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6) 0)

-- The five norm projections have a common order-seven uniform finite-jet family.
#check (DFP.TwoLeg.NormJet.uniformOn :
  ∀ B : ℝ,
    let norms := fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
      let observable := DFP.TwoLeg.observableMap
        (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε)
      (observable.firstStepNorm, observable.secondStepNorm,
        observable.initialGradientNorm, observable.intermediateGradientNorm,
        observable.finalGradientNorm)
    FiniteTaylorJet.IsUniformOn norms
      (fun θ ↦ FiniteTaylorJet.ofFunction ℝ 7 (norms θ) 0) 0
      (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B))
