module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.SecondLegScaleExpansion
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.ScaleStationaryAssembly
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

private theorem eqModPow_congr_right {n : ℕ} {f g k : ℝ → ℝ}
    (h : EqModPow n f g) (hg : ∀ ε, k ε = g ε) : EqModPow n f k := by
  exact EqModPow.congr h (fun _ => rfl) hg

private theorem pureScale_path_analytic :
    AnalyticAt ℝ (fun ε : ℝ => ((ε, 2, 1) : ℝ × ℝ × ℝ)) 0 := by
  fun_prop

/-- The pure scale-axis fourth-order jet of the normalized two-leg radius factor. -/
theorem radiusFactor_pureScaleJet :
    FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => radiusFactor ε 2 1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ => 1 - (300 / 18) * ε ^ 3 + (54 / 18) * ε ^ 4) 0 := by
  rcases pureScale_factor_expansions with ⟨hradius, _, _⟩
  have hradius' :
      EqModPow 5 (fun ε : ℝ => radiusFactor ε 2 1)
        (fun ε => 1 - (300 / 18) * ε ^ 3 + (54 / 18) * ε ^ 4) := by
    apply eqModPow_congr_right hradius
    intro ε
    ring
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
  · have h := analyticAt_radiusFactor.comp
      (f := fun ε : ℝ => ((ε, 2, 1) : ℝ × ℝ × ℝ)) pureScale_path_analytic
    simpa [Function.comp_def] using (h.contDiffAt :
      ContDiffAt ℝ 4
        ((fun x : ℝ × ℝ × ℝ => radiusFactor x.1 x.2.1 x.2.2) ∘
          fun ε : ℝ => ((ε, 2, 1) : ℝ × ℝ × ℝ)) 0)
  · fun_prop
  · simpa only [zero_add, Nat.reduceAdd] using EqModPow.to_isBigO hradius'

/-- The pure scale-axis fourth-order jet of the recovered two-leg shape factor. -/
theorem stateMap_shape_pureScaleJet :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ => (stateMap (ε, 2, 1)).2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ => 2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4) 0 := by
  rcases pureScale_factor_expansions with ⟨_, hshape, _⟩
  have hshape' :
      EqModPow 5 (fun ε : ℝ => (stateMap (ε, 2, 1)).2.1)
        (fun ε => 2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4) := by
    apply eqModPow_congr_right hshape
    intro ε
    ring
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
  · have hstate := stateMapAnalytic.comp
      (f := fun ε : ℝ => ((ε, 2, 1) : ℝ × ℝ × ℝ)) pureScale_path_analytic
    have hshapeAnalytic := analyticAt_fst.comp (analyticAt_snd.comp hstate)
    simpa [Function.comp_def] using (hshapeAnalytic.contDiffAt :
      ContDiffAt ℝ 4
        (fun ε : ℝ => ((stateMap ∘
          fun t : ℝ => ((t, 2, 1) : ℝ × ℝ × ℝ)) ε).2.1) 0)
  · fun_prop
  · simpa only [zero_add, Nat.reduceAdd] using EqModPow.to_isBigO hshape'

/-- The pure scale-axis fourth-order jet of the recovered high eigenvalue factor. -/
theorem stateMap_high_pureScaleJet :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ => (stateMap (ε, 2, 1)).2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0 := by
  rcases pureScale_factor_expansions with ⟨_, _, hhigh⟩
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
  · have hstate := stateMapAnalytic.comp
      (f := fun ε : ℝ => ((ε, 2, 1) : ℝ × ℝ × ℝ)) pureScale_path_analytic
    have hhighAnalytic := analyticAt_snd.comp (analyticAt_snd.comp hstate)
    simpa [Function.comp_def] using (hhighAnalytic.contDiffAt :
      ContDiffAt ℝ 4
        (fun ε : ℝ => ((stateMap ∘
          fun t : ℝ => ((t, 2, 1) : ℝ × ℝ × ℝ)) ε).2.2) 0)
  · fun_prop
  · simpa only [zero_add, Nat.reduceAdd] using EqModPow.to_isBigO hhigh

/-- Full weighted radius jet, with every mixed Hessian discharged by scale stationarity. -/
theorem weightedNormalizedRadiusJet_via_scaleStationarity
    (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          radiusFactor ε
            (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
            (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
            ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0 :=
  weightedNormalizedRadiusJet_of_scale P₃ H₃ P₄ H₄ radiusFactor_pureScaleJet

/-- Full weighted shape jet, with every mixed Hessian discharged by scale stationarity. -/
theorem weightedTransversePJet_via_scaleStationarity
    (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
            ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) 0 :=
  weightedTransversePJet_of_scale P₃ H₃ P₄ H₄ stateMap_shape_pureScaleJet

/-- Full weighted high-factor jet, with every mixed Hessian discharged by scale stationarity. -/
theorem weightedTransverseHJet_via_scaleStationarity
    (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0 :=
  weightedTransverseHJet_of_scale P₃ H₃ P₄ H₄ stateMap_high_pureScaleJet

end DFP.TwoLeg
