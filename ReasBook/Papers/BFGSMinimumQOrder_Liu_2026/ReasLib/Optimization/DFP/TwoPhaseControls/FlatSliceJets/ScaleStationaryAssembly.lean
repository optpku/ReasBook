module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.BasisHessianAssembly
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.ScaleStationarity

public section

noncomputable section

namespace DFP.TwoLeg

/-- Assemble the normalized-radius jet once its pure scale-axis jet is known.
The mixed scale/transverse Hessian conditions are discharged by scale stationarity. -/
theorem weightedNormalizedRadiusJet_of_scale
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => radiusFactor ε 2 1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 1 - (300 / 18) * ε ^ 3 + (54 / 18) * ε ^ 4) 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          radiusFactor ε
            (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
            (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
            ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0 :=
  weightedNormalizedRadiusJet_of_scale_and_basis_cross
    P₃ H₃ P₄ H₄ hscale radiusFactor_scale_shape_cross_eq_zero
      radiusFactor_scale_high_cross_eq_zero

/-- Assemble the recovered-shape jet once its pure scale-axis jet is known. -/
theorem weightedTransversePJet_of_scale
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => (stateMap (ε, 2, 1)).2.1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4) 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
            ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) 0 :=
  weightedTransversePJet_of_scale_and_basis_cross
    P₃ H₃ P₄ H₄ hscale stateMap_shape_scale_shape_cross_eq_zero
      stateMap_shape_scale_high_cross_eq_zero

/-- Assemble the recovered-high jet once its pure scale-axis jet is known. -/
theorem weightedTransverseHJet_of_scale
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => (stateMap (ε, 2, 1)).2.2) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0 :=
  weightedTransverseHJet_of_scale_and_basis_cross
    P₃ H₃ P₄ H₄ hscale stateMap_high_scale_shape_cross_eq_zero
      stateMap_high_scale_high_cross_eq_zero

end DFP.TwoLeg
