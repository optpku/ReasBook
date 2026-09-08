module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJetAssembly
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.WeightedDefectJets
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateJetAssembly
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet

public section

noncomputable section

namespace DFP.TwoLeg.StateJetAssembly

private def radiusActual (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
  DFP.TwoLeg.radiusFactor x.1 x.2.1 x.2.2

private def radiusPolynomial (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  1 + ((6 * θ.1.2 + 5 * θ.1.1 - 300) / 18) * ε ^ 3 +
    ((6 * θ.2.2 + 5 * θ.2.1 + 54) / 18) * ε ^ 4

private def shapeActual (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
  let y := DFP.TwoLeg.stateMap x
  let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
  y.2.1 - nextGraph.2.1

private def shapePolynomial (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  ((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
    ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4

private def highActual (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
  let y := DFP.TwoLeg.stateMap x
  let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
  y.2.2 - nextGraph.2.2

private def highPolynomial (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  (8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4

private theorem radiusResidual_eq (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    radiusResidual θ = fun ε => radiusActual θ ε - radiusPolynomial θ ε := by
  rfl

private theorem shapeResidual_eq (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    shapeResidual θ = fun ε => shapeActual θ ε - shapePolynomial θ ε := by
  rfl

private theorem scaleResidual_eq (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    scaleResidual θ = fun ε => highActual θ ε - highPolynomial θ ε := by
  rfl

private theorem radiusActual_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4 (radiusActual θ) 0 := by
  have hpoly : ContDiffAt ℝ 4 (radiusPolynomial θ) 0 := by
    unfold radiusPolynomial
    fun_prop
  have heq : radiusActual θ =
      fun ε => radiusResidual θ ε + radiusPolynomial θ ε := by
    funext ε
    rw [radiusResidual_eq]
    ring
  rw [heq]
  exact (radiusResidual_contDiffAt θ).add hpoly

private theorem shapeActual_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4 (shapeActual θ) 0 := by
  have hpoly : ContDiffAt ℝ 4 (shapePolynomial θ) 0 := by
    unfold shapePolynomial
    fun_prop
  have heq : shapeActual θ =
      fun ε => shapeResidual θ ε + shapePolynomial θ ε := by
    funext ε
    rw [shapeResidual_eq]
    ring
  rw [heq]
  exact (shapeResidual_contDiffAt θ).add hpoly

private theorem highActual_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4 (highActual θ) 0 := by
  have hpoly : ContDiffAt ℝ 4 (highPolynomial θ) 0 := by
    unfold highPolynomial
    fun_prop
  have heq : highActual θ =
      fun ε => scaleResidual θ ε + highPolynomial θ ε := by
    funext ε
    rw [scaleResidual_eq]
    ring
  rw [heq]
  exact (scaleResidual_contDiffAt θ).add hpoly

/-- The new weighted radius theorem makes the radius residual's four-jet zero. -/
theorem radiusResidual_zeroJet_via_scaleStationarity
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (radiusResidual θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0 := by
  have hpoly : ContDiffAt ℝ 4 (radiusPolynomial θ) 0 := by
    unfold radiusPolynomial
    fun_prop
  have hjet :
      FiniteTaylorJet.ofFunction ℝ 4 (radiusActual θ) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (radiusPolynomial θ) 0 := by
    change FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          DFP.TwoLeg.radiusFactor ε
            (2 + θ.1.1 * ε ^ 3 + θ.2.1 * ε ^ 4)
            (1 + θ.1.2 * ε ^ 3 + θ.2.2 * ε ^ 4)) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          1 + ((6 * θ.1.2 + 5 * θ.1.1 - 300) / 18) * ε ^ 3 +
            ((6 * θ.2.2 + 5 * θ.2.1 + 54) / 18) * ε ^ 4) 0
    exact DFP.TwoLeg.weightedNormalizedRadiusJet_via_scaleStationarity
      θ.1.1 θ.1.2 θ.2.1 θ.2.2
  rw [radiusResidual_eq]
  exact FiniteTaylorJet.ofFunction_sub_eq_zero_of_eq
    (radiusActual_contDiffAt θ) hpoly hjet

/-- The new shape-defect theorem makes the shape residual's four-jet zero. -/
theorem shapeResidual_zeroJet_via_scaleStationarity
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (shapeResidual θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0 := by
  have hpoly : ContDiffAt ℝ 4 (shapePolynomial θ) 0 := by
    unfold shapePolynomial
    fun_prop
  have hjet :
      FiniteTaylorJet.ofFunction ℝ 4 (shapeActual θ) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (shapePolynomial θ) 0 := by
    change FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          let x := DFP.TwoLeg.graphJetPath
            θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
          let y := DFP.TwoLeg.stateMap x
          let nextGraph := DFP.TwoLeg.graphJetPath
            θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
          y.2.1 - nextGraph.2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          ((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
            ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4) 0
    exact DFP.TwoLeg.weightedTransversePDefectJet_via_scaleStationarity
      θ.1.1 θ.1.2 θ.2.1 θ.2.2
  rw [shapeResidual_eq]
  exact FiniteTaylorJet.ofFunction_sub_eq_zero_of_eq
    (shapeActual_contDiffAt θ) hpoly hjet

/-- The new high-defect theorem makes the high residual's four-jet zero. -/
theorem scaleResidual_zeroJet_via_scaleStationarity
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (scaleResidual θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0 := by
  have hpoly : ContDiffAt ℝ 4 (highPolynomial θ) 0 := by
    unfold highPolynomial
    fun_prop
  have hjet :
      FiniteTaylorJet.ofFunction ℝ 4 (highActual θ) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (highPolynomial θ) 0 := by
    change FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          let x := DFP.TwoLeg.graphJetPath
            θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
          let y := DFP.TwoLeg.stateMap x
          let nextGraph := DFP.TwoLeg.graphJetPath
            θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
          y.2.2 - nextGraph.2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ => (8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4) 0
    exact DFP.TwoLeg.weightedTransverseHDefectJet_via_scaleStationarity
      θ.1.1 θ.1.2 θ.2.1 θ.2.2
  rw [scaleResidual_eq]
  exact FiniteTaylorJet.ofFunction_sub_eq_zero_of_eq
    (highActual_contDiffAt θ) hpoly hjet

/-- The joint radius/shape/high state residual has zero four-jet with every scalar
leaf discharged by scale stationarity. -/
theorem weightedJointResidualJet_via_scaleStationarity
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (jointResidual θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun _ : ℝ => ((0, 0, 0) : ℝ × ℝ × ℝ)) 0 := by
  exact jointResidualJet_of_componentJets θ
    (radiusResidual_zeroJet_via_scaleStationarity θ)
    (shapeResidual_zeroJet_via_scaleStationarity θ)
    (scaleResidual_zeroJet_via_scaleStationarity θ)

end DFP.TwoLeg.StateJetAssembly
