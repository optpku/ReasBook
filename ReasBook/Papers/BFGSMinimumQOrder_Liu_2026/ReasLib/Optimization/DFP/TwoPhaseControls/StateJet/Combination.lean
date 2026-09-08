module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.OfFunctionOperations
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet

public section

/-!
# Componentwise assembly of the joint state jet

This companion separates the formal product assembly in `weightedStateJet` from the three
scalar jet computations.  Its conditional assembly theorem is independent of those upstream
computations; the final adapter records their exact reuse boundary.
-/

noncomputable section

namespace DFP.TwoLeg.StateJet

/-- Radius coordinate of the joint state-jet remainder. -/
def radiusComponent (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  (remainder θ ε).1

/-- Shape coordinate of the joint state-jet remainder. -/
def shapeComponent (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  (remainder θ ε).2.1

/-- High-eigenvalue coordinate of the joint state-jet remainder. -/
def scaleComponent (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ := fun ε =>
  (remainder θ ε).2.2

/-- The joint remainder is assembled from its three scalar components. -/
theorem remainder_eq_components (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) :
    remainder θ ε =
      (radiusComponent θ ε, shapeComponent θ ε, scaleComponent θ ε) := by
  change remainder θ ε =
    ((remainder θ ε).1, (remainder θ ε).2.1, (remainder θ ε).2.2)
  cases hremainder : remainder θ ε with
  | mk radius transverse =>
      cases transverse
      rfl

private def graphPath (θ : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ → ℝ × ℝ × ℝ := fun ε =>
  DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε

private def stateAndNextGraph (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ℝ → (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) := fun ε =>
  let y := DFP.TwoLeg.stateMap (graphPath θ ε)
  (y, DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1)

private theorem graphJetPath_analyticAt (P₃ H₃ P₄ H₄ t : ℝ) :
    AnalyticAt ℝ (fun ε : ℝ => DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε) t := by
  have hpath :
      (fun ε : ℝ => DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε) =
        (fun ε : ℝ =>
          (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
            1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) := by
    funext ε
    exact DFP.TwoLeg.graphJetPath_apply P₃ H₃ P₄ H₄ ε
  rw [hpath]
  fun_prop

private theorem graphPath_analyticAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    AnalyticAt ℝ (graphPath θ) 0 := by
  exact graphJetPath_analyticAt _ _ _ _ _

private theorem graphPath_zero (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    graphPath θ 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  rw [graphPath, DFP.TwoLeg.graphJetPath_apply]
  norm_num

private theorem radiusActual_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4
      (fun ε : ℝ =>
        let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
        DFP.TwoLeg.radiusFactor x.1 x.2.1 x.2.2) 0 := by
  have houter : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ =>
        DFP.TwoLeg.radiusFactor x.1 x.2.1 x.2.2) (graphPath θ 0) := by
    rw [graphPath_zero]
    exact DFP.TwoLeg.analyticAt_radiusFactor
  have hcomp := houter.comp (x := (0 : ℝ)) (f := graphPath θ)
    (graphPath_analyticAt θ)
  simpa only [Function.comp_def, graphPath] using hcomp.contDiffAt

private theorem stateAndNextGraph_analyticAt
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    AnalyticAt ℝ (stateAndNextGraph θ) 0 := by
  let y := fun ε : ℝ => DFP.TwoLeg.stateMap (graphPath θ ε)
  have hstateAtPath : AnalyticAt ℝ DFP.TwoLeg.stateMap (graphPath θ 0) := by
    rw [graphPath_zero]
    exact DFP.TwoLeg.stateMapAnalytic
  have hy : AnalyticAt ℝ y 0 := by
    have hcomp := hstateAtPath.comp (x := (0 : ℝ)) (f := graphPath θ)
      (graphPath_analyticAt θ)
    simpa only [Function.comp_def, y] using hcomp
  have hy₁ : AnalyticAt ℝ (fun ε : ℝ => (y ε).1) 0 := by
    exact analyticAt_fst.comp (x := (0 : ℝ)) (f := y) hy
  have hnextOuter : AnalyticAt ℝ
      (fun t : ℝ => DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 t)
      ((y 0).1) := graphJetPath_analyticAt _ _ _ _ _
  have hnext : AnalyticAt ℝ
      (fun ε : ℝ =>
        DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 (y ε).1) 0 := by
    have hcomp := hnextOuter.comp (x := (0 : ℝ))
      (f := fun ε : ℝ => (y ε).1) hy₁
    simpa only [Function.comp_def] using hcomp
  unfold stateAndNextGraph
  simpa only [graphPath, y] using hy.prod hnext

private theorem stateP_analyticAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    AnalyticAt ℝ (fun ε : ℝ => (stateAndNextGraph θ ε).1.2.1) 0 := by
  have hz := stateAndNextGraph_analyticAt θ
  have hy : AnalyticAt ℝ (fun ε : ℝ => (stateAndNextGraph θ ε).1) 0 := by
    exact analyticAt_fst.comp (x := (0 : ℝ)) hz
  exact analyticAt_fst.comp (x := (0 : ℝ))
    (analyticAt_snd.comp (x := (0 : ℝ)) hy)

private theorem nextP_analyticAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    AnalyticAt ℝ (fun ε : ℝ => (stateAndNextGraph θ ε).2.2.1) 0 := by
  have hz := stateAndNextGraph_analyticAt θ
  have hnext : AnalyticAt ℝ (fun ε : ℝ => (stateAndNextGraph θ ε).2) 0 := by
    exact analyticAt_snd.comp (x := (0 : ℝ)) hz
  exact analyticAt_fst.comp (x := (0 : ℝ))
    (analyticAt_snd.comp (x := (0 : ℝ)) hnext)

private theorem stateH_analyticAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    AnalyticAt ℝ (fun ε : ℝ => (stateAndNextGraph θ ε).1.2.2) 0 := by
  have hz := stateAndNextGraph_analyticAt θ
  have hy : AnalyticAt ℝ (fun ε : ℝ => (stateAndNextGraph θ ε).1) 0 := by
    exact analyticAt_fst.comp (x := (0 : ℝ)) hz
  exact analyticAt_snd.comp (x := (0 : ℝ))
    (analyticAt_snd.comp (x := (0 : ℝ)) hy)

private theorem nextH_analyticAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    AnalyticAt ℝ (fun ε : ℝ => (stateAndNextGraph θ ε).2.2.2) 0 := by
  have hz := stateAndNextGraph_analyticAt θ
  have hnext : AnalyticAt ℝ (fun ε : ℝ => (stateAndNextGraph θ ε).2) 0 := by
    exact analyticAt_snd.comp (x := (0 : ℝ)) hz
  exact analyticAt_snd.comp (x := (0 : ℝ))
    (analyticAt_snd.comp (x := (0 : ℝ)) hnext)

private theorem transversePActual_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4
      (fun ε : ℝ =>
        let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
        let y := DFP.TwoLeg.stateMap x
        let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
        y.2.1 - nextGraph.2.1) 0 := by
  have hfun :
      (fun ε : ℝ =>
        let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
        let y := DFP.TwoLeg.stateMap x
        let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
        y.2.1 - nextGraph.2.1) =
      (fun ε : ℝ => (stateAndNextGraph θ ε).1.2.1) -
        (fun ε : ℝ => (stateAndNextGraph θ ε).2.2.1) := by
    funext ε
    rfl
  rw [hfun]
  exact ((stateP_analyticAt θ).sub (nextP_analyticAt θ)).contDiffAt

private theorem transverseHActual_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4
      (fun ε : ℝ =>
        let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
        let y := DFP.TwoLeg.stateMap x
        let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
        y.2.2 - nextGraph.2.2) 0 := by
  have hfun :
      (fun ε : ℝ =>
        let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
        let y := DFP.TwoLeg.stateMap x
        let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
        y.2.2 - nextGraph.2.2) =
      (fun ε : ℝ => (stateAndNextGraph θ ε).1.2.2) -
        (fun ε : ℝ => (stateAndNextGraph θ ε).2.2.2) := by
    funext ε
    rfl
  rw [hfun]
  exact ((stateH_analyticAt θ).sub (nextH_analyticAt θ)).contDiffAt

/-- The radius component of the remainder is `C⁴` at the jet base point. -/
theorem radiusComponent_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4 (radiusComponent θ) 0 := by
  have hpolynomial : ContDiffAt ℝ 4
      (fun ε : ℝ =>
        1 + ((6 * θ.1.2 + 5 * θ.1.1 - 300) / 18) * ε ^ 3 +
          ((6 * θ.2.2 + 5 * θ.2.1 + 54) / 18) * ε ^ 4) 0 := by
    fun_prop
  unfold radiusComponent
  simpa only [remainder_apply] using
    (radiusActual_contDiffAt θ).sub hpolynomial

/-- The shape component of the remainder is `C⁴` at the jet base point. -/
theorem shapeComponent_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4 (shapeComponent θ) 0 := by
  have hpolynomial : ContDiffAt ℝ 4
      (fun ε : ℝ =>
        ((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
          ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4) 0 := by
    fun_prop
  unfold shapeComponent
  simpa only [remainder_apply] using
    (transversePActual_contDiffAt θ).sub hpolynomial

/-- The high-eigenvalue component of the remainder is `C⁴` at the jet base point. -/
theorem scaleComponent_contDiffAt (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 4 (scaleComponent θ) 0 := by
  have hpolynomial : ContDiffAt ℝ 4
      (fun ε : ℝ => (8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4) 0 := by
    fun_prop
  unfold scaleComponent
  simpa only [remainder_apply] using
    (transverseHActual_contDiffAt θ).sub hpolynomial

/-- Assemble the joint zero jet from independent scalar zero-jet certificates. -/
theorem weightedStateJet_of_componentJets
    (θ : (ℝ × ℝ) × (ℝ × ℝ))
    (hr : FiniteTaylorJet.ofFunction ℝ 4 (radiusComponent θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0)
    (hp : FiniteTaylorJet.ofFunction ℝ 4 (shapeComponent θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0)
    (hh : FiniteTaylorJet.ofFunction ℝ 4 (scaleComponent θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0) :
    FiniteTaylorJet.ofFunction ℝ 4 (remainder θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun _ : ℝ => ((0, 0, 0) : ℝ × ℝ × ℝ)) 0 := by
  have htransverseCont :=
    (shapeComponent_contDiffAt θ).prodMk (scaleComponent_contDiffAt θ)
  have htransverse := FiniteTaylorJet.ofFunction_prodMk_eq_zero
    (shapeComponent_contDiffAt θ) (scaleComponent_contDiffAt θ) hp hh
  have hjoint := FiniteTaylorJet.ofFunction_prodMk_eq_zero
    (radiusComponent_contDiffAt θ) htransverseCont hr htransverse
  have hremainder : remainder θ = fun ε : ℝ =>
      (radiusComponent θ ε, shapeComponent θ ε, scaleComponent θ ε) := by
    funext ε
    exact remainder_eq_components θ ε
  rw [hremainder]
  exact hjoint

/-- The normalized-radius jet supplies the radius component's zero jet. -/
theorem radiusComponent_zeroJet (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (radiusComponent θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0 := by
  have h := FiniteTaylorJet.ofFunction_sub_eq_zero_of_eq
    (radiusActual_contDiffAt θ)
    (by fun_prop : ContDiffAt ℝ 4
      (fun ε : ℝ =>
        1 + ((6 * θ.1.2 + 5 * θ.1.1 - 300) / 18) * ε ^ 3 +
          ((6 * θ.2.2 + 5 * θ.2.1 + 54) / 18) * ε ^ 4) 0)
    (DFP.TwoLeg.weightedNormalizedRadiusJet θ.1.1 θ.1.2 θ.2.1 θ.2.2)
  unfold radiusComponent
  simpa only [remainder_apply] using h

/-- The transverse shape-defect jet supplies the shape component's zero jet. -/
theorem shapeComponent_zeroJet (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (shapeComponent θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0 := by
  have h := FiniteTaylorJet.ofFunction_sub_eq_zero_of_eq
    (transversePActual_contDiffAt θ)
    (by fun_prop : ContDiffAt ℝ 4
      (fun ε : ℝ =>
        ((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
          ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4) 0)
    (DFP.TwoLeg.weightedTransversePDefectJet θ.1.1 θ.1.2 θ.2.1 θ.2.2)
  unfold shapeComponent
  simpa only [remainder_apply] using h

/-- The transverse high-defect jet supplies the scale component's zero jet. -/
theorem scaleComponent_zeroJet (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (scaleComponent θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ => (0 : ℝ)) 0 := by
  have h := FiniteTaylorJet.ofFunction_sub_eq_zero_of_eq
    (transverseHActual_contDiffAt θ)
    (by fun_prop : ContDiffAt ℝ 4
      (fun ε : ℝ => (8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4) 0)
    (DFP.TwoLeg.weightedTransverseHDefectJet θ.1.1 θ.1.2 θ.2.1 θ.2.2)
  unfold scaleComponent
  simpa only [remainder_apply] using h

/-- Exact adapter for `weightedStateJet`, reducing it to the three existing scalar jets. -/
theorem weightedStateJet_via_components (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (remainder θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun _ : ℝ => ((0, 0, 0) : ℝ × ℝ × ℝ)) 0 := by
  exact weightedStateJet_of_componentJets θ
    (radiusComponent_zeroJet θ) (shapeComponent_zeroJet θ) (scaleComponent_zeroJet θ)

end DFP.TwoLeg.StateJet
