module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph
public import ReasLib.Analysis.Calculus.ContDiff.Taylor
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import ReasLib.Optimization.DFP.StableMatrix
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap.Linearization
public import ReasLib.Optimization.DFP.TwoPhaseControls.TransverseJet
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

noncomputable section

/-- Helper for `exists_localForwardInvariantSlowCurve`: the linear coordinate change
identifying the two transverse state coordinates with `Fin 2 → ℝ`. -/
private noncomputable def slowCurveStateEquiv :
    (ℝ × (Fin 2 → ℝ)) ≃L[ℝ] (ℝ × ℝ × ℝ) :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

/-- Helper for `exists_localForwardInvariantSlowCurve`: the fixed state about which
the center-stable dynamics is translated. -/
private def slowCurveBase : ℝ × ℝ × ℝ :=
  (0, 2, 1)

/-- Helper for `exists_localForwardInvariantSlowCurve`: the state map translated to
the origin and expressed in stable `Fin 2` coordinates. -/
private noncomputable def slowCurveShiftedMap
    (x : ℝ × (Fin 2 → ℝ)) : ℝ × (Fin 2 → ℝ) :=
  slowCurveStateEquiv.symm
    (stateMap (slowCurveStateEquiv x + slowCurveBase) - slowCurveBase)

/-- Helper for `exists_localForwardInvariantSlowCurve`: evaluation of the state
coordinate change on a center-stable vector. -/
private theorem slowCurveStateEquiv_apply (x : ℝ × (Fin 2 → ℝ)) :
    slowCurveStateEquiv x = (x.1, x.2 0, x.2 1) := by
  rfl

/-- Helper for `exists_localForwardInvariantSlowCurve`: evaluation of the inverse
state coordinate change. -/
private theorem slowCurveStateEquiv_symm_apply (x : ℝ × ℝ × ℝ) :
    slowCurveStateEquiv.symm x = (x.1, ![x.2.1, x.2.2]) := by
  rfl

/-- Helper for `exists_localForwardInvariantSlowCurve`: coordinate formula for the
translated state map. -/
private theorem slowCurveShiftedMap_apply (ε : ℝ) (z : Fin 2 → ℝ) :
    slowCurveShiftedMap (ε, z) =
      let y := stateMap (ε, z 0 + 2, z 1 + 1)
      (y.1, ![y.2.1 - 2, y.2.2 - 1]) := by
  rw [slowCurveShiftedMap, slowCurveStateEquiv_apply]
  simp only [slowCurveBase, Prod.mk_add_mk, add_zero]
  rw [slowCurveStateEquiv_symm_apply]
  apply Prod.ext
  · simp
  · funext i
    fin_cases i
    · simp
    · simp

/-- Helper for `exists_localForwardInvariantSlowCurve`: the translated state map fixes
the origin in center-stable coordinates. -/
private theorem slowCurveShiftedMap_zero :
    slowCurveShiftedMap (0, 0) = (0, 0) := by
  have hinput : slowCurveStateEquiv (0, 0) + slowCurveBase = (0, 2, 1) := by
    rw [slowCurveStateEquiv_apply]
    norm_num [slowCurveBase]
  rw [slowCurveShiftedMap, hinput, stateMap_base]
  rw [slowCurveBase, sub_self, slowCurveStateEquiv_symm_apply]
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i
    · rfl
    · rfl

/-- Helper for `exists_localForwardInvariantSlowCurve`: the translated state map is
`C^7` at the center-stable origin. -/
private theorem slowCurveShiftedMap_contDiffAt :
    ContDiffAt ℝ 7 slowCurveShiftedMap (0, 0) := by
  have hinput : ContDiffAt ℝ 7
      (fun x : ℝ × (Fin 2 → ℝ) ↦ slowCurveStateEquiv x + slowCurveBase) (0, 0) := by
    exact slowCurveStateEquiv.contDiff.contDiffAt.add contDiffAt_const
  have hinputBase : slowCurveStateEquiv (0, 0) + slowCurveBase = (0, 2, 1) := by
    rw [slowCurveStateEquiv_apply]
    norm_num [slowCurveBase]
  have hstate : ContDiffAt ℝ 7
      (fun x : ℝ × (Fin 2 → ℝ) ↦
        stateMap (slowCurveStateEquiv x + slowCurveBase)) (0, 0) := by
    have houter : ContDiffAt ℝ 7 stateMap
        (slowCurveStateEquiv (0, 0) + slowCurveBase) := by
      simpa only [hinputBase] using stateMapAnalytic.contDiffAt
    exact houter.comp (0, 0) hinput
  have hbase : ContDiffAt ℝ 7
      (fun _ : ℝ × (Fin 2 → ℝ) ↦ slowCurveBase) (0, 0) :=
    contDiffAt_const
  have htranslated := hstate.sub hbase
  have houtput := htranslated.continuousLinearMap_comp
    slowCurveStateEquiv.symm.toContinuousLinearMap
  apply houtput.congr_of_eventuallyEq
  filter_upwards [] with x
  rfl

/-- Helper for `exists_localForwardInvariantSlowCurve`: the derivative of the translated
state map is the center identity together with `DFPStable.map`. -/
private theorem slowCurveShiftedMap_hasFDerivAt :
    HasFDerivAt slowCurveShiftedMap
      (LocalCutoff.centerStable
        (Module.End.toContinuousLinearMap (Fin 2 → ℝ) DFPStable.map)) (0, 0) := by
  have hinput : HasFDerivAt
      (fun x : ℝ × (Fin 2 → ℝ) ↦ slowCurveStateEquiv x + slowCurveBase)
      slowCurveStateEquiv.toContinuousLinearMap (0, 0) :=
    slowCurveStateEquiv.toContinuousLinearMap.hasFDerivAt.add_const slowCurveBase
  have hinputBase : slowCurveStateEquiv (0, 0) + slowCurveBase = (0, 2, 1) := by
    rw [slowCurveStateEquiv_apply]
    norm_num [slowCurveBase]
  have hstateAtBase : HasFDerivAt stateMap
      (fderiv ℝ stateMap (0, 2, 1)) (0, 2, 1) :=
    stateMapAnalytic.differentiableAt.hasFDerivAt
  have hstateAtInput : HasFDerivAt stateMap
      (fderiv ℝ stateMap (0, 2, 1))
      (slowCurveStateEquiv (0, 0) + slowCurveBase) := by
    simpa only [hinputBase] using hstateAtBase
  have hinner := hstateAtInput.comp (0, 0) hinput
  have htranslated := hinner.sub_const slowCurveBase
  have hconjugated := slowCurveStateEquiv.symm.toContinuousLinearMap.hasFDerivAt.comp
    (0, 0) htranslated
  have hraw : HasFDerivAt slowCurveShiftedMap
      (slowCurveStateEquiv.symm.toContinuousLinearMap.comp
        ((fderiv ℝ stateMap (0, 2, 1)).comp
          slowCurveStateEquiv.toContinuousLinearMap)) (0, 0) := by
    apply hconjugated.congr_of_eventuallyEq
    filter_upwards [] with x
    rfl
  apply hraw.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change slowCurveStateEquiv.symm
      (fderiv ℝ stateMap (0, 2, 1) (slowCurveStateEquiv v)) = _
  rw [
    slowCurveStateEquiv_apply, stateMap_fderiv_apply,
    slowCurveStateEquiv_symm_apply, LocalCutoff.centerStable_apply]
  change _ = (v.1, DFPStable.map v.2)
  rw [DFPStable.map_apply, DFPStable.matrix_mulVec]
  apply Prod.ext
  · rfl
  · funext i
    fin_cases i
    · dsimp
      ring
    · rfl

/-- Helper for `exists_localForwardInvariantSlowCurve`: the stable matrix contracts the
weighted coordinate seminorm at rate `1 / 2`. -/
private theorem slowCurveStableMap_isContractingHalf :
    DFPStable.weightedSum.IsContracting DFPStable.map (1 / 2) := by
  rw [Seminorm.isContracting_iff]
  refine ⟨1 / 3, ?_, ?_⟩
  · norm_num
  · exact DFPStable.weightedSum_contracts.1

/-- Helper for `exists_localForwardInvariantSlowCurve`: the translated center-stable
dynamics admits a local `C^7` invariant graph in `Fin 2` coordinates. -/
private theorem exists_shiftedSlowCurveGraph :
    ∃ ζ : ℝ → (Fin 2 → ℝ),
      ContDiffAt ℝ 7 ζ 0 ∧
        ζ 0 = 0 ∧
          HasFDerivAt ζ (0 : ℝ →L[ℝ] (Fin 2 → ℝ)) 0 ∧
            (fun u ↦ (slowCurveShiftedMap (u, ζ u)).2) =ᶠ[𝓝 0]
              (fun u ↦ ζ (slowCurveShiftedMap (u, ζ u)).1) := by
  have hsmoothnessOrder : 2 ≤ 7 := by
    norm_num
  have hrate : (1 / 2 : NNReal) < 1 := by
    norm_num
  exact LocalInvariantGraph.existsOfEquivalentContractingSeminorm 7
    slowCurveShiftedMap DFPStable.map DFPStable.weightedSum (1 / 2)
    hsmoothnessOrder slowCurveShiftedMap_contDiffAt slowCurveShiftedMap_zero
    slowCurveShiftedMap_hasFDerivAt DFPStable.weightedSum_isEquivalent
    slowCurveStableMap_isContractingHalf hrate

/-- Helper for `exists_localForwardInvariantSlowCurve`: translating the invariant graph
back to state coordinates gives a `C^7` graph through `(2, 1)`, tangent to zero. -/
private theorem exists_slowCurveGraphCore :
    ∃ p h : ℝ → ℝ,
      ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0 ∧
        (p 0, h 0) = (2, 1) ∧
          HasFDerivAt (fun ε ↦ (p ε, h ε))
            (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 ∧
            (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
              (fun ε ↦
                let ε' := (stateMap (ε, p ε, h ε)).1
                (ε', p ε', h ε')) := by
  obtain ⟨ζ, hζ_smooth, hζ_zero, hζ_deriv, hζ_invariant⟩ :=
    exists_shiftedSlowCurveGraph
  let p : ℝ → ℝ := fun ε ↦ ζ ε 0 + 2
  let h : ℝ → ℝ := fun ε ↦ ζ ε 1 + 1
  refine ⟨p, h, ?_, ?_, ?_, ?_⟩
  · have hpair := hζ_smooth.continuousLinearMap_comp
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap
    have hconstant : ContDiffAt ℝ 7
        (fun _ : ℝ ↦ ((2, 1) : ℝ × ℝ)) 0 :=
      contDiffAt_const
    have htranslated := hpair.add hconstant
    apply htranslated.congr_of_eventuallyEq
    filter_upwards [] with ε
    rfl
  · simp only [p, h, hζ_zero, Pi.zero_apply, zero_add]
  · have hpair :=
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap.hasFDerivAt.comp
        0 hζ_deriv
    have htranslated := hpair.add_const ((2, 1) : ℝ × ℝ)
    have hzero :
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap.comp
            (0 : ℝ →L[ℝ] (Fin 2 → ℝ)) =
          (0 : ℝ →L[ℝ] (ℝ × ℝ)) := by
      apply ContinuousLinearMap.ext
      intro x
      simp
    have htranslatedZero := htranslated.congr_fderiv hzero
    apply htranslatedZero.congr_of_eventuallyEq
    filter_upwards [] with ε
    rfl
  · filter_upwards [hζ_invariant] with ε hε
    rw [slowCurveShiftedMap_apply] at hε
    dsimp only [p, h]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · have hshape := congrArg (fun z : Fin 2 → ℝ ↦ z 0) hε
        simp only [Matrix.cons_val_zero] at hshape
        linarith
      · have hhigh := congrArg (fun z : Fin 2 → ℝ ↦ z 1) hε
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hhigh
        linarith

/-- Helper for `exists_localForwardInvariantSlowCurve`: the transverse state map has
zero second derivative along the pure signed-scale axis at the base. -/
private theorem slowCurveStateTransverse_pureScale_secondDeriv :
    iteratedDeriv 2 (fun ε : ℝ ↦ (stateMap (ε, 2, 1)).2) 0 = (0, 0) := by
  let shape : ℝ → ℝ := fun ε ↦ (stateMap (ε, 2, 1)).2.1
  let high : ℝ → ℝ := fun ε ↦ (stateMap (ε, 2, 1)).2.2
  let shapePolynomial : ℝ → ℝ := fun ε ↦
    2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4
  let highPolynomial : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let shapeLeft : ℝ → ℝ := fun ε ↦ 2 + (348 / 9) * ε ^ 3
  let shapeRight : ℝ → ℝ := fun ε ↦ (18 / 9) * ε ^ 4
  have hshapeJet :
      FiniteTaylorJet.ofFunction ℝ 4 shape 0 =
        FiniteTaylorJet.ofFunction ℝ 4 shapePolynomial 0 := by
    simpa only [shape, shapePolynomial] using stateMap_shape_pureScaleJet
  have hhighJet :
      FiniteTaylorJet.ofFunction ℝ 4 high 0 =
        FiniteTaylorJet.ofFunction ℝ 4 highPolynomial 0 := by
    simpa only [high, highPolynomial] using stateMap_high_pureScaleJet
  have hshape :=
    (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 4
      shape shapePolynomial 0 0).mp hshapeJet (2 : Fin 5)
  have hhigh :=
    (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 4
      high highPolynomial 0 0).mp hhighJet (2 : Fin 5)
  have hshapeLeft : ContDiffAt ℝ 2 shapeLeft 0 := by
    simp only [shapeLeft]
    fun_prop
  have hshapeRight : ContDiffAt ℝ 2 shapeRight 0 := by
    simp only [shapeRight]
    fun_prop
  have hshapePolynomialEq : shapePolynomial = shapeLeft - shapeRight := by
    rfl
  have htwoPos : 0 < (2 : ℕ) := by
    norm_num
  have hshapePolynomialSecond : iteratedDeriv 2 shapePolynomial 0 = 0 := by
    rw [hshapePolynomialEq, iteratedDeriv_sub hshapeLeft hshapeRight]
    simp only [shapeLeft, shapeRight]
    simp only [iteratedDeriv_const_add (n := 2) htwoPos,
      iteratedDeriv_const_mul_field, iteratedDeriv_pow]
    norm_num
  have hhighPolynomialSecond : iteratedDeriv 2 highPolynomial 0 = 0 := by
    have hhighPolynomialEq : highPolynomial = fun ε : ℝ ↦ 1 + 8 * ε ^ 3 := by
      rfl
    rw [hhighPolynomialEq, iteratedDeriv_const_add (n := 2) htwoPos]
    simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
    norm_num
  have hshapeSecond : iteratedDeriv 2 shape 0 = 0 :=
    hshape.trans hshapePolynomialSecond
  have hhighSecond : iteratedDeriv 2 high 0 = 0 :=
    hhigh.trans hhighPolynomialSecond
  have hscalePath : ContDiffAt ℝ 2
      (fun ε : ℝ ↦ ((ε, 2, 1) : ℝ × ℝ × ℝ)) 0 := by
    fun_prop
  have hstate := stateMapAnalytic.contDiffAt.comp 0 hscalePath
  have hshapeContDiff : ContDiffAt ℝ 2 shape 0 := by
    simpa only [shape, Function.comp_apply] using hstate.snd.fst
  have hhighContDiff : ContDiffAt ℝ 2 high 0 := by
    simpa only [high, Function.comp_apply] using hstate.snd.snd
  have htransversePair : (fun ε : ℝ ↦ (stateMap (ε, 2, 1)).2) =
      (fun ε ↦ (shape ε, high ε)) := by
    rfl
  rw [htransversePair, iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_prodMk hshapeContDiff hhighContDiff le_rfl]
  change (iteratedDeriv 2 shape 0, iteratedDeriv 2 high 0) = (0, 0)
  rw [hshapeSecond, hhighSecond]

/-- Helper for `exists_localForwardInvariantSlowCurve`: the second derivative of a
graph path packages the two transverse scalar accelerations. -/
private theorem slowCurveGraphPath_secondDeriv (p h : ℝ → ℝ)
    (h_contDiff : ContDiffAt ℝ 2 (fun ε ↦ (p ε, h ε)) 0) :
    iteratedDeriv 2 (fun ε ↦ ((ε, p ε, h ε) : ℝ × ℝ × ℝ)) 0 =
      (0, iteratedDeriv 2 p 0, iteratedDeriv 2 h 0) := by
  have hp : ContDiffAt ℝ 2 p 0 := h_contDiff.fst
  have hh : ContDiffAt ℝ 2 h 0 := h_contDiff.snd
  have hpathEq : (fun ε ↦ ((ε, p ε, h ε) : ℝ × ℝ × ℝ)) =
      (fun ε ↦ (id ε, (p ε, h ε))) := by
    rfl
  rw [hpathEq, iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_prodMk contDiffAt_id (hp.prodMk hh) le_rfl,
    iteratedFDeriv_prodMk hp hh le_rfl]
  change (iteratedDeriv 2 id 0, iteratedDeriv 2 p 0, iteratedDeriv 2 h 0) =
    (0, iteratedDeriv 2 p 0, iteratedDeriv 2 h 0)
  norm_num [iteratedDeriv_id]

/-- Helper for `exists_localForwardInvariantSlowCurve`: along a tangent graph, the
transverse acceleration is the stable linear response to the graph acceleration. -/
private theorem slowCurveStateTransverse_secondDeriv (p h : ℝ → ℝ)
    (h_contDiff : ContDiffAt ℝ 2 (fun ε ↦ (p ε, h ε)) 0)
    (h_base : (p 0, h 0) = (2, 1))
    (h_tangent : HasFDerivAt (fun ε ↦ (p ε, h ε))
      (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0) :
    iteratedDeriv 2 (fun ε ↦ (stateMap (ε, p ε, h ε)).2) 0 =
      ((-(1 : ℝ) / 9) * iteratedDeriv 2 p 0 +
          ((2 : ℝ) / 3) * iteratedDeriv 2 h 0,
        0) := by
  let path : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let transverse : ℝ × ℝ × ℝ → ℝ × ℝ := fun x ↦ (stateMap x).2
  have hpathContDiff : ContDiffAt ℝ 2 path 0 := by
    exact contDiffAt_id.prodMk h_contDiff
  have hpathBase : path 0 = (0, 2, 1) := by
    simp only [path]
    rw [h_base]
  have htransverseContDiff : ContDiffAt ℝ 2 transverse (path 0) := by
    rw [hpathBase]
    exact (analyticAt_snd.comp stateMapAnalytic).contDiffAt
  have hpathDeriv : deriv path 0 = (1, 0, 0) := by
    have hgraphDeriv : HasDerivAt (fun ε ↦ (p ε, h ε))
        (0 : ℝ × ℝ) 0 := h_tangent.hasDerivAt
    have hpathHasDeriv : HasDerivAt path (1, 0, 0) 0 := by
      have hraw := (hasDerivAt_id 0).prodMk hgraphDeriv
      apply hraw.congr_deriv
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · rfl
    exact hpathHasDeriv.deriv
  let scalePath : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, 2, 1)
  have hscalePathContDiff : ContDiffAt ℝ 2 scalePath 0 := by
    simp only [scalePath]
    fun_prop
  have hscalePathDeriv : deriv scalePath 0 = (1, 0, 0) := by
    have htwo : HasDerivAt (fun _ : ℝ ↦ (2 : ℝ)) 0 0 :=
      hasDerivAt_const 0 2
    have hone : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 0 :=
      hasDerivAt_const 0 1
    have hderiv := (hasDerivAt_id 0).prodMk (htwo.prodMk hone)
    simpa only [scalePath, id_eq] using hderiv.deriv
  have hconstantGraph : ContDiffAt ℝ 2
      (fun _ : ℝ ↦ ((2, 1) : ℝ × ℝ)) 0 := by
    fun_prop
  have hscalePathSecond : iteratedDeriv 2 scalePath 0 = 0 := by
    change iteratedDeriv 2 scalePath 0 = ((0, 0, 0) : ℝ × ℝ × ℝ)
    simpa [scalePath, iteratedDeriv_const] using
      slowCurveGraphPath_secondDeriv (fun _ ↦ 2) (fun _ ↦ 1) hconstantGraph
  have hscaleComposition := iteratedDeriv_vcomp_two
    (g := transverse) (f := scalePath)
    ((analyticAt_snd.comp stateMapAnalytic).contDiffAt :
      ContDiffAt ℝ 2 transverse (scalePath 0)) hscalePathContDiff
  have hscaleHessian :
      iteratedFDeriv ℝ 2 transverse (0, 2, 1)
          (fun _ ↦ ((1, 0, 0) : ℝ × ℝ × ℝ)) = 0 := by
    change iteratedDeriv 2 (fun ε : ℝ ↦ (stateMap (ε, 2, 1)).2) 0 = _
      at hscaleComposition
    rw [slowCurveStateTransverse_pureScale_secondDeriv, hscalePathDeriv,
      hscalePathSecond, map_zero, add_zero] at hscaleComposition
    change iteratedFDeriv ℝ 2 transverse (0, 2, 1)
      (fun _ ↦ ((1, 0, 0) : ℝ × ℝ × ℝ)) = (0, 0)
    simpa only [scalePath] using hscaleComposition.symm
  have htransverseFDeriv (v : ℝ × ℝ × ℝ) :
      fderiv ℝ transverse (0, 2, 1) v =
        ((-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0) := by
    have hcomponent := stateMapAnalytic.differentiableAt.hasFDerivAt.snd
    have htransverseEq : transverse = fun x ↦ (stateMap x).2 := by
      rfl
    rw [htransverseEq, hcomponent.fderiv]
    change (fderiv ℝ stateMap (0, 2, 1) v).2 =
      ((-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0)
    rw [stateMap_fderiv_apply]
  have hcomposition := iteratedDeriv_vcomp_two htransverseContDiff hpathContDiff
  rw [hpathBase, hpathDeriv, hscaleHessian, zero_add,
    slowCurveGraphPath_secondDeriv p h h_contDiff, htransverseFDeriv] at hcomposition
  simpa only [path, transverse, Function.comp_def] using hcomposition

/-- Helper for `exists_localForwardInvariantSlowCurve`: every twice differentiable
invariant graph through the base and tangent to the scale axis is flat through order two. -/
private theorem slowCurveInvariantGraph_secondOrderFlat (p h : ℝ → ℝ)
    (h_contDiff : ContDiffAt ℝ 2 (fun ε ↦ (p ε, h ε)) 0)
    (h_base : (p 0, h 0) = (2, 1))
    (h_tangent : HasFDerivAt (fun ε ↦ (p ε, h ε))
      (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0)
    (h_invariant : (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) :
    iteratedDeriv 1 p 0 = 0 ∧
      iteratedDeriv 1 h 0 = 0 ∧
        iteratedDeriv 2 p 0 = 0 ∧
          iteratedDeriv 2 h 0 = 0 := by
  let graph : ℝ → ℝ × ℝ := fun ε ↦ (p ε, h ε)
  let path : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let scale : ℝ → ℝ := fun ε ↦ (stateMap (path ε)).1
  have hgraphTangent : HasFDerivAt graph
      (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 := by
    simpa only [graph] using h_tangent
  have hgraphTangentDeriv : HasDerivAt graph (0, 0) 0 := by
    apply hgraphTangent.hasDerivAt.congr_deriv
    apply Prod.ext
    · simp
    · simp
  have hpFirstDeriv : HasDerivAt p 0 0 := by
    apply hgraphTangent.fst.hasDerivAt.congr_deriv
    simp
  have hhFirstDeriv : HasDerivAt h 0 0 := by
    apply hgraphTangent.snd.hasDerivAt.congr_deriv
    simp
  have hpFirst : iteratedDeriv 1 p 0 = 0 := by
    simpa only [iteratedDeriv_one] using hpFirstDeriv.deriv
  have hhFirst : iteratedDeriv 1 h 0 = 0 := by
    simpa only [iteratedDeriv_one] using hhFirstDeriv.deriv
  have hgraphContDiff : ContDiffAt ℝ 2 graph 0 := by
    simpa only [graph] using h_contDiff
  have hpathContDiff : ContDiffAt ℝ 2 path 0 := by
    exact contDiffAt_id.prodMk h_contDiff
  have hpathBase : path 0 = (0, 2, 1) := by
    simp only [path]
    rw [h_base]
  have hpathTangent : HasDerivAt path (1, 0, 0) 0 := by
    have hraw := (hasDerivAt_id 0).prodMk hgraphTangentDeriv
    apply hraw.congr_deriv
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · rfl
  have hstateAtPath : DifferentiableAt ℝ stateMap (path 0) := by
    rw [hpathBase]
    exact stateMapAnalytic.differentiableAt
  have hstatePathTangent : HasDerivAt (stateMap ∘ path) (1, 0, 0) 0 := by
    have hraw := hstateAtPath.hasFDerivAt.comp_hasDerivAt 0 hpathTangent
    apply hraw.congr_deriv
    rw [hpathBase, stateMap_fderiv_apply]
    norm_num
  have hscaleTangent : HasDerivAt scale 1 0 := by
    have hraw := hstatePathTangent.hasFDerivAt.fst.hasDerivAt
    apply hraw.congr_deriv
    simp
  have hscaleBase : scale 0 = 0 := by
    simp only [scale, hpathBase, stateMap_base]
  have hstateAtPathContDiff : ContDiffAt ℝ 2 stateMap (path 0) := by
    rw [hpathBase]
    exact stateMapAnalytic.contDiffAt
  have hstatePathContDiff : ContDiffAt ℝ 2 (stateMap ∘ path) 0 :=
    hstateAtPathContDiff.comp 0 hpathContDiff
  have hscaleContDiff : ContDiffAt ℝ 2 scale 0 := by
    simpa only [scale, Function.comp_apply] using hstatePathContDiff.fst
  have hgraphAtScale : ContDiffAt ℝ 2 graph (scale 0) := by
    rw [hscaleBase]
    exact hgraphContDiff
  have hgraphFDeriv : fderiv ℝ graph 0 = 0 := hgraphTangent.fderiv
  have hgraphSecond :
      iteratedDeriv 2 graph 0 =
        (iteratedDeriv 2 p 0, iteratedDeriv 2 h 0) := by
    rw [iteratedDeriv_eq_iteratedFDeriv,
      iteratedFDeriv_prodMk h_contDiff.fst h_contDiff.snd le_rfl]
    rfl
  have hgraphCompSecond :
      iteratedDeriv 2 (graph ∘ scale) 0 =
        (iteratedDeriv 2 p 0, iteratedDeriv 2 h 0) := by
    have hcomposition := iteratedDeriv_vcomp_two hgraphAtScale hscaleContDiff
    rw [hscaleBase, hscaleTangent.deriv, hgraphFDeriv,
      zero_apply, add_zero,
      ← iteratedDeriv_eq_iteratedFDeriv, hgraphSecond] at hcomposition
    exact hcomposition
  have htransverseInvariant :
      (fun ε ↦ (stateMap (path ε)).2) =ᶠ[𝓝 0] graph ∘ scale := by
    filter_upwards [h_invariant] with ε hε
    simpa only [path, graph, scale, Function.comp_apply] using congrArg Prod.snd hε
  have htransverseSecond := htransverseInvariant.iteratedDeriv_eq 2
  have hstateSecond :=
    slowCurveStateTransverse_secondDeriv p h h_contDiff h_base h_tangent
  have hfixedSecond :
      ((-(1 : ℝ) / 9) * iteratedDeriv 2 p 0 +
          ((2 : ℝ) / 3) * iteratedDeriv 2 h 0,
        0) = (iteratedDeriv 2 p 0, iteratedDeriv 2 h 0) := by
    calc
      _ = iteratedDeriv 2 (fun ε ↦ (stateMap (path ε)).2) 0 := by
        simpa only [path] using hstateSecond.symm
      _ = iteratedDeriv 2 (graph ∘ scale) 0 := htransverseSecond
      _ = _ := hgraphCompSecond
  have hshapeSecond := congrArg Prod.fst hfixedSecond
  have hhighSecond := congrArg Prod.snd hfixedSecond
  have hhSecond : iteratedDeriv 2 h 0 = 0 := by
    simpa only [Prod.snd] using hhighSecond.symm
  have hpSecond : iteratedDeriv 2 p 0 = 0 := by
    simp only [hhSecond, mul_zero, add_zero] at hshapeSecond
    linarith
  exact ⟨hpFirst, hhFirst, hpSecond, hhSecond⟩

/-- Helper for `exists_localForwardInvariantSlowCurve`: a `C^5` graph flat through
second order has cubic and quartic Taylor coefficients with fifth-order remainder. -/
private theorem exists_slowCurveTaylorCoefficients (p h : ℝ → ℝ)
    (h_contDiff : ContDiffAt ℝ 5 (fun ε ↦ (p ε, h ε)) 0)
    (h_base : (p 0, h 0) = (2, 1))
    (h_p_first : iteratedDeriv 1 p 0 = 0)
    (h_h_first : iteratedDeriv 1 h 0 = 0)
    (h_p_second : iteratedDeriv 2 p 0 = 0)
    (h_h_second : iteratedDeriv 2 h 0 = 0) :
    ∃ P₃ H₃ P₄ H₄ : ℝ,
      (fun ε ↦ p ε - (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) ∧
        (fun ε ↦ h ε - (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) := by
  have hp0 : p 0 = 2 := congrArg Prod.fst h_base
  have hh0 : h 0 = 1 := congrArg Prod.snd h_base
  have hp_cont : ContDiffAt ℝ 5 p 0 := by
    simpa using h_contDiff.fst
  have hh_cont : ContDiffAt ℝ 5 h 0 := by
    simpa using h_contDiff.snd
  let ps : ℝ → ℝ := fun ε ↦ p ε - 2
  let hs : ℝ → ℝ := fun ε ↦ h ε - 1
  have hps_cont : ContDiffAt ℝ 5 ps 0 := by
    dsimp only [ps]
    exact hp_cont.sub contDiffAt_const
  have hhs_cont : ContDiffAt ℝ 5 hs 0 := by
    dsimp only [hs]
    exact hh_cont.sub contDiffAt_const
  have hps_zero : ∀ n < 3, iteratedDeriv n ps 0 = 0 := by
    intro n hn
    interval_cases n
    · simp [ps, iteratedDeriv_zero, hp0]
    · simpa [ps, iteratedDeriv_one] using h_p_first
    · simpa [ps, iteratedDeriv_succ, iteratedDeriv_one] using h_p_second
  have hhs_zero : ∀ n < 3, iteratedDeriv n hs 0 = 0 := by
    intro n hn
    interval_cases n
    · simp [hs, iteratedDeriv_zero, hh0]
    · simpa [hs, iteratedDeriv_one] using h_h_first
    · simpa [hs, iteratedDeriv_succ, iteratedDeriv_one] using h_h_second
  have hthreeFive : 3 ≤ 5 := by
    norm_num
  have hpsTaylor :=
    ContDiffAt.taylor_isLittleO_of_iteratedDeriv_eq_zero hps_cont
      hthreeFive hps_zero
  have hhsTaylor :=
    ContDiffAt.taylor_isLittleO_of_iteratedDeriv_eq_zero hhs_cont
      hthreeFive hhs_zero
  let P₃ : ℝ := ((3 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 3 ps 0
  let H₃ : ℝ := ((3 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 3 hs 0
  let P₄ : ℝ := ((4 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 4 ps 0
  let H₄ : ℝ := ((4 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 4 hs 0
  refine ⟨P₃, H₃, P₄, H₄, ?_, ?_⟩
  · have hmain := hpsTaylor.isBigO
    have h5 :
        (fun ε : ℝ ↦
          (((5 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 5 ps 0) * ε ^ 5) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) := by
      simpa only [smul_eq_mul] using
        (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).const_mul_left
          (((5 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 5 ps 0)
    have hsum := hmain.add h5
    apply hsum.congr'
    · filter_upwards [] with ε
      dsimp only [ps, P₃, P₄]
      norm_num [Finset.sum_Icc_succ_top]
      ring
    · rfl
  · have hmain := hhsTaylor.isBigO
    have h5 :
        (fun ε : ℝ ↦
          (((5 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 5 hs 0) * ε ^ 5) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) := by
      simpa only [smul_eq_mul] using
        (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)).const_mul_left
          (((5 : ℕ).factorial : ℝ)⁻¹ * iteratedDeriv 5 hs 0)
    have hsum := hmain.add h5
    apply hsum.congr'
    · filter_upwards [] with ε
      dsimp only [hs, H₃, H₄]
      norm_num [Finset.sum_Icc_succ_top]
      ring
    · rfl

/-- Helper for `exists_localForwardInvariantSlowCurve`: invariance of a graph with a
cubic-quartic fifth-order approximation forces the four transverse coefficient equations. -/
private theorem slowCurveInvariantGraph_coefficientEquations
    (p h : ℝ → ℝ) (P₃ H₃ P₄ H₄ : ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')))
    (h_pJet :
      (fun ε ↦ p ε - (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet :
      (fun ε ↦ h ε - (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5)) :
    3 * H₃ - 5 * P₃ + 174 = 0 ∧
      8 - H₃ = 0 ∧
      3 * H₄ - 5 * P₄ - 9 = 0 ∧
      H₄ = 0 := by
  let p₀ : ℝ → ℝ := fun ε ↦ 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + H₃ * ε ^ 3 + H₄ * ε ^ 4
  let x : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let x₀ : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p₀ ε, h₀ ε)
  let y : ℝ → ℝ × ℝ × ℝ := fun ε ↦ stateMap (x ε)
  let y₀ : ℝ → ℝ × ℝ × ℝ := fun ε ↦ stateMap (x₀ ε)
  have hpDiff :
      (fun ε ↦ p ε - p₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using h_pJet
  have hhDiff :
      (fun ε ↦ h ε - h₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using h_hJet
  have hpowFiveTendsto : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
      have hp₀Continuous : ContinuousAt p₀ 0 := by
        dsimp only [p₀]
        fun_prop
      convert hp₀Continuous.tendsto using 1
      norm_num [p₀]
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFiveTendsto).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
      have hh₀Continuous : ContinuousAt h₀ 0 := by
        dsimp only [h₀]
        fun_prop
      convert hh₀Continuous.tendsto using 1
      norm_num [h₀]
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFiveTendsto).add hh₀Tendsto
  have hxTendsto :
      Tendsto x (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hx₀Analytic : AnalyticAt ℝ x₀ 0 := by
    dsimp only [x₀, p₀, h₀]
    fun_prop
  have hx₀Base : x₀ 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    norm_num [x₀, p₀, h₀]
  have hx₀Tendsto :
      Tendsto x₀ (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    rw [← hx₀Base]
    exact hx₀Analytic.continuousAt.tendsto
  have hpathDiff :
      (fun ε ↦ x ε - x₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have hzero :
        (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
    simpa [x, x₀] using hzero.prod_left (hpDiff.prod_left hhDiff)
  have hstateDiff :
      (fun ε ↦ y ε - y₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have houter := stateMapAnalytic.hasStrictFDerivAt.isBigO_sub
    have hpairs :
        Tendsto (fun ε ↦ (x ε, x₀ ε)) (𝓝 0)
          (𝓝 (((0, 2, 1), (0, 2, 1)) :
            (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))) := by
      simpa only [nhds_prod_eq] using hxTendsto.prodMk hx₀Tendsto
    have hcomposed := houter.comp_tendsto hpairs
    have hcomposed' :
        (fun ε ↦ y ε - y₀ ε) =O[𝓝 0] (fun ε ↦ x ε - x₀ ε) := by
      simpa only [y, y₀, Function.comp_def] using hcomposed
    exact hcomposed'.trans hpathDiff
  have hscaleDiff :
      (fun ε ↦ (y ε).1 - (y₀ ε).1) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    exact hstateDiff.prod_left_fst
  have hshapeDiff :
      (fun ε ↦ (y ε).2.1 - (y₀ ε).2.1) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    exact hstateDiff.prod_left_snd.prod_left_fst
  have hhighDiff :
      (fun ε ↦ (y ε).2.2 - (y₀ ε).2.2) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    exact hstateDiff.prod_left_snd.prod_left_snd
  have hy₀Analytic : AnalyticAt ℝ y₀ 0 := by
    have houter := stateMapAnalytic
    rw [← hx₀Base] at houter
    simpa only [y₀, Function.comp_def] using houter.comp hx₀Analytic
  have hy₀Base : y₀ 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    dsimp only [y₀]
    rw [hx₀Base, stateMap_base]
  have hyTendsto :
      Tendsto y (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    have hcomposed := stateMapAnalytic.continuousAt.tendsto.comp hxTendsto
    simpa only [y, Function.comp_def, stateMap_base] using hcomposed
  have hyScaleTendsto : Tendsto (fun ε ↦ (y ε).1) (𝓝 0) (𝓝 0) := by
    have hproduct := hyTendsto
    rw [nhds_prod_eq] at hproduct
    exact hproduct.fst
  have hy₀ScaleTendsto : Tendsto (fun ε ↦ (y₀ ε).1) (𝓝 0) (𝓝 0) := by
    have hy₀Tendsto :
        Tendsto y₀ (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
      rw [← hy₀Base]
      exact hy₀Analytic.continuousAt.tendsto
    rw [nhds_prod_eq] at hy₀Tendsto
    exact hy₀Tendsto.fst
  have hy₀ScaleOrder :
      (fun ε ↦ (y₀ ε).1) =O[𝓝 0] (fun ε : ℝ ↦ ε) := by
    have hscaleAnalytic : AnalyticAt ℝ (fun ε ↦ (y₀ ε).1) 0 :=
      analyticAt_fst.comp hy₀Analytic
    have horder := hscaleAnalytic.differentiableAt.isBigO_sub
    simpa [y₀, x₀, p₀, h₀, stateMap_base] using horder
  have honeLtFive : 1 < 5 := by
    norm_num
  have hpowFiveOrder :
      (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0] (fun ε : ℝ ↦ ε) :=
    (Asymptotics.isLittleO_pow_id honeLtFive).isBigO
  have hyScaleOrder :
      (fun ε ↦ (y ε).1) =O[𝓝 0] (fun ε : ℝ ↦ ε) := by
    have hsum := (hscaleDiff.trans hpowFiveOrder).add hy₀ScaleOrder
    refine hsum.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [] with ε
    ring
  have hpUpdatedDiff :
      (fun ε ↦ p ((y ε).1) - p₀ ((y ε).1)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have hcomposed := hpDiff.comp_tendsto hyScaleTendsto
    have hscalePower := hyScaleOrder.pow 5
    exact hcomposed.trans hscalePower
  have hhUpdatedDiff :
      (fun ε ↦ h ((y ε).1) - h₀ ((y ε).1)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have hcomposed := hhDiff.comp_tendsto hyScaleTendsto
    have hscalePower := hyScaleOrder.pow 5
    exact hcomposed.trans hscalePower
  have hp₀Analytic : AnalyticAt ℝ p₀ 0 := by
    dsimp only [p₀]
    fun_prop
  have hh₀Analytic : AnalyticAt ℝ h₀ 0 := by
    dsimp only [h₀]
    fun_prop
  have hp₀UpdatedDiff :
      (fun ε ↦ p₀ ((y ε).1) - p₀ ((y₀ ε).1)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have houter := hp₀Analytic.hasStrictFDerivAt.isBigO_sub
    have hpairs :
        Tendsto (fun ε ↦ ((y ε).1, (y₀ ε).1)) (𝓝 0) (𝓝 (0, 0)) := by
      simpa only [nhds_prod_eq] using hyScaleTendsto.prodMk hy₀ScaleTendsto
    have hcomposed := houter.comp_tendsto hpairs
    have hcomposed' :
        (fun ε ↦ p₀ ((y ε).1) - p₀ ((y₀ ε).1)) =O[𝓝 0]
          (fun ε ↦ (y ε).1 - (y₀ ε).1) := by
      simpa only [Function.comp_def] using hcomposed
    exact hcomposed'.trans hscaleDiff
  have hh₀UpdatedDiff :
      (fun ε ↦ h₀ ((y ε).1) - h₀ ((y₀ ε).1)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have houter := hh₀Analytic.hasStrictFDerivAt.isBigO_sub
    have hpairs :
        Tendsto (fun ε ↦ ((y ε).1, (y₀ ε).1)) (𝓝 0) (𝓝 (0, 0)) := by
      simpa only [nhds_prod_eq] using hyScaleTendsto.prodMk hy₀ScaleTendsto
    have hcomposed := houter.comp_tendsto hpairs
    have hcomposed' :
        (fun ε ↦ h₀ ((y ε).1) - h₀ ((y₀ ε).1)) =O[𝓝 0]
          (fun ε ↦ (y ε).1 - (y₀ ε).1) := by
      simpa only [Function.comp_def] using hcomposed
    exact hcomposed'.trans hscaleDiff
  have hactualPInvariant :
      (fun ε ↦ (y ε).2.1) =ᶠ[𝓝 0] (fun ε ↦ p ((y ε).1)) := by
    filter_upwards [h_invariant] with ε hε
    have hcomponent := congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.1) hε
    simpa only [x, y] using hcomponent
  have hactualHInvariant :
      (fun ε ↦ (y ε).2.2) =ᶠ[𝓝 0] (fun ε ↦ h ((y ε).1)) := by
    filter_upwards [h_invariant] with ε hε
    have hcomponent := congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.2) hε
    simpa only [x, y] using hcomponent
  have hpDefectOrder :
      (fun ε ↦ (y₀ ε).2.1 - p₀ ((y₀ ε).1)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have hsum := ((hshapeDiff.neg_left.add hpUpdatedDiff).add hp₀UpdatedDiff)
    refine hsum.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hactualPInvariant] with ε hε
    rw [hε]
    ring
  have hhDefectOrder :
      (fun ε ↦ (y₀ ε).2.2 - h₀ ((y₀ ε).1)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have hsum := ((hhighDiff.neg_left.add hhUpdatedDiff).add hh₀UpdatedDiff)
    refine hsum.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hactualHInvariant] with ε hε
    rw [hε]
    ring
  have hpDefectAnalytic :
      AnalyticAt ℝ (fun ε ↦ (y₀ ε).2.1 - p₀ ((y₀ ε).1)) 0 := by
    have hshape := analyticAt_fst.comp (analyticAt_snd.comp hy₀Analytic)
    have hscale : AnalyticAt ℝ (fun ε ↦ (y₀ ε).1) 0 := by
      simpa only [Function.comp_def] using analyticAt_fst.comp hy₀Analytic
    have hp₀AtScale : AnalyticAt ℝ p₀ ((y₀ 0).1) := by
      simpa only [hy₀Base] using hp₀Analytic
    have hcomposition : AnalyticAt ℝ (fun ε ↦ p₀ ((y₀ ε).1)) 0 := by
      simpa only [Function.comp_def] using
        hp₀AtScale.comp (f := fun ε : ℝ ↦ (y₀ ε).1) hscale
    exact hshape.sub hcomposition
  have hhDefectAnalytic :
      AnalyticAt ℝ (fun ε ↦ (y₀ ε).2.2 - h₀ ((y₀ ε).1)) 0 := by
    have hhigh := analyticAt_snd.comp (analyticAt_snd.comp hy₀Analytic)
    have hscale : AnalyticAt ℝ (fun ε ↦ (y₀ ε).1) 0 := by
      simpa only [Function.comp_def] using analyticAt_fst.comp hy₀Analytic
    have hh₀AtScale : AnalyticAt ℝ h₀ ((y₀ 0).1) := by
      simpa only [hy₀Base] using hh₀Analytic
    have hcomposition : AnalyticAt ℝ (fun ε ↦ h₀ ((y₀ ε).1)) 0 := by
      simpa only [Function.comp_def] using
        hh₀AtScale.comp (f := fun ε : ℝ ↦ (y₀ ε).1) hscale
    exact hhigh.sub hcomposition
  have hpDefectJetZero :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε ↦ (y₀ ε).2.1 - p₀ ((y₀ ε).1)) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ ↦ 0) 0 := by
    apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
    · exact hpDefectAnalytic.contDiffAt
    · fun_prop
    · simpa only [zero_add, sub_zero, Nat.reduceAdd] using hpDefectOrder
  have hhDefectJetZero :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε ↦ (y₀ ε).2.2 - h₀ ((y₀ ε).1)) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ ↦ 0) 0 := by
    apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
    · exact hhDefectAnalytic.contDiffAt
    · fun_prop
    · simpa only [zero_add, sub_zero, Nat.reduceAdd] using hhDefectOrder
  have hpPolynomialJetZero :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦
            ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3 +
              ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ ↦ 0) 0 := by
    rw [← weightedTransversePDefectJet_via_scaleStationarity P₃ H₃ P₄ H₄]
    simpa only [y₀, x₀, p₀, h₀, graphJetPath_apply] using hpDefectJetZero
  have hhPolynomialJetZero :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3 - H₄ * ε ^ 4) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ ↦ 0) 0 := by
    rw [← weightedTransverseHDefectJet_via_scaleStationarity P₃ H₃ P₄ H₄]
    simpa only [y₀, x₀, p₀, h₀, graphJetPath_apply] using hhDefectJetZero
  have hpCubic :=
    (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 4
      (fun ε : ℝ ↦
        ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3 +
          ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4)
      (fun _ : ℝ ↦ 0) 0 0).mp hpPolynomialJetZero (3 : Fin 5)
  have hpQuartic :=
    (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 4
      (fun ε : ℝ ↦
        ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3 +
          ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4)
      (fun _ : ℝ ↦ 0) 0 0).mp hpPolynomialJetZero (4 : Fin 5)
  have hhCubic :=
    (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 4
      (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3 - H₄ * ε ^ 4)
      (fun _ : ℝ ↦ 0) 0 0).mp hhPolynomialJetZero (3 : Fin 5)
  have hhQuartic :=
    (FiniteTaylorJet.ofFunction_eq_iff_iteratedDeriv_eq 4
      (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3 - H₄ * ε ^ 4)
      (fun _ : ℝ ↦ 0) 0 0).mp hhPolynomialJetZero (4 : Fin 5)
  have hpPolynomialSplit :
      (fun ε : ℝ ↦
        ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3 +
          ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) =
        (fun ε : ℝ ↦ ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3) +
          (fun ε : ℝ ↦ ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) :=
    rfl
  have hhPolynomialSplit :
      (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3 - H₄ * ε ^ 4) =
        (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3) -
          (fun ε : ℝ ↦ H₄ * ε ^ 4) :=
    rfl
  have hpCubicLeft : ContDiffAt ℝ 3
      (fun ε : ℝ ↦ ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3) 0 := by
    fun_prop
  have hpCubicRight : ContDiffAt ℝ 3
      (fun ε : ℝ ↦ ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) 0 := by
    fun_prop
  have hpQuarticLeft : ContDiffAt ℝ 4
      (fun ε : ℝ ↦ ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3) 0 := by
    fun_prop
  have hpQuarticRight : ContDiffAt ℝ 4
      (fun ε : ℝ ↦ ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) 0 := by
    fun_prop
  have hhCubicLeft : ContDiffAt ℝ 3
      (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3) 0 := by
    fun_prop
  have hhCubicRight : ContDiffAt ℝ 3
      (fun ε : ℝ ↦ H₄ * ε ^ 4) 0 := by
    fun_prop
  have hhQuarticLeft : ContDiffAt ℝ 4
      (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3) 0 := by
    fun_prop
  have hhQuarticRight : ContDiffAt ℝ 4
      (fun ε : ℝ ↦ H₄ * ε ^ 4) 0 := by
    fun_prop
  norm_num at hpCubic hpQuartic hhCubic hhQuartic
  rw [hpPolynomialSplit, iteratedDeriv_add hpCubicLeft hpCubicRight] at hpCubic
  rw [hpPolynomialSplit, iteratedDeriv_add hpQuarticLeft hpQuarticRight] at hpQuartic
  rw [hhPolynomialSplit, iteratedDeriv_sub hhCubicLeft hhCubicRight] at hhCubic
  rw [hhPolynomialSplit, iteratedDeriv_sub hhQuarticLeft hhQuarticRight] at hhQuartic
  norm_num [iteratedDeriv_const_mul_field, iteratedDeriv_pow] at hpCubic hpQuartic
  norm_num [iteratedDeriv_const_mul_field, iteratedDeriv_pow] at hhCubic hhQuartic
  constructor
  · linarith
  · constructor
    · linarith
    · constructor
      · linarith
      · linarith

/-- The canonical two-leg state map has a locally forward-invariant `C^7` graph
through `(0, 2, 1)`, tangent to the signed-scale axis, with the displayed
transverse jets and signed-scale recurrence. -/
theorem exists_localForwardInvariantSlowCurve :
    ∃ p h : ℝ → ℝ,
      ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0 ∧
        (p 0, h 0) = (2, 1) ∧
          HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 ∧
            (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
              (fun ε ↦
                let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
                (ε', p ε', h ε')) ∧
              (fun ε : ℝ ↦
                p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
                (fun ε : ℝ ↦ ε ^ 5) ∧
                (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
                  (fun ε : ℝ ↦ ε ^ 5) ∧
                  (fun ε : ℝ ↦
                    (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1 -
                      (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
                    (fun ε : ℝ ↦ ε ^ 6) := by
  obtain ⟨p, h, hcont, hbase, htangent, hinvariant⟩ :=
    exists_slowCurveGraphCore
  have htwoSeven : (2 : WithTop ℕ∞) ≤ 7 := by
    norm_num
  have hfiveSeven : (5 : WithTop ℕ∞) ≤ 7 := by
    norm_num
  have hcontTwo : ContDiffAt ℝ 2 (fun ε ↦ (p ε, h ε)) 0 :=
    hcont.of_le htwoSeven
  have hcontFive : ContDiffAt ℝ 5 (fun ε ↦ (p ε, h ε)) 0 :=
    hcont.of_le hfiveSeven
  obtain ⟨hpFirst, hhFirst, hpSecond, hhSecond⟩ :=
    slowCurveInvariantGraph_secondOrderFlat p h hcontTwo hbase htangent hinvariant
  obtain ⟨P₃, H₃, P₄, H₄, hpJet, hhJet⟩ :=
    exists_slowCurveTaylorCoefficients p h hcontFive hbase
      hpFirst hhFirst hpSecond hhSecond
  obtain ⟨hshapeCubic, hhighCubic, hshapeQuartic, hhighQuartic⟩ :=
    slowCurveInvariantGraph_coefficientEquations
      p h P₃ H₃ P₄ H₄ hinvariant hpJet hhJet
  have hH₃ : H₃ = 8 := by
    linarith
  have hP₃ : P₃ = 198 / 5 := by
    linarith
  have hH₄ : H₄ = 0 := by
    linarith
  have hP₄ : P₄ = -9 / 5 := by
    linarith
  have hpTarget :
      (fun ε : ℝ ↦
        p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    refine hpJet.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [] with ε
    rw [hP₃, hP₄]
    ring
  have hhTarget :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    refine hhJet.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [] with ε
    rw [hH₃, hH₄]
    ring
  have hrecurrence := slowGraphSignedRecurrence p h hpTarget hhTarget
  have hstateRecurrence :
      (fun ε : ℝ ↦
        (stateMap (ε, p ε, h ε)).1 -
          (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 6) := by
    simpa only [stateMap, signedEpsilon] using hrecurrence
  exact ⟨p, h, hcont, hbase, htangent, hinvariant,
    hpTarget, hhTarget, hstateRecurrence⟩

end

end DFP.TwoLeg
