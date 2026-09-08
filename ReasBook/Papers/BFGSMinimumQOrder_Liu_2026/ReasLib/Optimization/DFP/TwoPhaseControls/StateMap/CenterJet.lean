module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap.Linearization
public import ReasLib.Optimization.DFP.TwoPhaseControls.TransverseJet
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.PureScaleJets

public section

namespace DFP.TwoLeg

/-- Helper for `stateMapTransverseSecondDerivAlongTangentGraph`: the transverse
state map has zero acceleration along the pure signed-scale axis at the base. -/
private lemma stateMapTransverse_pureScale_secondDeriv :
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
    rw [show highPolynomial = fun ε : ℝ ↦ 1 + 8 * ε ^ 3 from rfl,
      iteratedDeriv_const_add (n := 2) htwoPos]
    simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow]
    norm_num
  have hshapeSecond : iteratedDeriv 2 shape 0 = 0 := hshape.trans hshapePolynomialSecond
  have hhighSecond : iteratedDeriv 2 high 0 = 0 := hhigh.trans hhighPolynomialSecond
  have hscalePath : ContDiffAt ℝ 2
      (fun ε : ℝ ↦ ((ε, 2, 1) : ℝ × ℝ × ℝ)) 0 := by
    fun_prop
  have hstate := stateMapAnalytic.contDiffAt.comp 0 hscalePath
  have hshapeContDiff : ContDiffAt ℝ 2 shape 0 := by
    simpa only [shape, Function.comp_apply] using hstate.snd.fst
  have hhighContDiff : ContDiffAt ℝ 2 high 0 := by
    simpa only [high, Function.comp_apply] using hstate.snd.snd
  rw [show (fun ε : ℝ ↦ (stateMap (ε, 2, 1)).2) =
      (fun ε ↦ (shape ε, high ε)) from rfl,
    iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_prodMk hshapeContDiff hhighContDiff le_rfl]
  change (iteratedDeriv 2 shape 0, iteratedDeriv 2 high 0) = (0, 0)
  rw [hshapeSecond, hhighSecond]

/-- Helper for `stateMapTransverseSecondDerivAlongTangentGraph`: the second
derivative of a graph path packages the two transverse scalar accelerations. -/
private lemma graphPath_secondDeriv (p h : ℝ → ℝ)
    (h_contDiff : ContDiffAt ℝ 2 (fun ε ↦ (p ε, h ε)) 0) :
    iteratedDeriv 2 (fun ε ↦ ((ε, p ε, h ε) : ℝ × ℝ × ℝ)) 0 =
      (0, iteratedDeriv 2 p 0, iteratedDeriv 2 h 0) := by
  have hp : ContDiffAt ℝ 2 p 0 := h_contDiff.fst
  have hh : ContDiffAt ℝ 2 h 0 := h_contDiff.snd
  rw [show (fun ε ↦ ((ε, p ε, h ε) : ℝ × ℝ × ℝ)) =
      (fun ε ↦ (id ε, (p ε, h ε))) from rfl,
    iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_prodMk contDiffAt_id (hp.prodMk hh) le_rfl,
    iteratedFDeriv_prodMk hp hh le_rfl]
  change (iteratedDeriv 2 id 0, iteratedDeriv 2 p 0, iteratedDeriv 2 h 0) =
    (0, iteratedDeriv 2 p 0, iteratedDeriv 2 h 0)
  norm_num [iteratedDeriv_id]

/-- Along a twice continuously differentiable graph through `(0, 2, 1)` tangent to
the signed-scale axis, the transverse state-map acceleration is the stable linear
response to the graph's transverse acceleration. -/
theorem stateMapTransverseSecondDerivAlongTangentGraph (p h : ℝ → ℝ)
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
    have htwo : HasDerivAt (fun _ : ℝ ↦ (2 : ℝ)) 0 0 := hasDerivAt_const 0 2
    have hone : HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 0 := hasDerivAt_const 0 1
    have hderiv := (hasDerivAt_id 0).prodMk (htwo.prodMk hone)
    simpa only [scalePath, id_eq] using hderiv.deriv
  have hconstantGraph : ContDiffAt ℝ 2 (fun _ : ℝ ↦ ((2, 1) : ℝ × ℝ)) 0 := by
    fun_prop
  have hscalePathSecond : iteratedDeriv 2 scalePath 0 = 0 := by
    change iteratedDeriv 2 scalePath 0 = ((0, 0, 0) : ℝ × ℝ × ℝ)
    simpa [scalePath, iteratedDeriv_const] using
      graphPath_secondDeriv (fun _ ↦ 2) (fun _ ↦ 1) hconstantGraph
  have hscaleComposition := iteratedDeriv_vcomp_two
    (g := transverse) (f := scalePath)
    ((analyticAt_snd.comp stateMapAnalytic).contDiffAt :
      ContDiffAt ℝ 2 transverse (scalePath 0)) hscalePathContDiff
  have hscaleHessian :
      iteratedFDeriv ℝ 2 transverse (0, 2, 1)
          (fun _ ↦ ((1, 0, 0) : ℝ × ℝ × ℝ)) = 0 := by
    change iteratedDeriv 2 (fun ε : ℝ ↦ (stateMap (ε, 2, 1)).2) 0 = _
      at hscaleComposition
    rw [stateMapTransverse_pureScale_secondDeriv, hscalePathDeriv,
      hscalePathSecond, map_zero, add_zero] at hscaleComposition
    change iteratedFDeriv ℝ 2 transverse (0, 2, 1)
      (fun _ ↦ ((1, 0, 0) : ℝ × ℝ × ℝ)) = (0, 0)
    simpa only [scalePath] using hscaleComposition.symm
  have htransverseFDeriv (v : ℝ × ℝ × ℝ) :
      fderiv ℝ transverse (0, 2, 1) v =
        ((-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0) := by
    have hcomponent := stateMapAnalytic.differentiableAt.hasFDerivAt.snd
    rw [show transverse = fun x ↦ (stateMap x).2 from rfl, hcomponent.fderiv]
    change (fderiv ℝ stateMap (0, 2, 1) v).2 =
      ((-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2, 0)
    rw [stateMap_fderiv_apply]
  have hcomposition := iteratedDeriv_vcomp_two htransverseContDiff hpathContDiff
  rw [hpathBase, hpathDeriv, hscaleHessian, zero_add,
    graphPath_secondDeriv p h h_contDiff, htransverseFDeriv] at hcomposition
  simpa only [path, transverse, Function.comp_def] using hcomposition

end DFP.TwoLeg
