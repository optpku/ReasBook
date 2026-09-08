module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap.CenterJet
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- A twice continuously differentiable local graph through `(0, 2, 1)` that is
tangent to the signed-scale axis and invariant under the two-leg state map is flat
through second order in both transverse coordinates. -/
theorem invariantSlowGraphSecondOrderFlatness (p h : ℝ → ℝ)
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
  have hgraphTangent : HasFDerivAt graph (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 := by
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
    simp
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
    stateMapTransverseSecondDerivAlongTangentGraph p h h_contDiff h_base h_tangent
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

end DFP.TwoLeg
