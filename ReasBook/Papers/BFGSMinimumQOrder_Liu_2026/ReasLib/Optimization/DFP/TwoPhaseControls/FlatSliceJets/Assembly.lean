module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.SplitComparison
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-!
Conditional assembly lemmas for the weighted radius and transverse jets.

The parameter-only contributions are supplied by `FlatSliceJets`.  Each theorem
below reduces the corresponding full weighted jet to two scale-only facts:

* the scale-axis jet;
* an order-five bound for the mixed interaction with the flat parameter slice.

This keeps the reusable jet algebra independent of the explicit rational
expansions used to discharge those two remaining hypotheses.
-/

private theorem analyticAt_weightedPath
    (outer : (ℝ × ℝ × ℝ) → ℝ)
    (houter : AnalyticAt ℝ outer (0, 2, 1))
    (P₃ H₃ P₄ H₄ : ℝ) :
    AnalyticAt ℝ
      (fun ε : ℝ => outer
        (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 := by
  let path : ℝ → ℝ × ℝ × ℝ := fun ε =>
    (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
      1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)
  have hpath : AnalyticAt ℝ path 0 := by
    dsimp only [path]
    fun_prop
  have houter' : AnalyticAt ℝ outer (path 0) := by
    simpa [path] using houter
  simpa [path, Function.comp_def] using houter'.comp hpath

private theorem analyticAt_scalePath
    (outer : (ℝ × ℝ × ℝ) → ℝ)
    (houter : AnalyticAt ℝ outer (0, 2, 1)) :
    AnalyticAt ℝ (fun ε : ℝ => outer (ε, 2, 1)) 0 := by
  let path : ℝ → ℝ × ℝ × ℝ := fun ε => (ε, 2, 1)
  have hpath : AnalyticAt ℝ path 0 := by
    dsimp only [path]
    fun_prop
  have houter' : AnalyticAt ℝ outer (path 0) := by
    simpa [path] using houter
  simpa [path, Function.comp_def] using houter'.comp hpath

private theorem analyticAt_flatTransversePath
    (outer : (ℝ × ℝ × ℝ) → ℝ)
    (houter : AnalyticAt ℝ outer (0, 2, 1))
    (P₃ H₃ P₄ H₄ : ℝ) :
    AnalyticAt ℝ
      (fun ε : ℝ => outer
        (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 := by
  let path : ℝ → ℝ × ℝ × ℝ := fun ε =>
    (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
      1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)
  have hpath : AnalyticAt ℝ path 0 := by
    dsimp only [path]
    fun_prop
  have houter' : AnalyticAt ℝ outer (path 0) := by
    simpa [path] using houter
  simpa [path, Function.comp_def] using houter'.comp hpath

/-- Assemble the weighted normalized-radius jet from its scale-axis jet and an
order-five mixed-interaction estimate. -/
theorem weightedNormalizedRadiusJet_of_scale_and_mixed
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => radiusFactor ε 2 1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 1 - (300 / 18) * ε ^ 3 + (54 / 18) * ε ^ 4) 0)
    (hmixed :
      (fun ε : ℝ =>
        radiusFactor ε
            (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
            (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) -
          (radiusFactor ε 2 1 +
            radiusFactor 0
              (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
              (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) - 1)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5)) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          radiusFactor ε
            (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
            (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
            ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0 := by
  let p : ℝ → ℝ := fun ε => 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4
  let h : ℝ → ℝ := fun ε => 1 + H₃ * ε ^ 3 + H₄ * ε ^ 4
  let outer : ℝ × ℝ × ℝ → ℝ := fun x => radiusFactor x.1 x.2.1 x.2.2
  let fullPath : ℝ → ℝ × ℝ × ℝ := fun ε => (ε, p ε, h ε)
  let scalePath : ℝ → ℝ × ℝ × ℝ := fun ε => (ε, 2, 1)
  let flatPath : ℝ → ℝ × ℝ × ℝ := fun ε => (0, p ε, h ε)
  let full : ℝ → ℝ := fun ε => outer (fullPath ε)
  let scale : ℝ → ℝ := fun ε => outer (scalePath ε)
  let flat : ℝ → ℝ := fun ε => outer (flatPath ε)
  let base : ℝ → ℝ := fun _ => 1
  let scalePoly : ℝ → ℝ :=
    fun ε => 1 - (300 / 18) * ε ^ 3 + (54 / 18) * ε ^ 4
  let flatPoly : ℝ → ℝ := fun ε =>
    1 + ((5 * P₃ + 6 * H₃) / 18) * ε ^ 3 +
      ((5 * P₄ + 6 * H₄) / 18) * ε ^ 4
  have hfullPath : AnalyticAt ℝ fullPath 0 := by
    dsimp only [fullPath, p, h]
    fun_prop
  have hscalePath : AnalyticAt ℝ scalePath 0 := by
    dsimp only [scalePath]
    fun_prop
  have hflatPath : AnalyticAt ℝ flatPath 0 := by
    dsimp only [flatPath, p, h]
    fun_prop
  have hfullOuter : AnalyticAt ℝ outer (fullPath 0) := by
    simpa [outer, fullPath, p, h] using analyticAt_radiusFactor
  have hscaleOuter : AnalyticAt ℝ outer (scalePath 0) := by
    simpa [outer, scalePath] using analyticAt_radiusFactor
  have hflatOuter : AnalyticAt ℝ outer (flatPath 0) := by
    simpa [outer, flatPath, p, h] using analyticAt_radiusFactor
  have hfull : ContDiffAt ℝ 4 full 0 := by
    simpa [full, Function.comp_def] using (hfullOuter.comp hfullPath).contDiffAt
  have hscale' : ContDiffAt ℝ 4 scale 0 := by
    simpa [scale, Function.comp_def] using (hscaleOuter.comp hscalePath).contDiffAt
  have hflat : ContDiffAt ℝ 4 flat 0 := by
    simpa [flat, Function.comp_def] using (hflatOuter.comp hflatPath).contDiffAt
  have hbase : ContDiffAt ℝ 4 base 0 := by
    dsimp only [base]
    fun_prop
  have hscalePoly : ContDiffAt ℝ 4 scalePoly 0 := by
    dsimp only [scalePoly]
    fun_prop
  have hflatPoly : ContDiffAt ℝ 4 flatPoly 0 := by
    dsimp only [flatPoly]
    fun_prop
  have hsplit := FiniteTaylorJet.ofFunction_split_of_isBigO_succ
    hfull hscale' hflat hbase hscalePoly hflatPoly hbase
    (by simpa only [zero_add, full, scale, flat, base, outer, fullPath,
      scalePath, flatPath, p, h] using hmixed)
    (by simpa only [scale, scalePath, outer, scalePoly] using hscale)
    (by simpa only [flat, flatPath, outer, flatPoly, p, h] using
      weightedZeroScaleNormalizedRadiusJet P₃ H₃ P₄ H₄)
    (by rfl)
  simp only [full, fullPath, outer, p, h] at hsplit
  convert hsplit using 1
  congr 1
  funext ε
  dsimp only [scalePoly, flatPoly, base]
  ring

/-- Assemble the weighted transverse-shape jet from its scale-axis jet and an
order-five mixed-interaction estimate. -/
theorem weightedTransversePJet_of_scale_and_mixed
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => (stateMap (ε, 2, 1)).2.1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4) 0)
    (hmixed :
      (fun ε : ℝ =>
        (stateMap
              (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
                1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1 -
          ((stateMap (ε, 2, 1)).2.1 +
            (stateMap
              (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
                1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1 - 2)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5)) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
            ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) 0 := by
  let outer : ℝ × ℝ × ℝ → ℝ := fun x => (stateMap x).2.1
  have houter : AnalyticAt ℝ outer (0, 2, 1) := by
    exact analyticAt_fst.comp (analyticAt_snd.comp stateMapAnalytic)
  have hfull : ContDiffAt ℝ 4
      (fun ε : ℝ => outer
        (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 :=
    (analyticAt_weightedPath outer houter P₃ H₃ P₄ H₄).contDiffAt
  have hscale' : ContDiffAt ℝ 4 (fun ε : ℝ => outer (ε, 2, 1)) 0 :=
    (analyticAt_scalePath outer houter).contDiffAt
  have hflat : ContDiffAt ℝ 4
      (fun ε : ℝ => outer
        (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 :=
    (analyticAt_flatTransversePath outer houter P₃ H₃ P₄ H₄).contDiffAt
  have hbase : ContDiffAt ℝ 4 (fun _ : ℝ => (2 : ℝ)) 0 := by fun_prop
  have hscalePoly : ContDiffAt ℝ 4
      (fun ε : ℝ => 2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4) 0 := by fun_prop
  have hflatPoly : ContDiffAt ℝ 4
      (fun ε : ℝ => 2 + ((6 * H₃ - P₃) / 9) * ε ^ 3 +
        ((6 * H₄ - P₄) / 9) * ε ^ 4) 0 := by fun_prop
  have hsplit := FiniteTaylorJet.ofFunction_split_of_isBigO_succ
    (f := fun ε : ℝ => outer
      (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
        1 + H₃ * ε ^ 3 + H₄ * ε ^ 4))
    (s := fun ε : ℝ => outer (ε, 2, 1))
    (t := fun ε : ℝ => outer
      (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
        1 + H₃ * ε ^ 3 + H₄ * ε ^ 4))
    (c := fun _ : ℝ => (2 : ℝ))
    (s' := fun ε : ℝ => 2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4)
    (t' := fun ε : ℝ => 2 + ((6 * H₃ - P₃) / 9) * ε ^ 3 +
      ((6 * H₄ - P₄) / 9) * ε ^ 4)
    (c' := fun _ : ℝ => (2 : ℝ))
    hfull hscale' hflat hbase hscalePoly hflatPoly hbase
    (by simpa only [zero_add, outer] using hmixed)
    (by simpa only [outer] using hscale)
    (by simpa only [outer] using weightedZeroScaleTransversePJet P₃ H₃ P₄ H₄)
    rfl
  dsimp only [outer] at hsplit
  convert hsplit using 1
  congr 1
  funext ε
  ring

/-- Assemble the weighted transverse-high jet from its scale-axis jet and an
order-five mixed-interaction estimate. -/
theorem weightedTransverseHJet_of_scale_and_mixed
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => (stateMap (ε, 2, 1)).2.2) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0)
    (hmixed :
      (fun ε : ℝ =>
        (stateMap
              (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
                1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2 -
          ((stateMap (ε, 2, 1)).2.2 +
            (stateMap
              (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
                1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2 - 1)) =O[𝓝 0]
        (fun ε : ℝ => ε ^ 5)) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0 := by
  let outer : ℝ × ℝ × ℝ → ℝ := fun x => (stateMap x).2.2
  have houter : AnalyticAt ℝ outer (0, 2, 1) := by
    exact analyticAt_snd.comp (analyticAt_snd.comp stateMapAnalytic)
  have hfull : ContDiffAt ℝ 4
      (fun ε : ℝ => outer
        (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 :=
    (analyticAt_weightedPath outer houter P₃ H₃ P₄ H₄).contDiffAt
  have hscale' : ContDiffAt ℝ 4 (fun ε : ℝ => outer (ε, 2, 1)) 0 :=
    (analyticAt_scalePath outer houter).contDiffAt
  have hflat : ContDiffAt ℝ 4
      (fun ε : ℝ => outer
        (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 :=
    (analyticAt_flatTransversePath outer houter P₃ H₃ P₄ H₄).contDiffAt
  have hbase : ContDiffAt ℝ 4 (fun _ : ℝ => (1 : ℝ)) 0 := by fun_prop
  have hscalePoly : ContDiffAt ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0 := by fun_prop
  have hsplit := FiniteTaylorJet.ofFunction_split_of_isBigO_succ
    (f := fun ε : ℝ => outer
      (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
        1 + H₃ * ε ^ 3 + H₄ * ε ^ 4))
    (s := fun ε : ℝ => outer (ε, 2, 1))
    (t := fun ε : ℝ => outer
      (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
        1 + H₃ * ε ^ 3 + H₄ * ε ^ 4))
    (c := fun _ : ℝ => (1 : ℝ))
    (s' := fun ε : ℝ => 1 + 8 * ε ^ 3)
    (t' := fun _ : ℝ => (1 : ℝ))
    (c' := fun _ : ℝ => (1 : ℝ))
    hfull hscale' hflat hbase hscalePoly hbase hbase
    (by simpa only [zero_add, outer] using hmixed)
    (by simpa only [outer] using hscale)
    (by simpa only [outer] using weightedZeroScaleTransverseHJet P₃ H₃ P₄ H₄)
    rfl
  dsimp only [outer] at hsplit
  convert hsplit using 1
  congr 1
  funext ε
  ring

end DFP.TwoLeg
