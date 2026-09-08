module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.Assembly
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.MixedFlatPath

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.TwoLeg

private theorem weightedPath_mixed_isBigO
    (outer : (ℝ × ℝ × ℝ) → ℝ)
    (houter : AnalyticAt ℝ outer (0, 2, 1))
    (P₃ H₃ P₄ H₄ : ℝ)
    (hcross :
      iteratedFDeriv ℝ 2 outer (0, 2, 1)
        ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, P₃, H₃)] = 0) :
    (fun ε : ℝ =>
      outer
          (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
            1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) -
        outer (ε, 2, 1) -
        outer
          (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
            1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) +
        outer (0, 2, 1)) =O[𝓝 0] (fun ε : ℝ => ε ^ 5) := by
  have hmixed := FiniteTaylorJet.analytic_mixed_cubic_quartic_isBigO
    outer ((0, 2, 1) : ℝ × ℝ × ℝ) (1, 0, 0) (0, P₃, H₃) (0, P₄, H₄)
    houter hcross
  have hfull (ε : ℝ) :
      ((0, 2, 1) : ℝ × ℝ × ℝ) +
          (ε • (1, 0, 0) +
            (ε ^ 3 • (0, P₃, H₃) + ε ^ 4 • (0, P₄, H₄))) =
        (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) := by
    ext <;> norm_num <;> ring
  have hscale (ε : ℝ) :
      ((0, 2, 1) : ℝ × ℝ × ℝ) + ε • (1, 0, 0) = (ε, 2, 1) := by
    ext <;> norm_num
  have hflat (ε : ℝ) :
      ((0, 2, 1) : ℝ × ℝ × ℝ) +
          (ε ^ 3 • (0, P₃, H₃) + ε ^ 4 • (0, P₄, H₄)) =
        (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) := by
    ext <;> norm_num <;> ring
  refine hmixed.congr_left ?_
  intro ε
  dsimp only
  rw [hfull, hscale, hflat]

/-- The weighted normalized-radius jet follows from the scale-axis jet once the
single quadratic scale/transverse cross derivative is known to vanish. -/
theorem weightedNormalizedRadiusJet_of_scale_and_cross
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => radiusFactor ε 2 1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 1 - (300 / 18) * ε ^ 3 + (54 / 18) * ε ^ 4) 0)
    (hcross :
      iteratedFDeriv ℝ 2
          (fun x : ℝ × ℝ × ℝ => radiusFactor x.1 x.2.1 x.2.2)
          (0, 2, 1) ![(1, 0, 0), (0, P₃, H₃)] = 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          radiusFactor ε
            (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
            (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
            ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0 := by
  refine weightedNormalizedRadiusJet_of_scale_and_mixed P₃ H₃ P₄ H₄ hscale ?_
  let outer : ℝ × ℝ × ℝ → ℝ := fun x => radiusFactor x.1 x.2.1 x.2.2
  have hcross' :
      iteratedFDeriv ℝ 2 outer (0, 2, 1)
        ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, P₃, H₃)] = 0 := by
    simpa only [outer] using hcross
  have hmixed := weightedPath_mixed_isBigO outer analyticAt_radiusFactor
    P₃ H₃ P₄ H₄ hcross'
  refine hmixed.congr_left ?_
  intro ε
  dsimp only [outer]
  rw [radiusFactor_base]
  ring

/-- The weighted transverse-shape jet follows from the scale-axis jet once the
single quadratic scale/transverse cross derivative is known to vanish. -/
theorem weightedTransversePJet_of_scale_and_cross
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => (stateMap (ε, 2, 1)).2.1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 2 + (348 / 9) * ε ^ 3 - (18 / 9) * ε ^ 4) 0)
    (hcross :
      iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ => (stateMap x).2.1)
          (0, 2, 1) ![(1, 0, 0), (0, P₃, H₃)] = 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
            ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) 0 := by
  refine weightedTransversePJet_of_scale_and_mixed P₃ H₃ P₄ H₄ hscale ?_
  let outer : ℝ × ℝ × ℝ → ℝ := fun x => (stateMap x).2.1
  have houter : AnalyticAt ℝ outer (0, 2, 1) := by
    exact analyticAt_fst.comp (analyticAt_snd.comp stateMapAnalytic)
  have hcross' :
      iteratedFDeriv ℝ 2 outer (0, 2, 1)
        ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, P₃, H₃)] = 0 := by
    simpa only [outer] using hcross
  have hmixed := weightedPath_mixed_isBigO outer houter P₃ H₃ P₄ H₄ hcross'
  refine hmixed.congr_left ?_
  intro ε
  dsimp only [outer]
  rw [stateMap_base]
  ring

/-- The weighted transverse-high jet follows from the scale-axis jet once the
single quadratic scale/transverse cross derivative is known to vanish. -/
theorem weightedTransverseHJet_of_scale_and_cross
    (P₃ H₃ P₄ H₄ : ℝ)
    (hscale :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => (stateMap (ε, 2, 1)).2.2) 0 =
        FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0)
    (hcross :
      iteratedFDeriv ℝ 2 (fun x : ℝ × ℝ × ℝ => (stateMap x).2.2)
          (0, 2, 1) ![(1, 0, 0), (0, P₃, H₃)] = 0) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          (stateMap
            (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun ε : ℝ => 1 + 8 * ε ^ 3) 0 := by
  refine weightedTransverseHJet_of_scale_and_mixed P₃ H₃ P₄ H₄ hscale ?_
  let outer : ℝ × ℝ × ℝ → ℝ := fun x => (stateMap x).2.2
  have houter : AnalyticAt ℝ outer (0, 2, 1) := by
    exact analyticAt_snd.comp (analyticAt_snd.comp stateMapAnalytic)
  have hcross' :
      iteratedFDeriv ℝ 2 outer (0, 2, 1)
        ![((1, 0, 0) : ℝ × ℝ × ℝ), (0, P₃, H₃)] = 0 := by
    simpa only [outer] using hcross
  have hmixed := weightedPath_mixed_isBigO outer houter P₃ H₃ P₄ H₄ hcross'
  refine hmixed.congr_left ?_
  intro ε
  dsimp only [outer]
  rw [stateMap_base]
  ring

end DFP.TwoLeg
