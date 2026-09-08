module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.FlatPath
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap.Linearization

public section

/-!
# Flat transverse slice jets for the two-leg state map

These lemmas isolate the dependence of the weighted radius and transverse jets on the cubic and
quartic graph coefficients.  The scale coordinate is held at zero, so the remaining full graph-jet
proofs only need the pure-scale terms and the absence of mixed terms through order four.
-/

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

private theorem radiusFactor_fderiv_zeroTransverse (u w : ℝ) :
    fderiv ℝ (fun x : ℝ × ℝ × ℝ ↦ radiusFactor x.1 x.2.1 x.2.2)
        (0, 2, 1) (0, u, w) =
      (5 / 18 : ℝ) * u + (1 / 3 : ℝ) * w := by
  let p : ℝ → ℝ := fun t ↦ 2 + t * u
  let h : ℝ → ℝ := fun t ↦ 1 + t * w
  let one : ℝ → ℝ := fun _ ↦ 1
  let two : ℝ → ℝ := fun _ ↦ 2
  let nine : ℝ → ℝ := fun _ ↦ 9
  have hp : HasDerivAt p u 0 := by
    simpa only [p, id_eq, zero_add, one_mul] using
      ((hasDerivAt_id 0).mul_const u).const_add 2
  have hh : HasDerivAt h w 0 := by
    simpa only [h, id_eq, zero_add, one_mul] using
      ((hasDerivAt_id 0).mul_const w).const_add 1
  have hone : HasDerivAt one 0 0 := hasDerivAt_const 0 1
  have htwo : HasDerivAt two 0 0 := hasDerivAt_const 0 2
  have hnine : HasDerivAt nine 0 0 := hasDerivAt_const 0 9
  let numerator := ((nine * h) * p) * (p + one)
  have hnumerator : HasDerivAt numerator (45 * u + 54 * w) 0 := by
    exact (((hnine.mul hh).mul hp).mul (hp.add hone)).congr_deriv
      (g' := 45 * u + 54 * w)
        (by norm_num [numerator, p, h, one, nine]; ring)
  let core := (nine * h) * p + (p + one) ^ 2
  have hcore : HasDerivAt core (15 * u + 18 * w) 0 := by
    exact (((hnine.mul hh).mul hp).add ((hp.add hone).pow 2)).congr_deriv
      (g' := 15 * u + 18 * w) (by norm_num [core, p, h, one, nine]; ring)
  let denominator := two * core
  have hdenominator : HasDerivAt denominator (30 * u + 36 * w) 0 := by
    exact (htwo.mul hcore).congr_deriv (g' := 30 * u + 36 * w)
      (by norm_num [denominator, core, p, h, one, two, nine]; ring)
  have hdenominator_ne : denominator 0 ≠ 0 := by
    norm_num [denominator, core, p, h, one, two, nine]
  let explicit := numerator / denominator
  have hexplicit :
      HasDerivAt explicit ((5 / 18 : ℝ) * u + (1 / 3 : ℝ) * w) 0 := by
    exact (hnumerator.div hdenominator hdenominator_ne).congr_deriv
      (g' := (5 / 18 : ℝ) * u + (1 / 3 : ℝ) * w)
        (by norm_num [explicit, numerator, denominator, core, p, h, one, two, nine]; ring)
  have hp_pos : ∀ᶠ t in 𝓝 0, 0 < p t := by
    apply hp.continuousAt.eventually
    exact Ioi_mem_nhds (by norm_num [p])
  have hh_pos : ∀ᶠ t in 𝓝 0, 0 < h t := by
    apply hh.continuousAt.eventually
    exact Ioi_mem_nhds (by norm_num [h])
  have hradiusLine :
      HasDerivAt (fun t : ℝ ↦ radiusFactor 0 (p t) (h t))
        ((5 / 18 : ℝ) * u + (1 / 3 : ℝ) * w) 0 := by
    apply hexplicit.congr_of_eventuallyEq
    filter_upwards [hp_pos, hh_pos] with t hpt hht
    simpa only [explicit, numerator, denominator, core, p, h, one, two, nine,
      Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Pi.div_apply] using
        radiusFactor_zero (p t) (h t) hpt hht
  have hline :
      HasDerivAt (fun t : ℝ ↦ ((0, p t, h t) : ℝ × ℝ × ℝ)) (0, u, w) 0 := by
    exact (hasDerivAt_const (x := 0) (c := (0 : ℝ))).prodMk (hp.prodMk hh)
  have hfAt : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ radiusFactor x.1 x.2.1 x.2.2)
      (0, p 0, h 0) := by
    simpa [p, h] using analyticAt_radiusFactor
  have hchain := hfAt.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline
  simpa [p, h] using hchain.unique hradiusLine

/-- The zero-scale radius jet contains exactly the part of the weighted radius coefficients that
depends on the cubic and quartic transverse graph coefficients. -/
theorem weightedZeroScaleNormalizedRadiusJet (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          radiusFactor 0
            (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
            (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          1 + ((5 * P₃ + 6 * H₃) / 18) * ε ^ 3 +
            ((5 * P₄ + 6 * H₄) / 18) * ε ^ 4) 0 := by
  let f : ℝ × ℝ × ℝ → ℝ := fun x ↦ radiusFactor x.1 x.2.1 x.2.2
  have hflat := FiniteTaylorJet.ofFunction_comp_cubic_quartic f
    ((0, 2, 1) : ℝ × ℝ × ℝ) (0, P₃, H₃) (0, P₄, H₄)
    analyticAt_radiusFactor
  dsimp only [f] at hflat
  rw [radiusFactor_base, radiusFactor_fderiv_zeroTransverse,
    radiusFactor_fderiv_zeroTransverse] at hflat
  have hpath (ε : ℝ) :
      ((0, 2, 1) : ℝ × ℝ × ℝ) + ε ^ 3 • (0, P₃, H₃) +
          ε ^ 4 • (0, P₄, H₄) =
        (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) := by
    ext <;> norm_num <;> ring
  simp_rw [hpath] at hflat
  convert hflat using 1
  all_goals congr 1
  all_goals funext ε
  all_goals ring

private theorem stateMapP_fderiv_apply (v : ℝ × ℝ × ℝ) :
    fderiv ℝ (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.1) (0, 2, 1) v =
      (-(1 : ℝ) / 9) * v.2.1 + ((2 : ℝ) / 3) * v.2.2 := by
  have hcomponent := stateMapAnalytic.differentiableAt.hasFDerivAt.snd.fst
  rw [hcomponent.fderiv]
  simp [stateMap_fderiv_apply]

private theorem stateMapH_fderiv_apply (v : ℝ × ℝ × ℝ) :
    fderiv ℝ (fun x : ℝ × ℝ × ℝ ↦ (stateMap x).2.2) (0, 2, 1) v = 0 := by
  have hcomponent := stateMapAnalytic.differentiableAt.hasFDerivAt.snd.snd
  rw [hcomponent.fderiv]
  simp [stateMap_fderiv_apply]

/-- The zero-scale updated-shape jet contains exactly the coefficient-dependent part of the
weighted transverse shape jet. -/
theorem weightedZeroScaleTransversePJet (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          (stateMap
            (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          2 + ((6 * H₃ - P₃) / 9) * ε ^ 3 +
            ((6 * H₄ - P₄) / 9) * ε ^ 4) 0 := by
  let f : ℝ × ℝ × ℝ → ℝ := fun x ↦ (stateMap x).2.1
  have hf : AnalyticAt ℝ f (0, 2, 1) := by
    exact analyticAt_fst.comp (analyticAt_snd.comp stateMapAnalytic)
  have hflat := FiniteTaylorJet.ofFunction_comp_cubic_quartic f
    ((0, 2, 1) : ℝ × ℝ × ℝ) (0, P₃, H₃) (0, P₄, H₄) hf
  dsimp only [f] at hflat
  rw [stateMap_base, stateMapP_fderiv_apply, stateMapP_fderiv_apply] at hflat
  have hpath (ε : ℝ) :
      ((0, 2, 1) : ℝ × ℝ × ℝ) + ε ^ 3 • (0, P₃, H₃) +
          ε ^ 4 • (0, P₄, H₄) =
        (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) := by
    ext <;> norm_num <;> ring
  simp_rw [hpath] at hflat
  convert hflat using 1
  all_goals congr 1
  all_goals funext ε
  all_goals ring

/-- The zero-scale updated-high-coordinate jet is constant through order four, independently of
the cubic and quartic transverse graph coefficients. -/
theorem weightedZeroScaleTransverseHJet (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          (stateMap
            (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
              1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ ↦ 1) 0 := by
  let f : ℝ × ℝ × ℝ → ℝ := fun x ↦ (stateMap x).2.2
  have hf : AnalyticAt ℝ f (0, 2, 1) := by
    exact analyticAt_snd.comp (analyticAt_snd.comp stateMapAnalytic)
  have hflat := FiniteTaylorJet.ofFunction_comp_cubic_quartic f
    ((0, 2, 1) : ℝ × ℝ × ℝ) (0, P₃, H₃) (0, P₄, H₄) hf
  dsimp only [f] at hflat
  rw [stateMap_base, stateMapH_fderiv_apply, stateMapH_fderiv_apply] at hflat
  have hpath (ε : ℝ) :
      ((0, 2, 1) : ℝ × ℝ × ℝ) + ε ^ 3 • (0, P₃, H₃) +
          ε ^ 4 • (0, P₄, H₄) =
        (0, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
          1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) := by
    ext <;> norm_num <;> ring
  simp_rw [hpath] at hflat
  convert hflat using 1
  all_goals congr 1
  all_goals funext ε
  all_goals simp

end DFP.TwoLeg
