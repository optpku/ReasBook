module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.WeightedDefectJets

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- A locally invariant cubic--quartic graph for the two-leg state map satisfies
the four scalar coefficient equations of its invariance defect. -/
theorem invariantSlowGraphCoefficientEquations
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
    exact Filter.Eventually.of_forall (fun ε ↦ by ring)
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

end DFP.TwoLeg
