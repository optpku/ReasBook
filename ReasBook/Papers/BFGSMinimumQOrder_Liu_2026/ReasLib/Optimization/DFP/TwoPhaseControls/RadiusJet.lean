module

public import Mathlib.Analysis.Asymptotics.Defs
public import ReasLib.Analysis.Asymptotics.UniformRemainder.ModulusOrderDrop
public import ReasLib.Analysis.Calculus.FiniteTaylorJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.AnalyticJetGerm
import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.PureScaleJets
import all ReasLib.Analysis.Asymptotics.UniformRemainder
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- Along a polynomial graph with arbitrary cubic and quartic coefficients,
the order-four jet of the normalized two-leg radius factor has the displayed
weighted coefficients. -/
theorem weightedNormalizedRadiusJet (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := graphJetPath P₃ H₃ P₄ H₄ ε
          radiusFactor x.1 x.2.1 x.2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
            ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0 := by
  simpa only [graphJetPath_apply] using
    weightedNormalizedRadiusJet_via_scaleStationarity P₃ H₃ P₄ H₄

/-- Along the polynomial slow graph, the normalized radius factor has
order-four jet `1 - 3 * ε ^ 3 + (5 / 2) * ε ^ 4`. -/
theorem slowGraphNormalizedRadiusJet :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := slowGraphJetPath ε
          radiusFactor x.1 x.2.1 x.2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦ 1 - 3 * ε ^ 3 + (5 / 2) * ε ^ 4) 0 := by
  have hpath (ε : ℝ) :
      slowGraphJetPath ε = graphJetPath (198 / 5) 8 (-9 / 5) 0 ε := by
    rw [slowGraphJetPath_apply, graphJetPath_apply]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · ring
      · ring
  have hinput :
      (fun ε : ℝ ↦
        let x := slowGraphJetPath ε
        radiusFactor x.1 x.2.1 x.2.2) =
        (fun ε : ℝ ↦
          let x := graphJetPath (198 / 5) 8 (-9 / 5) 0 ε
          radiusFactor x.1 x.2.1 x.2.2) := by
    funext ε
    rw [hpath]
  have houtput :
      (fun ε : ℝ ↦ 1 - 3 * ε ^ 3 + (5 / 2) * ε ^ 4) =
        (fun ε : ℝ ↦
          1 + ((6 * 8 + 5 * (198 / 5) - 300) / 18) * ε ^ 3 +
            ((6 * 0 + 5 * (-9 / 5) + 54) / 18) * ε ^ 4) := by
    funext ε
    ring
  rw [hinput, houtput]
  exact weightedNormalizedRadiusJet (198 / 5) 8 (-9 / 5) 0

/-- A perturbation of the polynomial slow graph by `O(ε ^ 5)` yields the
signed recurrence `ε₊ = ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5 + O(ε ^ 6)`. -/
theorem slowGraphSignedRecurrence (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      signedEpsilon ε (p ε) (h ε) -
        (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 6) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let x : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let x₀ : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p₀ ε, h₀ ε)
  let radius : ℝ → ℝ := fun ε ↦
    radiusFactor (x ε).1 (x ε).2.1 (x ε).2.2
  let radius₀ : ℝ → ℝ := fun ε ↦
    radiusFactor (x₀ ε).1 (x₀ ε).2.1 (x₀ ε).2.2
  let radiusPolynomial : ℝ → ℝ := fun ε ↦
    1 - 3 * ε ^ 3 + (5 / 2) * ε ^ 4
  let sqrtPolynomial : ℝ → ℝ := fun ε ↦
    1 - (3 / 2) * ε ^ 3 + (5 / 4) * ε ^ 4
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using hp
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using hh
  have hpow5 : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
      have hcontinuous : ContinuousAt p₀ 0 := by
        dsimp only [p₀]
        fun_prop
      convert hcontinuous.tendsto using 1
      norm_num [p₀]
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpow5).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
      have hcontinuous : ContinuousAt h₀ 0 := by
        dsimp only [h₀]
        fun_prop
      convert hcontinuous.tendsto using 1
      norm_num [h₀]
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpow5).add hh₀Tendsto
  have hxTendsto : Tendsto x (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hx₀Tendsto : Tendsto x₀ (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    have hcontinuous : ContinuousAt x₀ 0 := by
      dsimp only [x₀, p₀, h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [x₀, p₀, h₀]
  have hpathDiff :
      (fun ε ↦ x ε - x₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
    simpa [x, x₀] using hzero.prod_left (hpDiff.prod_left hhDiff)
  have hradiusDiff :
      (fun ε ↦ radius ε - radius₀ ε) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    have houter := analyticAt_radiusFactor.hasStrictFDerivAt.isBigO_sub
    have hpairs : Tendsto (fun ε ↦ (x ε, x₀ ε)) (𝓝 0)
        (𝓝 (((0, 2, 1), (0, 2, 1)) :
          (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))) :=
      by
        simpa only [nhds_prod_eq] using hxTendsto.prodMk hx₀Tendsto
    have hcomposed := houter.comp_tendsto hpairs
    have hcomposed' :
        (fun ε ↦ radius ε - radius₀ ε) =O[𝓝 0]
          (fun ε ↦ x ε - x₀ ε) := by
      simpa only [radius, radius₀, Function.comp_def] using hcomposed
    exact hcomposed'.trans hpathDiff
  have hx₀Analytic : AnalyticAt ℝ x₀ 0 := by
    dsimp only [x₀, p₀, h₀]
    fun_prop
  have hradius₀Analytic : AnalyticAt ℝ radius₀ 0 := by
    have houter : AnalyticAt ℝ
        (fun y : ℝ × ℝ × ℝ ↦ radiusFactor y.1 y.2.1 y.2.2) (x₀ 0) := by
      simpa [x₀, p₀, h₀] using analyticAt_radiusFactor
    simpa only [radius₀, Function.comp_def] using houter.comp hx₀Analytic
  have hradiusPolynomialAnalytic : AnalyticAt ℝ radiusPolynomial 0 := by
    dsimp only [radiusPolynomial]
    fun_prop
  have hradiusJet :
      FiniteTaylorJet.ofFunction ℝ 4 radius₀ 0 =
        FiniteTaylorJet.ofFunction ℝ 4 radiusPolynomial 0 := by
    simpa only [radius₀, radiusPolynomial, x₀, p₀, h₀,
      slowGraphJetPath_apply] using slowGraphNormalizedRadiusJet
  have hradius₀Polynomial : EqModPow 5 radius₀ radiusPolynomial := by
    simpa only [Nat.reduceAdd] using
      EqModPow.of_analytic_jet_eq hradius₀Analytic
        hradiusPolynomialAnalytic hradiusJet
  have hradiusPolynomial : EqModPow 5 radius radiusPolynomial :=
    (EqModPow.of_isBigO hradiusDiff).trans hradius₀Polynomial
  have hsquare :
      EqModPow 5 radiusPolynomial (fun ε ↦ sqrtPolynomial ε ^ 2) := by
    apply EqModPow.of_factor
      (q := fun ε : ℝ ↦ -(9 / 4) * ε + (15 / 4) * ε ^ 2 -
        (25 / 16) * ε ^ 3)
    · fun_prop
    · intro ε
      dsimp only [radiusPolynomial, sqrtPolynomial]
      ring
  have hradiusSquare :
      EqModPow 5 radius (fun ε ↦ sqrtPolynomial ε ^ 2) :=
    hradiusPolynomial.trans hsquare
  have hpZero : p 0 = 2 := by
    have hzero := mem_of_mem_nhds hpDiff.eq_zero_imp
    have := hzero (by norm_num : (0 : ℝ) ^ 5 = 0)
    norm_num [p₀] at this
    linarith
  have hhZero : h 0 = 1 := by
    have hzero := mem_of_mem_nhds hhDiff.eq_zero_imp
    have := hzero (by norm_num : (0 : ℝ) ^ 5 = 0)
    norm_num [h₀] at this
    linarith
  have hradiusZero : radius 0 = 1 := by
    simpa only [radius, x, hpZero, hhZero] using radiusFactor_base
  have hradiusContinuous : ContinuousAt radius 0 := by
    have htendsto := analyticAt_radiusFactor.continuousAt.tendsto.comp hxTendsto
    change Tendsto radius (𝓝 0) (𝓝 (radius 0))
    rw [hradiusZero]
    simpa only [radius, x, Function.comp_def, radiusFactor_base] using htendsto
  have hsqrtPolynomialContinuous : ContinuousAt sqrtPolynomial 0 := by
    dsimp only [sqrtPolynomial]
    fun_prop
  have hsqrt :
      EqModPow 5 (fun ε ↦ Real.sqrt (radius ε)) sqrtPolynomial := by
    apply EqModPow.sqrt_of_sq hradiusSquare hradiusContinuous
      hsqrtPolynomialContinuous
    · rw [hradiusZero]
      norm_num
    · dsimp only [sqrtPolynomial]
      norm_num
  have hscale := Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε) (𝓝 0)
  have hproduct := hscale.mul (EqModPow.to_isBigO hsqrt)
  refine hproduct.congr' ?_ ?_
  · exact Filter.Eventually.of_forall (fun ε ↦ by
      dsimp only [radius, x, sqrtPolynomial, signedEpsilon]
      ring)
  · exact Filter.Eventually.of_forall (fun ε ↦ by ring)

/-- For a slow graph with the fixed cubic and quartic jets, one positive
threshold and coefficient bound the signed two-leg recurrence remainder at
every smaller positive scale. -/
theorem slowGraphSignedRecurrenceBound (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ η₀ > 0, ∃ Cε > 0, ∀ η ∈ Set.Ioc 0 η₀, ∀ ε ∈ Set.Ioc 0 η,
      |signedEpsilon ε (p ε) (h ε) - ε +
          (3 / 2) * ε ^ 4 - (5 / 4) * ε ^ 5| ≤ Cε * ε ^ 6 := by
  have hrecurrence := slowGraphSignedRecurrence p h hp hh
  obtain ⟨Cε, hCε, hUniform⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_of_isBigO_natPow_singleton
      hrecurrence
  unfold Asymptotics.IsUniformRemainderOn at hUniform
  obtain ⟨δ, hδ, hbound⟩ := hUniform
  refine ⟨δ / 2, by positivity, Cε, hCε, ?_⟩
  intro η hη ε hε
  have habs : |ε| < δ := by
    rw [abs_of_pos hε.1]
    have hhalf : δ / 2 < δ := by linarith
    exact hε.2.trans_lt (hη.2.trans_lt hhalf)
  have hpoint := hbound () (Set.mem_univ ()) ε habs
  have hremainder :
      signedEpsilon ε (p ε) (h ε) -
          (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5) =
        signedEpsilon ε (p ε) (h ε) - ε +
          (3 / 2) * ε ^ 4 - (5 / 4) * ε ^ 5 := by
    ring
  dsimp only at hpoint
  rw [hremainder] at hpoint
  simpa only [Real.norm_eq_abs, Real.rpow_natCast, abs_of_pos hε.1] using hpoint

/-- The normalized signed recurrence remainder has the canonical order-five
tail-supremum modulus, uniformly controlled at a linear rate. -/
theorem slowGraphSignedRecurrenceModulus (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    let R : Unit → ℝ → ℝ := fun _ ε ↦
      signedEpsilon ε (p ε) (h ε) -
        (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)
    ∃ η₀ > 0, ∃ Cε > 0,
      Asymptotics.IsUniformRemainderModulusOn R Set.univ 5 η₀
          (Asymptotics.uniformRemainderModulus R Set.univ 5) ∧
        ∀ η ∈ Set.Ioc 0 η₀,
          Asymptotics.uniformRemainderModulus R Set.univ 5 η ≤ Cε * η := by
  dsimp only
  obtain ⟨Cε, hCε, η₀, hη₀, hmodulus, hbound⟩ :=
    Asymptotics.IsUniformRemainderModulusOn.exists_natPow_orderDrop
      (slowGraphSignedRecurrence p h hp hh)
  exact ⟨η₀, hη₀, Cε, hCε, hmodulus, hbound⟩

end DFP.TwoLeg
