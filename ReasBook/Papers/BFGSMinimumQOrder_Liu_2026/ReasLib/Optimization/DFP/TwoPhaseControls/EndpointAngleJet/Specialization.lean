module

public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet
import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.EndpointAngleSmoothness

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg.EndpointAngleJet

/-- A smooth scalar observable preserves fifth-order closeness to the polynomial slow-graph
path under fifth-order perturbations of its two graph coordinates. -/
private theorem smoothObservableStabilityUnderGraphJets
    (F : ℝ × ℝ × ℝ → ℝ)
    (hF : ContDiffAt ℝ 1 F ((0, 2, 1) : ℝ × ℝ × ℝ))
    (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦ F (ε, p ε, h ε) - F (slowGraphJetPath ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let x : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let x₀ : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p₀ ε, h₀ ε)
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using h_pJet
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using h_hJet
  have hpowFiveTendsto : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
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
      (hpDiff.trans_tendsto hpowFiveTendsto).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
      have hcontinuous : ContinuousAt h₀ 0 := by
        dsimp only [h₀]
        fun_prop
      convert hcontinuous.tendsto using 1
      norm_num [h₀]
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFiveTendsto).add hh₀Tendsto
  have hxTendsto : Tendsto x (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hx₀Tendsto : Tendsto x₀ (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    have hcontinuous : ContinuousAt x₀ 0 := by
      dsimp only [x₀, p₀, h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [x₀, p₀, h₀]
  have hpathDiff : (fun ε ↦ x ε - x₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
    simpa [x, x₀] using hzero.prod_left (hpDiff.prod_left hhDiff)
  have hstrict := hF.hasStrictFDerivAt one_ne_zero
  have houter := hstrict.isBigO_sub
  have hpairs : Tendsto (fun ε ↦ (x ε, x₀ ε)) (𝓝 0)
      (𝓝 (((0, 2, 1), (0, 2, 1)) :
        (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))) := by
    simpa only [nhds_prod_eq] using hxTendsto.prodMk hx₀Tendsto
  have hcomposed := houter.comp_tendsto hpairs
  have hcomposed' : (fun ε ↦ F (x ε) - F (x₀ ε)) =O[𝓝 0]
      (fun ε ↦ x ε - x₀ ε) := by
    simpa only [Function.comp_def] using hcomposed
  have hstability := hcomposed'.trans hpathDiff
  simpa only [x, x₀, p₀, h₀, slowGraphJetPath_apply] using hstability

/-- For coordinate germs with the prescribed slow-graph jets, the first canonical real
endpoint-gradient angle increment is `-2 * ε ^ 2 + o(ε ^ 2)`. -/
theorem firstLeadingOfGraphJets (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal -
        (-2 * ε ^ 2)) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
  have hsmooth : ContDiffAt ℝ 1
      (fun x : ℝ × ℝ × ℝ ↦
        (observableMap x).firstEndpointAngleIncrement.toReal)
      ((0, 2, 1) : ℝ × ℝ × ℝ) :=
    DFP.TwoLeg.firstEndpointAngleIncrement_toReal_contDiffAt 1
  have hstability := smoothObservableStabilityUnderGraphJets
    (fun x : ℝ × ℝ × ℝ ↦
      (observableMap x).firstEndpointAngleIncrement.toReal)
    hsmooth p h h_pJet h_hJet
  have hTwoFive : 2 < 5 := by
    norm_num
  have hTwoSix : 2 < 6 := by
    norm_num
  have hTwoSeven : 2 < 7 := by
    norm_num
  have hstabilityLittle := hstability.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow hTwoFive)
  have hslowLittle := slowFirst.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow hTwoSeven)
  have hfifth : (fun ε : ℝ ↦ -(122 / 5) * ε ^ 5) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) := by
    exact (Asymptotics.isLittleO_pow_pow hTwoFive).const_mul_left (-(122 / 5))
  have hsixth : (fun ε : ℝ ↦ (88 / 15) * ε ^ 6) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) := by
    exact (Asymptotics.isLittleO_pow_pow hTwoSix).const_mul_left (88 / 15)
  have hsum := hstabilityLittle.add
    (hslowLittle.add (hfifth.add hsixth))
  apply hsum.congr_left
  intro ε
  ring

/-- For coordinate germs with the prescribed slow-graph jets, the second canonical real
endpoint-gradient angle increment is `-ε ^ 2 + o(ε ^ 2)`. -/
theorem secondLeadingOfGraphJets (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal -
        (-(ε ^ 2))) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
  have hsmooth : ContDiffAt ℝ 1
      (fun x : ℝ × ℝ × ℝ ↦
        (observableMap x).secondEndpointAngleIncrement.toReal)
      ((0, 2, 1) : ℝ × ℝ × ℝ) :=
    DFP.TwoLeg.secondEndpointAngleIncrement_toReal_contDiffAt 1
  have hstability := smoothObservableStabilityUnderGraphJets
    (fun x : ℝ × ℝ × ℝ ↦
      (observableMap x).secondEndpointAngleIncrement.toReal)
    hsmooth p h h_pJet h_hJet
  have hTwoFive : 2 < 5 := by
    norm_num
  have hTwoSix : 2 < 6 := by
    norm_num
  have hTwoSeven : 2 < 7 := by
    norm_num
  have hstabilityLittle := hstability.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow hTwoFive)
  have hslowLittle := slowSecond.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow hTwoSeven)
  have hfifth : (fun ε : ℝ ↦ -(104 / 5) * ε ^ 5) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) := by
    exact (Asymptotics.isLittleO_pow_pow hTwoFive).const_mul_left (-(104 / 5))
  have hsixth : (fun ε : ℝ ↦ (71 / 15) * ε ^ 6) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 2) := by
    exact (Asymptotics.isLittleO_pow_pow hTwoSix).const_mul_left (71 / 15)
  have hsum := hstabilityLittle.add
    (hslowLittle.add (hfifth.add hsixth))
  apply hsum.congr_left
  intro ε
  ring

end DFP.TwoLeg.EndpointAngleJet
