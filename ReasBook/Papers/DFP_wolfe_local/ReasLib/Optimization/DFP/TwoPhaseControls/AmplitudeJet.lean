/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.SlowGraphRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet.WeightedFactorization
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- Fifth-order perturbations of the polynomial slow graph preserve the normalized
amplitude ratio's expansion through order seven. -/
theorem amplitudeRemainderOfSlowGraphJets (p h : ℝ → ℝ)
    (hp :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
  have hp' : (fun ε : ℝ ↦ p ε - slowGraphAmplitudeP ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [slowGraphAmplitudeP_apply] using hp
  have hh' : (fun ε : ℝ ↦ h ε - slowGraphAmplitudeH ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [slowGraphAmplitudeH_apply] using hh
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by fun_prop
    simpa using hcont.tendsto
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    have hmodel : Tendsto (fun ε : ℝ ↦
        2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4) (𝓝 0) (𝓝 2) := by
      have hcont : ContinuousAt
          (fun ε : ℝ ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4) 0 := by
        fun_prop
      simpa using hcont.tendsto
    simpa only [sub_add_cancel, zero_add] using
      (hp.trans_tendsto hpowFive).add hmodel
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    have hmodel : Tendsto (fun ε : ℝ ↦ 1 + 8 * ε ^ 3) (𝓝 0) (𝓝 1) := by
      have hcont : ContinuousAt (fun ε : ℝ ↦ 1 + 8 * ε ^ 3) 0 := by
        fun_prop
      simpa using hcont.tendsto
    simpa only [sub_add_cancel, zero_add] using
      (hh.trans_tendsto hpowFive).add hmodel
  have hpath : Tendsto (fun ε : ℝ ↦ (ε, p ε, h ε)) (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hslowPath : Tendsto slowGraphJetPath (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    have hcont : ContinuousAt slowGraphJetPath 0 := by
      have hpoly : ContinuousAt
          (fun ε : ℝ ↦ (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) 0 := by fun_prop
      apply hpoly.congr_of_eventuallyEq
      filter_upwards [] with ε
      exact slowGraphJetPath_apply ε
    convert hcont.tendsto using 1
    rw [slowGraphJetPath_apply]
    norm_num
  have hobs := observableMap_amplitude_eq_secondLegAmplitude_eventually p h hpath
  have hslowPath' : Tendsto
      (fun ε : ℝ ↦ (ε, slowGraphAmplitudeP ε, slowGraphAmplitudeH ε)) (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    have hpathEq : slowGraphJetPath =
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) := by
      funext ε
      exact slowGraphJetPath_apply ε
    rw [hpathEq] at hslowPath
    simpa only [slowGraphAmplitudeP_apply, slowGraphAmplitudeH_apply] using hslowPath
  have hobsSlow := observableMap_amplitude_eq_secondLegAmplitude_eventually
    (fun ε : ℝ ↦ slowGraphAmplitudeP ε)
    (fun ε : ℝ ↦ slowGraphAmplitudeH ε) hslowPath'
  obtain ⟨hfactor, hshape, hhigh⟩ :=
    secondLegAmplitude_cubicCoordinateFactorization p h hp' hh'
  have hdiff := secondLegAmplitude_isBigO_of_cubicCoordinateFactorization
    hfactor hshape hhigh hp' hh'
  have hsum := hdiff.add slowGraphAmplitudeRemainderDirect
  apply hsum.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [hobs, hobsSlow] with ε hε hεSlow
  rw [slowGraphJetPath_apply]
  rw [hε]
  rw [slowGraphAmplitudeP_apply, slowGraphAmplitudeH_apply] at hεSlow
  rw [hεSlow]
  ring

/-- Amplitude component of Lemma 7 (`lem:two-step-expansions`).
On an invariant graph of the two-leg state map with the prescribed slow-graph
jets, the normalized amplitude ratio equals `1 - (13 / 2) * ε ^ 4` up to
`O(ε ^ 6)`. -/
theorem slowCurveAmplitudeDrift (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 6) := by
  have _hInvariant := h_invariant
  have h₈ := amplitudeRemainderOfSlowGraphJets p h h_pJet h_hJet
  have hSixEight : 6 < 8 := by
    norm_num
  have h₈ToSix : (fun ε : ℝ ↦ ε ^ 8) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6) :=
    (Asymptotics.isLittleO_pow_pow hSixEight).isBigO
  have h₆ : (fun ε : ℝ ↦ (116 / 5) * ε ^ 6) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 6) :=
    Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 6) (𝓝 0) |>.const_mul_left (116 / 5)
  have hSixSeven : 6 < 7 := by
    norm_num
  have h₇ : (fun ε : ℝ ↦ -(976 / 5) * ε ^ 7) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 6) :=
    (Asymptotics.isLittleO_pow_pow hSixSeven).isBigO.const_mul_left (-(976 / 5))
  have hsum := (h₈.trans h₈ToSix).add (h₆.add h₇)
  have hsum' :
      (fun ε : ℝ ↦
        ((observableMap (ε, p ε, h ε)).amplitudeRatio -
          (1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)) +
          ((116 / 5) * ε ^ 6 + (-(976 / 5) * ε ^ 7))) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 6) := hsum
  have hcombine : ∀ ε : ℝ,
      ((observableMap (ε, p ε, h ε)).amplitudeRatio -
          (1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)) +
          ((116 / 5) * ε ^ 6 + (-(976 / 5) * ε ^ 7)) =
        (observableMap (ε, p ε, h ε)).amplitudeRatio -
          (1 - (13 / 2) * ε ^ 4) := by
    intro ε
    ring
  exact hsum'.congr_left hcombine

end DFP.TwoLeg
