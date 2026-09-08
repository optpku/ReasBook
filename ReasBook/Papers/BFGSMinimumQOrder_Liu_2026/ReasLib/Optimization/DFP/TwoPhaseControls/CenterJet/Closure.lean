module

public import ReasLib.Optimization.DFP.TwoPhaseControls.CenterJet.SlowGraphRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.CenterJet.TransverseStability
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterCancellationBridge

/-!
# Clean closure of the full-center slow-graph remainders

This module combines transverse stability with the exact polynomial slow-graph
remainders.  The cancellation bridge is used only to transfer the stability
estimate from the nonsingular representative back to the original observable.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.CenterJet

private theorem slowGraphParameters_tendsto (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    Tendsto p (𝓝 0) (𝓝 2) ∧ Tendsto h (𝓝 0) (𝓝 1) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt h₀ 0 := by
      dsimp only [h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [h₀]
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using hp
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using hh
  constructor
  · simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFive).add hp₀Tendsto
  · simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFive).add hh₀Tendsto

private theorem originalFullCenter_stability_of_canceled
    (i : Fin 2) (p h gauge : ℝ → ℝ)
    (hpTendsto : Tendsto p (𝓝 0) (𝓝 2))
    (hhTendsto : Tendsto h (𝓝 0) (𝓝 1))
    (hcanceled : (fun ε : ℝ ↦
      CenterCancellation.canceledFullCenterDisplacement (ε, p ε, h ε) i -
        CenterCancellation.canceledFullCenterDisplacement (slowGraphJetPath ε) i) =O[𝓝 0]
          gauge) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).fullCenterDisplacement i -
        (observableMap (slowGraphJetPath ε)).fullCenterDisplacement i) =O[𝓝 0]
          gauge := by
  have hpath : Tendsto (fun ε : ℝ ↦ (ε, p ε, h ε)) (𝓝 0) (𝓝 (0, 2, 1)) := by
    simpa only [nhds_prod_eq, id_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hslow : Tendsto slowGraphJetPath (𝓝 0) (𝓝 (0, 2, 1)) := by
    rw [show slowGraphJetPath =
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) by
          funext ε
          exact slowGraphJetPath_apply ε]
    have hc : ContinuousAt
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    convert hc.tendsto using 1
    · norm_num
  have hleftε :=
    (CenterCancellation.fullCenterDisplacement_eventuallyEq_canceled i).comp_tendsto hpath
  have hrightε :=
    (CenterCancellation.fullCenterDisplacement_eventuallyEq_canceled i).comp_tendsto hslow
  apply hcanceled.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hleftε, hrightε] with ε hleft hright
  exact congrArg₂ (fun x y : ℝ ↦ x - y) hleft.symm hright.symm

private theorem originalFullCenter_stabilityUnderGraphJets
    (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 -
        (observableMap (slowGraphJetPath ε)).fullCenterDisplacement 0) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 8) ∧
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).fullCenterDisplacement 1 -
        (observableMap (slowGraphJetPath ε)).fullCenterDisplacement 1) =O[𝓝 0]
          (fun ε : ℝ ↦ ε ^ 9) := by
  obtain ⟨hpTendsto, hhTendsto⟩ := slowGraphParameters_tendsto p h hp hh
  obtain ⟨hlow, hhigh⟩ :=
    CenterCancellation.canceledFullCenterDisplacement_stabilityUnderGraphJets p h hp hh
  exact ⟨
    originalFullCenter_stability_of_canceled 0 p h (fun ε : ℝ ↦ ε ^ 8)
      hpTendsto hhTendsto hlow,
    originalFullCenter_stability_of_canceled 1 p h (fun ε : ℝ ↦ ε ^ 9)
      hpTendsto hhTendsto hhigh⟩

/-- Along any fifth-order perturbation of the polynomial slow graph, the low
full-center coordinate has the clean order-seven model through an `O(ε⁸)` remainder. -/
theorem slowFullLowRemainderViaStability (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 -
        (-(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
  have hstability := (originalFullCenter_stabilityUnderGraphJets p h hp hh).1
  have hsum := hstability.add slowGraphFullCenterLowRemainder
  apply hsum.congr' (Filter.Eventually.of_forall ?_) Filter.EventuallyEq.rfl
  intro ε
  ring

/-- Along any fifth-order perturbation of the polynomial slow graph, the high
full-center coordinate has the clean order-eight model through an `O(ε⁹)` remainder. -/
theorem slowFullHighRemainderViaStability (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).fullCenterDisplacement 1 -
        (-(508 / 5) * ε ^ 8)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 9) := by
  have hstability := (originalFullCenter_stabilityUnderGraphJets p h hp hh).2
  have hsum := hstability.add slowGraphFullCenterHighRemainder
  apply hsum.congr' (Filter.Eventually.of_forall ?_) Filter.EventuallyEq.rfl
  intro ε
  ring

end DFP.TwoLeg.CenterJet
