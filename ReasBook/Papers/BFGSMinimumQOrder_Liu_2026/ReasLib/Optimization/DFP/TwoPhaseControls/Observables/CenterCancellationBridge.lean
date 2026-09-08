module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterSmoothness
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterSmoothness

/-!
# Public bridge to the canceled center-displacement formulas

This module exposes the neighborhood equalities used internally to remove the
two line-search singularities from the half- and full-cycle center observables.
-/

public section

noncomputable section

open Filter
open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg.CenterCancellation

/-- Near the canceled base state, the original half- and full-center observables
agree simultaneously with their nonsingular canceled representatives. -/
theorem centerDisplacements_eventuallyEq_canceled :
    (fun x : ℝ × ℝ × ℝ ↦
      ((DFP.TwoLeg.observableMap x).halfCenterDisplacement,
        (DFP.TwoLeg.observableMap x).fullCenterDisplacement)) =ᶠ[𝓝 (0, 2, 1)]
      (fun x ↦ (canceledHalfCenterDisplacement x,
        canceledFullCenterDisplacement x)) := by
  have hpContinuous : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    continuousAt_fst.comp continuousAt_snd
  have hhContinuous : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
    continuousAt_snd.comp continuousAt_snd
  let B : ℝ × ℝ × ℝ → ℝ := fun x ↦ 1 + 2 * x.1 ^ 3 + x.1 ^ 4
  have hBContinuous : ContinuousAt B (0, 2, 1) := by
    dsimp only [B]
    fun_prop
  have hpBase : (((0, 2, 1) : ℝ × ℝ × ℝ).2.1 : ℝ) ≠ 0 := by
    norm_num
  have hp : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.2.1 ≠ 0 :=
    hpContinuous.eventually_ne hpBase
  have hhBase : (((0, 2, 1) : ℝ × ℝ × ℝ).2.2 : ℝ) ≠ 0 := by
    norm_num
  have hh : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), x.2.2 ≠ 0 :=
    hhContinuous.eventually_ne hhBase
  have hBBase : B (0, 2, 1) ≠ 0 := by
    norm_num [B]
  have hB : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), B x ≠ 0 :=
    hBContinuous.eventually_ne hBBase
  filter_upwards [hp, hh, hB] with x hpx hhx hBx
  have hBx' : 1 + 2 * x.1 ^ 3 + x.1 ^ 4 ≠ 0 := by
    simpa only [B] using hBx
  unfold canceledHalfCenterDisplacement canceledFullCenterDisplacement
  unfold DFP.TwoLeg.observableMap
  dsimp only
  rw [firstDisplacement_eq_raw x.1 x.2.1 x.2.2 hpx hhx hBx']
  rw [secondDisplacement_eq_raw]
  rfl

/-- Near the canceled base state, every full-center coordinate agrees with the
corresponding coordinate of the canceled full-center representative. -/
theorem fullCenterDisplacement_eventuallyEq_canceled (i : Fin 2) :
    (fun x : ℝ × ℝ × ℝ ↦
      (DFP.TwoLeg.observableMap x).fullCenterDisplacement i) =ᶠ[𝓝 (0, 2, 1)]
      (fun x ↦ canceledFullCenterDisplacement x i) := by
  filter_upwards [centerDisplacements_eventuallyEq_canceled] with x hx
  exact congrArg (fun y :
    EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ y.2 i) hx

/-- Near the canceled base state, every half-center coordinate agrees with the
corresponding coordinate of the canceled half-center representative. -/
theorem halfCenterDisplacement_eventuallyEq_canceled (i : Fin 2) :
    (fun x : ℝ × ℝ × ℝ ↦
      (DFP.TwoLeg.observableMap x).halfCenterDisplacement i) =ᶠ[𝓝 (0, 2, 1)]
      (fun x ↦ canceledHalfCenterDisplacement x i) := by
  filter_upwards [centerDisplacements_eventuallyEq_canceled] with x hx
  exact congrArg (fun y :
    EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ y.1 i) hx

end DFP.TwoLeg.CenterCancellation
