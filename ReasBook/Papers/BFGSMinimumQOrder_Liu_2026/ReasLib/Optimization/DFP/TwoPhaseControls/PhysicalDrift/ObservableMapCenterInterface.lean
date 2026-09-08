module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables

public section

noncomputable section

open scoped EuclideanSpace Matrix

namespace DFP.TwoLeg.Mixed

/-!
This file gives the center field of `observableMap` a small projection interface.
Downstream source proofs can rewrite through this statement instead of unfolding
the entire nested two-leg evaluator.
-/

/-- Infrastructure I.16a: the full-center field of `observableMap` is the raw two-leg
displacement expression in its first-frame coordinates. -/
theorem observableMap_fullCenterDisplacement_eq_rawSteps
    (b : ℝ) (state : ℝ × ℝ × ℝ) :
    let r := state.1
    let p := state.2.1
    let h := state.2.2
    let H₀ : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![h * p * r ^ 2, h]
    let g₀Raw : Fin 2 → ℝ := ![(1 : ℝ), p * r]
    let firstStep := rawObservableStep H₀ g₀Raw (TwoPhaseControls.first b)
    let F₁ := OrientedEigenframe.frame
      (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
      (WithLp.toLp 2 firstStep.2.1)
    let H₁ := F₁.transpose * firstStep.1 * F₁
    let g₁Raw := F₁.transpose *ᵥ firstStep.2.1
    let secondStep := rawObservableStep H₁ g₁Raw (TwoPhaseControls.second b)
    let s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 firstStep.2.2
    let s₁ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (F₁ *ᵥ secondStep.2.2)
    let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 g₀Raw
    let g₂ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (F₁ *ᵥ secondStep.2.1)
    (observableMap b state).fullCenterDisplacement =
      s₀ + s₁ - (g₂ - g₀) := by
  rfl

/-- Helper for Infrastructure I.16a: the first coordinate of the full-center field is the
corresponding first coordinate of the raw displacement expression. -/
theorem observableMap_fullCenterDisplacement_coord_zero_eq_rawSteps
    (b : ℝ) (state : ℝ × ℝ × ℝ) :
    let r := state.1
    let p := state.2.1
    let h := state.2.2
    let H₀ : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![h * p * r ^ 2, h]
    let g₀Raw : Fin 2 → ℝ := ![(1 : ℝ), p * r]
    let firstStep := rawObservableStep H₀ g₀Raw (TwoPhaseControls.first b)
    let F₁ := OrientedEigenframe.frame
      (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
      (WithLp.toLp 2 firstStep.2.1)
    let H₁ := F₁.transpose * firstStep.1 * F₁
    let g₁Raw := F₁.transpose *ᵥ firstStep.2.1
    let secondStep := rawObservableStep H₁ g₁Raw (TwoPhaseControls.second b)
    let s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 firstStep.2.2
    let s₁ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (F₁ *ᵥ secondStep.2.2)
    let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 g₀Raw
    let g₂ : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (F₁ *ᵥ secondStep.2.1)
    (observableMap b state).fullCenterDisplacement 0 =
      (s₀ + s₁ - (g₂ - g₀)) 0 := by
  have hcenter := observableMap_fullCenterDisplacement_eq_rawSteps b state
  exact congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hcenter

end DFP.TwoLeg.Mixed
