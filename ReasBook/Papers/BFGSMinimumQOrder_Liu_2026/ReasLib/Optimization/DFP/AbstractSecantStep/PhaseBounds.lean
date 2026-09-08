module

public import ReasLib.Optimization.DFP.AbstractSecantStep.Identities
public import ReasLib.Optimization.DFP.TwoPhaseControls.QuadraticBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bounds for phase-controlled abstract secant steps

These results connect the algebraic two-phase controls to the coordinate-free
quantities carried by an abstract DFP secant step.
-/

public section

open scoped Matrix

namespace DFP.AbstractSecantStep

/-- An abstract secant step whose matrix and line ratio are one of the two
prescribed phase controls has predicted decrease uniformly comparable to the
squared Euclidean displacement norm. -/
theorem predictedDecrease_mem_Icc_of_phase
    (z : DFP.AbstractSecantStep (Fin 2)) (ε : ℝ) (i : Fin 2)
    (hε : 0 < ε) (hεlt : ε < 1 / 4)
    (hA : z.secantMatrix = (TwoPhaseControls.phase ε i).matrix)
    (hτ : z.tau = (TwoPhaseControls.phase ε i).tau) :
    z.predictedDecrease ∈ Set.Icc
      ((3 / 4 : ℝ) * ‖WithLp.toLp 2 z.displacement‖ ^ 2)
      ((9 / 2 : ℝ) * ‖WithLp.toLp 2 z.displacement‖ ^ 2) := by
  have hcurvature : z.secantCurvature =
      z.displacement ⬝ᵥ
        ((TwoPhaseControls.phase ε i).matrix *ᵥ z.displacement) := by
    rw [z.secantCurvature_def, z.gradientChange_def, hA]
  have hline := z.secantCurvature_eq_tau_mul_predictedDecrease
  rw [hcurvature, hτ] at hline
  exact TwoPhaseControls.phaseQuotient_mem_Icc_of_curvature
    ε i z.displacement z.predictedDecrease hε hεlt hline

/-- For a phase-controlled abstract step, the squared-step-to-decrease ratio
differs from the prescribed phase ratio by the phase quadratic-form defect. -/
theorem phaseStepRatio_deviation_le
    (z : DFP.AbstractSecantStep (Fin 2)) (ε : ℝ) (i : Fin 2)
    (hA : z.secantMatrix = (TwoPhaseControls.phase ε i).matrix)
    (hτ : z.tau = (TwoPhaseControls.phase ε i).tau) :
    |‖WithLp.toLp 2 z.displacement‖ ^ 2 / z.predictedDecrease -
        (TwoPhaseControls.phase ε i).tau| ≤
      2 * |ε| * ‖WithLp.toLp 2 z.displacement‖ ^ 2 /
        z.predictedDecrease := by
  have hqpos : 0 < z.predictedDecrease := z.predictedDecrease_pos
  have hcurvature : z.displacement ⬝ᵥ
        ((TwoPhaseControls.phase ε i).matrix *ᵥ z.displacement) =
      (TwoPhaseControls.phase ε i).tau * z.predictedDecrease := by
    calc
      z.displacement ⬝ᵥ
          ((TwoPhaseControls.phase ε i).matrix *ᵥ z.displacement) =
          z.secantCurvature := by
        rw [z.secantCurvature_def, z.gradientChange_def, hA]
      _ = z.tau * z.predictedDecrease :=
        z.secantCurvature_eq_tau_mul_predictedDecrease
      _ = (TwoPhaseControls.phase ε i).tau * z.predictedDecrease := by
        rw [hτ]
  have hdefect :=
    TwoPhaseControls.abs_dotProduct_sub_phase_quadraticForm_le
      ε i z.displacement
  have hnorm : z.displacement ⬝ᵥ z.displacement =
      ‖WithLp.toLp 2 z.displacement‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, pow_two]
  have hratio :
      ‖WithLp.toLp 2 z.displacement‖ ^ 2 / z.predictedDecrease -
          (TwoPhaseControls.phase ε i).tau =
        (‖WithLp.toLp 2 z.displacement‖ ^ 2 -
            z.displacement ⬝ᵥ
              ((TwoPhaseControls.phase ε i).matrix *ᵥ z.displacement)) /
          z.predictedDecrease := by
    rw [hcurvature]
    field_simp [ne_of_gt hqpos]
  rw [hratio, abs_div, abs_of_pos hqpos]
  apply div_le_div_of_nonneg_right _ hqpos.le
  simpa only [hnorm] using hdefect

end DFP.AbstractSecantStep
