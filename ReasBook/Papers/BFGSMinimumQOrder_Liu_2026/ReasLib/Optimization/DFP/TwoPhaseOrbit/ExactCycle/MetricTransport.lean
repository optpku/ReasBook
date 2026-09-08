module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactCycle.Transport
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.Iteration
import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.PhysicalTransport
import Mathlib.Tactic.FinCases
import Mathlib.Tactic

/-!
# Metric transport for exact two-phase cycles

This module identifies each physical phase metric, and the metric after that
phase, with the corresponding abstract secant-step matrices transported by the
phase frame.
-/

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoPhaseOrbit.State

/-- The physical inverse-Hessian metric at the beginning of one phase. -/
def phaseMetric (s : State) (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Fin.cases s.metric (fun _ ↦ s.middleMetric) i

/-- Phase zero begins with the boundary metric. -/
@[simp]
theorem phaseMetric_zero (s : State) : s.phaseMetric 0 = s.metric := by
  rfl

/-- Phase one begins with the middle metric. -/
@[simp]
theorem phaseMetric_one (s : State) : s.phaseMetric 1 = s.middleMetric := by
  rfl

namespace PhaseValidity

/-- For valid phase data, the middle metric is the second abstract step's
inverse Hessian transported by the middle frame. -/
theorem middleMetric_eq_secondStepTransport {s : State} (h : PhaseValidity s) :
    s.middleMetric =
      s.middleFrame * (secondStep s h).inverseHessian * s.middleFrame.transpose := by
  rw [State.middleMetric_def, State.middleFrame_def,
    State.secondStep_inverseHessian]
  rw [← DFP.FirstLeg.metricReconstruction_of_ne s.ε s.p s.h
    (ne_of_gt h.firstGradientLow_pos) (ne_of_gt h.firstSpectralHigh_pos)]
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end PhaseValidity

namespace ExactCycle

/-- The physical metric at the beginning of either exact phase is the
abstract inverse Hessian transported by that phase's frame. -/
theorem phaseMetric_eq_transport {s : State} (h : ExactCycle s) (i : Fin 2) :
    s.phaseMetric i =
      s.phaseFrame i * (h.step i).inverseHessian * (s.phaseFrame i).transpose := by
  fin_cases i
  · have hzero : s.phaseMetric (0 : Fin 2) =
        s.phaseFrame 0 * (h.step 0).inverseHessian * (s.phaseFrame 0).transpose := by
      rw [phaseMetric_zero, phaseFrame_zero, h.step_zero,
        State.metric_def, State.firstStep_inverseHessian]
    simpa using hzero
  · have hone : s.phaseMetric (1 : Fin 2) =
        s.phaseFrame 1 * (h.step 1).inverseHessian * (s.phaseFrame 1).transpose := by
      rw [phaseMetric_one, phaseFrame_one, h.step_one]
      exact h.valid.middleMetric_eq_secondStepTransport
    simpa using hone

end ExactCycle

end DFP.TwoPhaseOrbit.State

namespace DFP.TwoPhaseOrbit

/-- The flattened exact step length at a structured phase index is the step
length of the selected abstract secant step. -/
theorem endpointStepLength_eq_exactStep (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j))
    (j : ℕ) (i : Fin 2) :
    orbit.endpointStepLength h_exact (2 * j + i.val) =
      ((h_exact j).step i).stepLength := by
  fin_cases i
  · simpa using endpointStepLength_even orbit h_exact j
  · simpa using endpointStepLength_odd orbit h_exact j

/-- The flattened endpoint metric at a structured phase index is the physical
metric selected for that phase. -/
theorem endpointMetric_eq_phaseMetric (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) :
    orbit.endpointMetric (2 * j + i.val) = (orbit.state j).phaseMetric i := by
  fin_cases i
  · change orbit.endpointMetric (2 * j) = (orbit.state j).metric
    exact endpointMetric_even orbit j
  · change orbit.endpointMetric (2 * j + 1) = (orbit.state j).middleMetric
    exact endpointMetric_odd orbit j

/-- Exact-cycle data transports the flattened metric directly from the
selected abstract step. -/
theorem endpointMetric_eq_exactStepTransport (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) (h : State.ExactCycle (orbit.state j)) :
    orbit.endpointMetric (2 * j + i.val) =
      (orbit.state j).phaseFrame i * (h.step i).inverseHessian *
        ((orbit.state j).phaseFrame i).transpose := by
  rw [endpointMetric_eq_phaseMetric]
  exact h.phaseMetric_eq_transport i

/-- The flattened metric after an exact phase is the transported next inverse
Hessian of the selected abstract step. -/
theorem endpointMetric_succ_eq_exactStepTransport (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) (h : State.ExactCycle (orbit.state j)) :
    orbit.endpointMetric (2 * j + i.val + 1) =
      (orbit.state j).phaseFrame i * (h.step i).nextInverseHessian *
        ((orbit.state j).phaseFrame i).transpose := by
  fin_cases i
  · have hzero : orbit.endpointMetric (2 * j + (0 : Fin 2).val + 1) =
        (orbit.state j).phaseFrame 0 * (h.step 0).nextInverseHessian *
          ((orbit.state j).phaseFrame 0).transpose := by
      simp only [Fin.val_zero, add_zero, State.phaseFrame_zero]
      rw [endpointMetric_odd, h.step_zero]
      exact h.first.metric
    simpa using hzero
  · have hone : orbit.endpointMetric (2 * j + (1 : Fin 2).val + 1) =
        (orbit.state j).phaseFrame 1 * (h.step 1).nextInverseHessian *
          ((orbit.state j).phaseFrame 1).transpose := by
      simp only [Fin.val_one, State.phaseFrame_one]
      have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by
        omega
      rw [hindex, endpointMetric_even, orbit.state_succ, h.step_one]
      exact h.second.metric
    simpa using hone

end DFP.TwoPhaseOrbit
