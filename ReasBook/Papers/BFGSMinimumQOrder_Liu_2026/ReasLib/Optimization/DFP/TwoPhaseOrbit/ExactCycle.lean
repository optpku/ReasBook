module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit

public section

noncomputable section

namespace DFP.TwoPhaseOrbit.State.ExactCycle

/-- Select the abstract secant step at either phase of an exact two-phase cycle. -/
def step {s : State} (h : ExactCycle s) (i : Fin 2) : DFP.AbstractSecantStep (Fin 2) :=
  Fin.cases (State.firstStep s h.valid) (fun _ ↦ State.secondStep s h.valid) i

/-- Phase zero selects the first abstract secant step of an exact cycle. -/
theorem step_zero {s : State} (h : ExactCycle s) :
    h.step 0 = State.firstStep s h.valid := by
  rfl

/-- Phase one selects the second abstract secant step of an exact cycle. -/
theorem step_one {s : State} (h : ExactCycle s) :
    h.step 1 = State.secondStep s h.valid := by
  rfl

/-- The line ratio of either phase of an exact cycle is one of the two
prescribed rational values. -/
theorem step_tau_mem {s : State} (h : ExactCycle s) (i : Fin 2) :
    (h.step i).tau = 2 / 3 ∨ (h.step i).tau = 1 / 3 := by
  fin_cases i
  · left
    change (h.step (0 : Fin 2)).tau = 2 / 3
    rw [step_zero, State.firstStep_tau, TwoPhaseControls.first_tau]
  · right
    change (h.step (1 : Fin 2)).tau = 1 / 3
    rw [step_one, State.secondStep_tau, TwoPhaseControls.second_tau]

end DFP.TwoPhaseOrbit.State.ExactCycle
