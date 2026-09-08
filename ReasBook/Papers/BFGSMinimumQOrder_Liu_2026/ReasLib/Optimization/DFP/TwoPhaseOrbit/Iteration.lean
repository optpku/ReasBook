module

public import ReasLib.Optimization.DFP.Iteration
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactCycle

public section

noncomputable section

namespace DFP.TwoPhaseOrbit

/-- The inverse-Hessian matrices at the boundary and intermediate endpoints of a
two-phase orbit, flattened into one sequence. -/
def endpointMetric (orbit : DFP.TwoPhaseOrbit) : ℕ → Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.twoStepSequence
    (fun j ↦ (orbit.state j).metric)
    (fun j ↦ (orbit.state j).middleMetric)

/-- At an even endpoint, `endpointMetric` is the corresponding cycle-boundary metric. -/
@[simp] theorem endpointMetric_even (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointMetric (2 * j) = (orbit.state j).metric := by
  rw [endpointMetric, DFP.twoStepSequence_even]

/-- At an odd endpoint, `endpointMetric` is the corresponding intermediate metric. -/
@[simp] theorem endpointMetric_odd (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointMetric (2 * j + 1) = (orbit.state j).middleMetric := by
  rw [endpointMetric, DFP.twoStepSequence_odd]

/-- The exact step lengths of both phases of a two-phase orbit, flattened into one
sequence. -/
def endpointStepLength (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) : ℕ → ℝ :=
  DFP.twoStepSequence
    (fun j ↦ ((h_exact j).step 0).stepLength)
    (fun j ↦ ((h_exact j).step 1).stepLength)

/-- At an even endpoint, `endpointStepLength` is the first exact phase's step length. -/
@[simp] theorem endpointStepLength_even (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) (j : ℕ) :
    orbit.endpointStepLength h_exact (2 * j) = ((h_exact j).step 0).stepLength := by
  rw [endpointStepLength, DFP.twoStepSequence_even]

/-- At an odd endpoint, `endpointStepLength` is the second exact phase's step length. -/
@[simp] theorem endpointStepLength_odd (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) (j : ℕ) :
    orbit.endpointStepLength h_exact (2 * j + 1) = ((h_exact j).step 1).stepLength := by
  rw [endpointStepLength, DFP.twoStepSequence_odd]

/-- Every inverse-Hessian matrix in the flattened sequence of an exact
two-phase orbit is positive definite. -/
theorem endpointMetric_posDef (orbit : DFP.TwoPhaseOrbit)
    (h_exact : ∀ j, State.ExactCycle (orbit.state j)) (k : ℕ) :
    (orbit.endpointMetric k).PosDef := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · rw [endpointMetric_even]
    rw [← State.toCycleBoundaryState_metric (orbit.state j) (h_exact j).valid]
    exact CycleBoundaryState.metric_posDef _
  · rw [endpointMetric_odd, (h_exact j).first.metric]
    have hframe : (orbit.state j).frame ∈
        Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
      (h_exact j).valid.frame_specialOrthogonal
    have hunit : IsUnit (orbit.state j).frame := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have hdet := (Matrix.mem_specialOrthogonalGroup_iff.mp hframe).2
      simp [hdet]
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial (orbit.state j).frame,
      ← Matrix.star_eq_conjTranspose]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hunit).mpr
      (DFP.AbstractSecantStep.nextInverseHessian_posDef _)

end DFP.TwoPhaseOrbit
