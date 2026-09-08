module

import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradient
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ExactCycle
import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoPhaseOrbit.State

/-- The physical frame used at one of the two phases of a cycle. -/
def phaseFrame (s : State) (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Fin.cases s.frame (fun _ ↦ s.middleFrame) i

/-- The physical gradient at the beginning of one phase of a cycle. -/
def phaseGradient (s : State) (i : Fin 2) : EuclideanSpace ℝ (Fin 2) :=
  Fin.cases s.gradient (fun _ ↦ s.middleGradient) i

/-- The physical displacement made during one phase of a cycle. -/
def phaseDisplacement (s : State) (i : Fin 2) : EuclideanSpace ℝ (Fin 2) :=
  Fin.cases s.firstDisplacement (fun _ ↦ s.secondDisplacement) i

/-- Phase zero uses the incoming boundary frame. -/
@[simp]
theorem phaseFrame_zero (s : State) : s.phaseFrame 0 = s.frame := by
  rfl

/-- Phase one uses the physical middle frame. -/
@[simp]
theorem phaseFrame_one (s : State) : s.phaseFrame 1 = s.middleFrame := by
  rfl

/-- Phase zero begins with the boundary gradient. -/
@[simp]
theorem phaseGradient_zero (s : State) : s.phaseGradient 0 = s.gradient := by
  rfl

/-- Phase one begins with the physical middle gradient. -/
@[simp]
theorem phaseGradient_one (s : State) : s.phaseGradient 1 = s.middleGradient := by
  rfl

/-- Phase zero uses the first physical displacement. -/
@[simp]
theorem phaseDisplacement_zero (s : State) :
    s.phaseDisplacement 0 = s.firstDisplacement := by
  rfl

/-- Phase one uses the second physical displacement. -/
@[simp]
theorem phaseDisplacement_one (s : State) :
    s.phaseDisplacement 1 = s.secondDisplacement := by
  rfl

namespace PhaseValidity

/-- The fixed first-leg eigenframe of valid phase data is special orthogonal. -/
theorem firstLegFrame_mem_specialOrthogonal {s : State} (h : PhaseValidity s) :
    DFP.FirstLeg.frame s.ε s.p s.h ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  exact DFP.FirstLeg.frame_mem_specialOrthogonalGroup s.ε s.p s.h
    (ne_of_gt h.firstGradientLow_pos)

/-- The physical middle frame of valid phase data is special orthogonal. -/
theorem middleFrame_mem_specialOrthogonal {s : State} (h : PhaseValidity s) :
    s.middleFrame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [State.middleFrame_def]
  exact mul_mem h.frame_specialOrthogonal h.firstLegFrame_mem_specialOrthogonal

/-- The physical boundary gradient is the first abstract-step gradient transported
by the incoming frame. -/
theorem gradient_eq_firstStepTransport {s : State} (h : PhaseValidity s) :
    s.gradient = WithLp.toLp 2 (s.frame *ᵥ (firstStep s h).gradient) := by
  rw [State.gradient_def, State.firstStep_gradient]
  rw [Matrix.mulVec_smul, WithLp.toLp_smul]

/-- The physical middle gradient is the second abstract-step gradient transported
by the middle frame. -/
theorem middleGradient_eq_secondStepTransport {s : State} (h : PhaseValidity s) :
    s.middleGradient =
      WithLp.toLp 2 (s.middleFrame *ᵥ (secondStep s h).gradient) := by
  let F := DFP.FirstLeg.frame s.ε s.p s.h
  let g := s.amplitude • DFP.FirstLeg.outputGradient s.ε s.p s.h
  let glocal := s.amplitude •
    ![(DFP.FirstLeg.gradientFactors s.ε s.p s.h).1,
      s.ε ^ 2 * (DFP.FirstLeg.gradientFactors s.ε s.p s.h).2]
  have hfactor : F.transpose *ᵥ g = glocal := by
    exact DFP.FirstLeg.frame_transpose_mulVec_outputGradient
      s.ε s.p s.h s.amplitude
  have horthogonal : F ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp
      h.firstLegFrame_mem_specialOrthogonal).1
  have hcancel : F * F.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp horthogonal
  have hrecover : F *ᵥ glocal = g := by
    rw [← hfactor, Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  rw [State.middleGradient_def, State.middleFrame_def]
  rw [State.secondStep_gradient]
  change s.amplitude • WithLp.toLp 2
      (s.frame *ᵥ DFP.FirstLeg.outputGradient s.ε s.p s.h) =
    WithLp.toLp 2 ((s.frame * F) *ᵥ glocal)
  rw [← WithLp.toLp_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]
  rw [hrecover]

/-- The frame used at either phase of valid data is special orthogonal. -/
theorem phaseFrame_mem_specialOrthogonal {s : State} (h : PhaseValidity s)
    (i : Fin 2) :
    s.phaseFrame i ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  fin_cases i
  · simpa using h.frame_specialOrthogonal
  · simpa using h.middleFrame_mem_specialOrthogonal

end PhaseValidity

namespace ExactCycle

/-- The physical gradient at either phase is the corresponding abstract-step
gradient transported by that phase's frame. -/
theorem phaseGradient_eq_transport {s : State} (h : ExactCycle s) (i : Fin 2) :
    s.phaseGradient i = WithLp.toLp 2 (s.phaseFrame i *ᵥ (h.step i).gradient) := by
  fin_cases i
  · change s.gradient =
      WithLp.toLp 2 (s.frame *ᵥ (h.step 0).gradient)
    rw [h.step_zero]
    exact h.valid.gradient_eq_firstStepTransport
  · change s.middleGradient =
      WithLp.toLp 2 (s.middleFrame *ᵥ (h.step 1).gradient)
    rw [h.step_one]
    exact h.valid.middleGradient_eq_secondStepTransport

/-- The physical displacement at either phase is the corresponding abstract-step
displacement transported by that phase's frame. -/
theorem phaseDisplacement_eq_transport {s : State} (h : ExactCycle s) (i : Fin 2) :
    s.phaseDisplacement i =
      WithLp.toLp 2 (s.phaseFrame i *ᵥ (h.step i).displacement) := by
  fin_cases i
  · change s.firstDisplacement =
      WithLp.toLp 2 (s.frame *ᵥ (h.step 0).displacement)
    rw [h.step_zero]
    exact h.first.displacement
  · change s.secondDisplacement =
      WithLp.toLp 2 (s.middleFrame *ᵥ (h.step 1).displacement)
    rw [h.step_one]
    exact h.second.displacement

/-- The abstract secant matrix selected at either phase is the corresponding
two-phase control matrix. -/
theorem step_secantMatrix_eq_phase {s : State} (h : ExactCycle s) (i : Fin 2) :
    (h.step i).secantMatrix = (TwoPhaseControls.phase s.ε i).matrix := by
  fin_cases i
  · change (h.step (0 : Fin 2)).secantMatrix =
      (TwoPhaseControls.phase s.ε (0 : Fin 2)).matrix
    rw [h.step_zero, TwoPhaseControls.phase_zero]
    exact State.firstStep_secantMatrix s h.valid
  · change (h.step (1 : Fin 2)).secantMatrix =
      (TwoPhaseControls.phase s.ε (1 : Fin 2)).matrix
    rw [h.step_one, TwoPhaseControls.phase_one]
    exact State.secondStep_secantMatrix s h.valid

/-- The abstract line ratio selected at either phase is the corresponding
two-phase control ratio. -/
theorem step_tau_eq_phase {s : State} (h : ExactCycle s) (i : Fin 2) :
    (h.step i).tau = (TwoPhaseControls.phase s.ε i).tau := by
  fin_cases i
  · change (h.step (0 : Fin 2)).tau =
      (TwoPhaseControls.phase s.ε (0 : Fin 2)).tau
    rw [h.step_zero, TwoPhaseControls.phase_zero]
    exact State.firstStep_tau s h.valid
  · change (h.step (1 : Fin 2)).tau =
      (TwoPhaseControls.phase s.ε (1 : Fin 2)).tau
    rw [h.step_one, TwoPhaseControls.phase_one]
    exact State.secondStep_tau s h.valid

/-- Orthogonal transport identifies the physical phase pairing with the abstract
predicted decrease. -/
theorem phasePredictedDecrease_eq {s : State} (h : ExactCycle s) (i : Fin 2) :
    -inner ℝ (s.phaseGradient i) (s.phaseDisplacement i) =
      (h.step i).predictedDecrease := by
  rw [h.phaseGradient_eq_transport, h.phaseDisplacement_eq_transport]
  rw [(h.step i).predictedDecrease_def]
  congr 1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using
    Matrix.dotProduct_mulVec_eq_of_mem_specialOrthogonalGroup
      (s.phaseFrame i) (h.valid.phaseFrame_mem_specialOrthogonal i)
      (h.step i).displacement (h.step i).gradient

/-- Orthogonal transport identifies the physical phase displacement norm with
the norm of the abstract displacement. -/
theorem phaseDisplacement_norm_eq {s : State} (h : ExactCycle s) (i : Fin 2) :
    ‖s.phaseDisplacement i‖ = ‖WithLp.toLp 2 (h.step i).displacement‖ := by
  rw [h.phaseDisplacement_eq_transport]
  exact Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    (s.phaseFrame i) (h.valid.phaseFrame_mem_specialOrthogonal i)
    (h.step i).displacement

end ExactCycle

end DFP.TwoPhaseOrbit.State

namespace DFP.TwoPhaseOrbit

/-- The flattened endpoint gradient is the physical gradient of the selected phase. -/
theorem endpointGradient_eq_phaseGradient (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) :
    orbit.endpointGradient (2 * j + i.val) = (orbit.state j).phaseGradient i := by
  fin_cases i
  · change orbit.endpointGradient (2 * j) = (orbit.state j).gradient
    exact endpointGradient_even orbit j
  · change orbit.endpointGradient (2 * j + 1) = (orbit.state j).middleGradient
    exact endpointGradient_odd orbit j

/-- The flattened adjacent-endpoint displacement is the physical displacement
of the selected phase. -/
theorem endpointStep_eq_phaseDisplacement (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) :
    orbit.endpoint (2 * j + i.val + 1) - orbit.endpoint (2 * j + i.val) =
      (orbit.state j).phaseDisplacement i := by
  fin_cases i
  · change orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j) =
      (orbit.state j).firstDisplacement
    rw [endpoint_odd, endpoint_even, State.middlePoint_def]
    abel
  · change orbit.endpoint (2 * j + 2) - orbit.endpoint (2 * j + 1) =
      (orbit.state j).secondDisplacement
    have hsucc : orbit.state (j + 1) = (orbit.state j).next := orbit.state_succ j
    rw [show 2 * j + 2 = 2 * (j + 1) by omega,
      endpoint_even, endpoint_odd, hsucc, State.next_point]
    abel

/-- Exact-cycle data transports the flattened endpoint gradient directly from
the selected abstract step. -/
theorem endpointGradient_eq_exactStepTransport (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) (h : State.ExactCycle (orbit.state j)) :
    orbit.endpointGradient (2 * j + i.val) =
      WithLp.toLp 2
        ((orbit.state j).phaseFrame i *ᵥ (h.step i).gradient) := by
  rw [endpointGradient_eq_phaseGradient]
  exact h.phaseGradient_eq_transport i

/-- The flattened endpoint gradient after an exact phase is the next abstract
gradient transported by that phase's frame. -/
theorem endpointGradient_succ_eq_exactStepTransport (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) (h : State.ExactCycle (orbit.state j)) :
    orbit.endpointGradient (2 * j + i.val + 1) =
      WithLp.toLp 2
        ((orbit.state j).phaseFrame i *ᵥ (h.step i).nextGradient) := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · change orbit.endpointGradient (2 * j + 1) =
      WithLp.toLp 2 ((orbit.state j).frame *ᵥ (h.step 0).nextGradient)
    rw [endpointGradient_odd, h.step_zero]
    exact h.first.gradient
  · refine Fin.cases ?_ (fun i ↦ Fin.elim0 i) i
    change orbit.endpointGradient (2 * j + 1 + 1) =
      WithLp.toLp 2 ((orbit.state j).middleFrame *ᵥ (h.step 1).nextGradient)
    have hindex : 2 * j + 1 + 1 = 2 * (j + 1) := by
      omega
    rw [hindex, endpointGradient_even, orbit.state_succ, h.step_one]
    exact h.second.gradient

/-- Exact-cycle data transports the flattened adjacent-endpoint displacement
directly from the selected abstract step. -/
theorem endpointStep_eq_exactStepTransport (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) (h : State.ExactCycle (orbit.state j)) :
    orbit.endpoint (2 * j + i.val + 1) - orbit.endpoint (2 * j + i.val) =
      WithLp.toLp 2
        ((orbit.state j).phaseFrame i *ᵥ (h.step i).displacement) := by
  rw [endpointStep_eq_phaseDisplacement]
  exact h.phaseDisplacement_eq_transport i

/-- The physical predicted decrease between adjacent flattened endpoints is the
predicted decrease of the selected abstract step. -/
theorem endpointPredictedDecrease_eq_exactStep (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) (h : State.ExactCycle (orbit.state j)) :
    -inner ℝ (orbit.endpointGradient (2 * j + i.val))
        (orbit.endpoint (2 * j + i.val + 1) -
          orbit.endpoint (2 * j + i.val)) =
      (h.step i).predictedDecrease := by
  rw [endpointGradient_eq_phaseGradient, endpointStep_eq_phaseDisplacement]
  exact h.phasePredictedDecrease_eq i

/-- The adjacent flattened-endpoint distance has the norm of the selected
abstract displacement. -/
theorem endpointStepNorm_eq_exactStep (orbit : DFP.TwoPhaseOrbit)
    (j : ℕ) (i : Fin 2) (h : State.ExactCycle (orbit.state j)) :
    ‖orbit.endpoint (2 * j + i.val + 1) - orbit.endpoint (2 * j + i.val)‖ =
      ‖WithLp.toLp 2 (h.step i).displacement‖ := by
  rw [endpointStep_eq_phaseDisplacement]
  exact h.phaseDisplacement_norm_eq i

end DFP.TwoPhaseOrbit
