module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Regularity
import all ReasLib.Geometry.Euclidean.Plane.Rotation
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.TwoPhaseOrbit

/-- The physical state at one boundary of an exact planar two-phase DFP cycle. -/
structure State where
  ε : ℝ
  p : ℝ
  h : ℝ
  amplitude : ℝ
  frame : Matrix (Fin 2) (Fin 2) ℝ
  point : EuclideanSpace ℝ (Fin 2)

namespace State

/-- The initial physical state associated to a chosen slow curve and scale. -/
def initial (p h : ℝ → ℝ) (ε₀ : ℝ) : State where
  ε := ε₀
  p := p ε₀
  h := h ε₀
  amplitude := 1
  frame := 1
  point := WithLp.toLp 2 ![(1 : ℝ), p ε₀ * ε₀ ^ 2]

/-- The normalized scale, shape, and high-eigenvalue coordinates of a physical state. -/
def coordinates (s : State) : ℝ × ℝ × ℝ :=
  (s.ε, s.p, s.h)

/-- The inverse-Hessian matrix encoded by a physical two-phase state. -/
def metric (s : State) : Matrix (Fin 2) (Fin 2) ℝ :=
  s.frame * Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h] * s.frame.transpose

/-- The gradient encoded by a physical two-phase state. -/
def gradient (s : State) : EuclideanSpace ℝ (Fin 2) :=
  s.amplitude • WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), s.p * s.ε ^ 2])

/-- The center `x - g` encoded by a physical two-phase state. -/
def center (s : State) : EuclideanSpace ℝ (Fin 2) :=
  s.point - s.gradient

/-- The exact first-phase displacement, expressed in the incoming physical frame. -/
def firstDisplacement (s : State) : EuclideanSpace ℝ (Fin 2) :=
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h]
  let g : Fin 2 → ℝ := s.amplitude • ![(1 : ℝ), s.p * s.ε ^ 2]
  let v := H *ᵥ g
  let A := (TwoPhaseControls.first s.ε).matrix
  let α := (TwoPhaseControls.first s.ε).tau * (g ⬝ᵥ v) / (v ⬝ᵥ (A *ᵥ v))
  WithLp.toLp 2 (s.frame *ᵥ (-(α • v)))

/-- The endpoint reached after the first exact DFP phase. -/
def middlePoint (s : State) : EuclideanSpace ℝ (Fin 2) :=
  s.point + s.firstDisplacement

/-- The inverse-Hessian matrix after the first exact DFP phase. -/
def middleMetric (s : State) : Matrix (Fin 2) (Fin 2) ℝ :=
  s.frame * DFP.FirstLeg.outputMetric s.ε s.p s.h * s.frame.transpose

/-- The gradient after the first exact DFP phase. -/
def middleGradient (s : State) : EuclideanSpace ℝ (Fin 2) :=
  s.amplitude •
    WithLp.toLp 2 (s.frame *ᵥ DFP.FirstLeg.outputGradient s.ε s.p s.h)

/-- The fixed oriented eigenframe after the first exact DFP phase. -/
def middleFrame (s : State) : Matrix (Fin 2) (Fin 2) ℝ :=
  s.frame * DFP.FirstLeg.frame s.ε s.p s.h

/-- The exact second-phase displacement, expressed in the physical middle frame. -/
def secondDisplacement (s : State) : EuclideanSpace ℝ (Fin 2) :=
  let spectral := DFP.FirstLeg.spectralFactors s.ε s.p s.h
  let gradient := DFP.FirstLeg.gradientFactors s.ε s.p s.h
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![s.ε ^ 4 * spectral.1, spectral.2]
  let g : Fin 2 → ℝ :=
    s.amplitude • ![gradient.1, s.ε ^ 2 * gradient.2]
  let v := H *ᵥ g
  let A := (TwoPhaseControls.second s.ε).matrix
  let α := (TwoPhaseControls.second s.ε).tau * (g ⬝ᵥ v) / (v ⬝ᵥ (A *ᵥ v))
  WithLp.toLp 2 (s.middleFrame *ᵥ (-(α • v)))

/-- Apply one complete exact algebraic two-phase transition to a physical state. -/
def next (s : State) : State :=
  let q := DFP.TwoLeg.stateMap s.coordinates
  { ε := q.1
    p := q.2.1
    h := q.2.2
    amplitude := s.amplitude * (DFP.SecondLeg.coordinates s.ε s.p s.h).1
    frame := s.middleFrame * DFP.SecondLeg.frame s.ε s.p s.h
    point := s.middlePoint + s.secondDisplacement }

/-- The initial state's normalized coordinates are the prescribed slow-curve values. -/
theorem initial_coordinates (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (initial p h ε₀).coordinates = (ε₀, p ε₀, h ε₀) := by
  rfl

/-- The initial state's scale is the chosen initial scale. -/
@[simp]
theorem initial_epsilon (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (initial p h ε₀).ε = ε₀ := by
  rfl

/-- The initial state's shape coordinate is evaluated on the chosen graph. -/
@[simp]
theorem initial_p (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (initial p h ε₀).p = p ε₀ := by
  rfl

/-- The initial state's high coordinate is evaluated on the chosen graph. -/
@[simp]
theorem initial_h (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (initial p h ε₀).h = h ε₀ := by
  rfl

/-- The initial amplitude is one. -/
theorem initial_amplitude (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (initial p h ε₀).amplitude = 1 := by
  rfl

/-- The initial oriented frame is the identity matrix. -/
theorem initial_frame (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (initial p h ε₀).frame = 1 := by
  rfl

/-- The initial point is its canonical gradient. -/
theorem initial_point (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (initial p h ε₀).point = (initial p h ε₀).gradient := by
  simp [initial, gradient]

/-- The initial center `x₀ - g₀` is zero. -/
theorem initial_center (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (initial p h ε₀).center = 0 := by
  simp [center, initial, gradient]

/-- The coordinate projection of a state is its stored triple. -/
theorem coordinates_def (s : State) : s.coordinates = (s.ε, s.p, s.h) := by
  rfl

/-- The metric has the canonical diagonal-frame normal form. -/
theorem metric_def (s : State) :
    s.metric =
      s.frame * Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h] * s.frame.transpose := by
  rfl

/-- The gradient has the canonical oriented-frame normal form. -/
theorem gradient_def (s : State) :
    s.gradient =
      s.amplitude • WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), s.p * s.ε ^ 2]) := by
  rfl

/-- The center is the difference between the endpoint and its encoded gradient. -/
theorem center_def (s : State) : s.center = s.point - s.gradient := by
  rfl

/-- The first displacement is the prescribed inverse-form DFP displacement. -/
theorem firstDisplacement_def (s : State) :
    s.firstDisplacement =
      let H : Matrix (Fin 2) (Fin 2) ℝ :=
        Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h]
      let g : Fin 2 → ℝ := s.amplitude • ![(1 : ℝ), s.p * s.ε ^ 2]
      let v := H *ᵥ g
      let A := (TwoPhaseControls.first s.ε).matrix
      let α := (TwoPhaseControls.first s.ε).tau * (g ⬝ᵥ v) / (v ⬝ᵥ (A *ᵥ v))
      WithLp.toLp 2 (s.frame *ᵥ (-(α • v))) := by
  rfl

/-- The middle endpoint is obtained by adding the first displacement. -/
theorem middlePoint_def (s : State) :
    s.middlePoint = s.point + s.firstDisplacement := by
  rfl

/-- The middle metric is the first-leg output transported by the incoming frame. -/
theorem middleMetric_def (s : State) :
    s.middleMetric =
      s.frame * DFP.FirstLeg.outputMetric s.ε s.p s.h * s.frame.transpose := by
  rfl

/-- The middle gradient is the first-leg output transported and scaled physically. -/
theorem middleGradient_def (s : State) :
    s.middleGradient = s.amplitude •
      WithLp.toLp 2 (s.frame *ᵥ DFP.FirstLeg.outputGradient s.ε s.p s.h) := by
  rfl

/-- The middle frame is the incoming frame followed by the fixed first-leg branch. -/
theorem middleFrame_def (s : State) :
    s.middleFrame = s.frame * DFP.FirstLeg.frame s.ε s.p s.h := by
  rfl

/-- The second displacement is the prescribed inverse-form DFP displacement in the
middle oriented eigenframe. -/
theorem secondDisplacement_def (s : State) :
    s.secondDisplacement =
      let spectral := DFP.FirstLeg.spectralFactors s.ε s.p s.h
      let gradient := DFP.FirstLeg.gradientFactors s.ε s.p s.h
      let H : Matrix (Fin 2) (Fin 2) ℝ :=
        Matrix.diagonal ![s.ε ^ 4 * spectral.1, spectral.2]
      let g : Fin 2 → ℝ :=
        s.amplitude • ![gradient.1, s.ε ^ 2 * gradient.2]
      let v := H *ᵥ g
      let A := (TwoPhaseControls.second s.ε).matrix
      let α := (TwoPhaseControls.second s.ε).tau * (g ⬝ᵥ v) / (v ⬝ᵥ (A *ᵥ v))
      WithLp.toLp 2 (s.middleFrame *ᵥ (-(α • v))) := by
  rfl

/-- The next normalized coordinates are exactly the signed two-leg state map. -/
theorem next_coordinates (s : State) :
    s.next.coordinates = DFP.TwoLeg.stateMap s.coordinates := by
  rfl

/-- The next amplitude is the current amplitude times the oriented final low coordinate. -/
theorem next_amplitude (s : State) :
    s.next.amplitude =
      s.amplitude * (DFP.SecondLeg.coordinates s.ε s.p s.h).1 := by
  rfl

/-- The next frame follows both fixed oriented eigenframe branches. -/
theorem next_frame (s : State) :
    s.next.frame = s.middleFrame * DFP.SecondLeg.frame s.ε s.p s.h := by
  rfl

/-- The next endpoint is the middle endpoint plus the second displacement. -/
theorem next_point (s : State) :
    s.next.point = s.middlePoint + s.secondDisplacement := by
  rfl

/-- The positivity and orientation conditions that make both algebraic phases valid at
one physical cycle boundary. -/
structure PhaseValidity (s : State) : Prop where
  frame_specialOrthogonal : s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ
  ε_pos : 0 < s.ε
  ε_lt_quarter : s.ε < 1 / 4
  p_pos : 0 < s.p
  h_pos : 0 < s.h
  amplitude_pos : 0 < s.amplitude
  firstSpectralLow_pos : 0 < (DFP.FirstLeg.spectralFactors s.ε s.p s.h).1
  firstSpectralHigh_pos : 0 < (DFP.FirstLeg.spectralFactors s.ε s.p s.h).2
  firstGradientLow_pos : 0 < (DFP.FirstLeg.gradientFactors s.ε s.p s.h).1
  firstGradientHigh_pos : 0 < (DFP.FirstLeg.gradientFactors s.ε s.p s.h).2
  firstRadiusFactor_pos : 0 < (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).1
  secondSpectralLow_pos : 0 < (DFP.SecondLeg.spectralFactors s.ε s.p s.h).1
  secondSpectralHigh_pos : 0 < (DFP.SecondLeg.spectralFactors s.ε s.p s.h).2
  secondGradientLow_pos : 0 < (DFP.SecondLeg.gradientFactors s.ε s.p s.h).1
  secondGradientHigh_pos : 0 < (DFP.SecondLeg.gradientFactors s.ε s.p s.h).2
  secondRadiusFactor_pos : 0 < (DFP.SecondLeg.canonicalFactors s.ε s.p s.h).1

namespace PhaseValidity

/-- Assemble phase validity from named boundary, first-phase, and second-phase facts. -/
theorem ofComponents (s : State)
    (h_frame : s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (h_ε : 0 < s.ε) (h_εlt : s.ε < 1 / 4) (h_p : 0 < s.p)
    (h_h : 0 < s.h) (h_amplitude : 0 < s.amplitude)
    (h_firstSpectralLow : 0 < (DFP.FirstLeg.spectralFactors s.ε s.p s.h).1)
    (h_firstSpectralHigh : 0 < (DFP.FirstLeg.spectralFactors s.ε s.p s.h).2)
    (h_firstGradientLow : 0 < (DFP.FirstLeg.gradientFactors s.ε s.p s.h).1)
    (h_firstGradientHigh : 0 < (DFP.FirstLeg.gradientFactors s.ε s.p s.h).2)
    (h_firstRadius : 0 < (DFP.FirstLeg.canonicalFactors s.ε s.p s.h).1)
    (h_secondSpectralLow : 0 < (DFP.SecondLeg.spectralFactors s.ε s.p s.h).1)
    (h_secondSpectralHigh : 0 < (DFP.SecondLeg.spectralFactors s.ε s.p s.h).2)
    (h_secondGradientLow : 0 < (DFP.SecondLeg.gradientFactors s.ε s.p s.h).1)
    (h_secondGradientHigh : 0 < (DFP.SecondLeg.gradientFactors s.ε s.p s.h).2)
    (h_secondRadius : 0 < (DFP.SecondLeg.canonicalFactors s.ε s.p s.h).1) :
    PhaseValidity s := by
  exact
    { frame_specialOrthogonal := h_frame
      ε_pos := h_ε
      ε_lt_quarter := h_εlt
      p_pos := h_p
      h_pos := h_h
      amplitude_pos := h_amplitude
      firstSpectralLow_pos := h_firstSpectralLow
      firstSpectralHigh_pos := h_firstSpectralHigh
      firstGradientLow_pos := h_firstGradientLow
      firstGradientHigh_pos := h_firstGradientHigh
      firstRadiusFactor_pos := h_firstRadius
      secondSpectralLow_pos := h_secondSpectralLow
      secondSpectralHigh_pos := h_secondSpectralHigh
      secondGradientLow_pos := h_secondGradientLow
      secondGradientHigh_pos := h_secondGradientHigh
      secondRadiusFactor_pos := h_secondRadius }

end PhaseValidity

/-- The first column of an oriented state frame has Euclidean norm one. -/
theorem toCycleBoundaryState_e_norm (s : State) (h : PhaseValidity s) :
    ‖WithLp.toLp 2 (fun i ↦ s.frame i 0)‖ = 1 := by
  rcases (Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp h.frame_specialOrthogonal) with
    ⟨hdiag, hoff, hunit⟩
  have hnorm := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (fun i ↦ s.frame i 0))
  rw [Fin.sum_univ_two] at hnorm
  rw [hoff] at hunit
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i ↦ s.frame i 0))]

/-- The squared scale of a valid phase is strictly positive. -/
theorem toCycleBoundaryState_r_pos (s : State) (h : PhaseValidity s) :
    0 < s.ε ^ 2 := by
  exact pow_pos h.ε_pos 2

/-- View a valid physical boundary state through the canonical `CycleBoundaryState`
interface, using radius `ε ^ 2` and the first column of its oriented frame. -/
def toCycleBoundaryState (s : State) (h : PhaseValidity s) : CycleBoundaryState where
  e := WithLp.toLp 2 (fun i ↦ s.frame i 0)
  r := s.ε ^ 2
  p := s.p
  h := s.h
  amplitude := s.amplitude
  e_norm := toCycleBoundaryState_e_norm s h
  r_pos := toCycleBoundaryState_r_pos s h
  p_pos := h.p_pos
  h_pos := h.h_pos
  amplitude_pos := h.amplitude_pos

/-- The canonical boundary-state view has the physical state's inverse-Hessian matrix. -/
theorem toCycleBoundaryState_metric (s : State) (h : PhaseValidity s) :
    (toCycleBoundaryState s h).metric = s.metric := by
  have hcoords :=
    (Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp h.frame_specialOrthogonal)
  have hframe : (toCycleBoundaryState s h).frame = s.frame := by
    apply Matrix.ext
    intro i j
    fin_cases j
    · have hcol := CycleBoundaryState.frame_col_zero (toCycleBoundaryState s h) i
      simpa [toCycleBoundaryState] using hcol
    · have hcol := CycleBoundaryState.frame_col_one (toCycleBoundaryState s h) i
      rw [CycleBoundaryState.perp_eq] at hcol
      fin_cases i
      · calc
          (toCycleBoundaryState s h).frame 0 1 = -s.frame 1 0 := by
            simpa [toCycleBoundaryState] using hcol
          _ = s.frame 0 1 := hcoords.2.1.symm
      · calc
          (toCycleBoundaryState s h).frame 1 1 = s.frame 0 0 := by
            simpa [toCycleBoundaryState] using hcol
          _ = s.frame 1 1 := hcoords.1
  have hmetric := (CycleBoundaryState.spec (toCycleBoundaryState s h)).1
  rw [hmetric, State.metric_def, hframe]
  change
    s.frame * Matrix.diagonal ![s.h * s.p * (s.ε ^ 2) ^ 2, s.h] * s.frame.transpose =
      s.frame * Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h] * s.frame.transpose
  have hpow : (s.ε ^ 2) ^ 2 = s.ε ^ 4 := by ring
  rw [hpow]

/-- The canonical boundary-state view has the physical state's gradient. -/
theorem toCycleBoundaryState_gradient (s : State) (h : PhaseValidity s) :
    (toCycleBoundaryState s h).gradient = s.gradient := by
  have hcoords :=
    (Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp h.frame_specialOrthogonal)
  have hframe : (toCycleBoundaryState s h).frame = s.frame := by
    apply Matrix.ext
    intro i j
    fin_cases j
    · have hcol := CycleBoundaryState.frame_col_zero (toCycleBoundaryState s h) i
      simpa [toCycleBoundaryState] using hcol
    · have hcol := CycleBoundaryState.frame_col_one (toCycleBoundaryState s h) i
      rw [CycleBoundaryState.perp_eq] at hcol
      fin_cases i
      · calc
          (toCycleBoundaryState s h).frame 0 1 = -s.frame 1 0 := by
            simpa [toCycleBoundaryState] using hcol
          _ = s.frame 0 1 := hcoords.2.1.symm
      · calc
          (toCycleBoundaryState s h).frame 1 1 = s.frame 0 0 := by
            simpa [toCycleBoundaryState] using hcol
          _ = s.frame 1 1 := hcoords.1
  have hgradient := (CycleBoundaryState.spec (toCycleBoundaryState s h)).2
  rw [hgradient, State.gradient_def, hframe]
  change
    s.amplitude •
        (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
          !₂[(1 : ℝ), s.p * s.ε ^ 2] =
      s.amplitude • WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), s.p * s.ε ^ 2])
  rfl

/-- The first phase begins with a positive definite inverse-Hessian matrix. -/
theorem firstStep_inverseHessian_posDef (s : State) (h : PhaseValidity s) :
    (Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i
  · dsimp
    exact mul_pos (mul_pos h.h_pos h.p_pos) (pow_pos h.ε_pos 4)
  · dsimp
    exact h.h_pos

/-- The first control supplies a positive definite secant matrix. -/
theorem firstStep_secantMatrix_posDef (s : State) (h : PhaseValidity s) :
    (TwoPhaseControls.first s.ε).matrix.PosDef := by
  rw [← TwoPhaseControls.phase_zero]
  exact TwoPhaseControls.matrix_posDef s.ε s.ε 0 h.ε_pos le_rfl h.ε_lt_quarter

/-- The first control has a strictly positive line ratio. -/
theorem firstStep_tau_pos (ε : ℝ) :
    0 < (TwoPhaseControls.first ε).tau := by
  rw [← TwoPhaseControls.phase_zero]
  exact TwoPhaseControls.tau_pos ε 0

/-- The first phase begins with a nonzero normalized gradient. -/
theorem firstStep_gradient_ne_zero (s : State) (h : PhaseValidity s) :
    s.amplitude • ![(1 : ℝ), s.p * s.ε ^ 2] ≠ 0 := by
  apply smul_ne_zero (ne_of_gt h.amplitude_pos)
  intro hzero
  have hcoord := congrArg (fun x : Fin 2 → ℝ => x 0) hzero
  norm_num at hcoord

/-- The exact abstract secant step for the first phase in incoming frame coordinates. -/
def firstStep (s : State) (h : PhaseValidity s) : DFP.AbstractSecantStep (Fin 2) where
  inverseHessian := Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h]
  gradient := s.amplitude • ![(1 : ℝ), s.p * s.ε ^ 2]
  secantMatrix := (TwoPhaseControls.first s.ε).matrix
  tau := (TwoPhaseControls.first s.ε).tau
  inverseHessian_posDef := firstStep_inverseHessian_posDef s h
  secantMatrix_posDef := firstStep_secantMatrix_posDef s h
  tau_pos := firstStep_tau_pos s.ε
  gradient_ne_zero := firstStep_gradient_ne_zero s h

/-- The first abstract step uses the incoming diagonal inverse Hessian. -/
@[simp]
theorem firstStep_inverseHessian (s : State) (h : PhaseValidity s) :
    (firstStep s h).inverseHessian =
      Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h] := by
  rfl

/-- The first abstract step stores the canonical incoming-frame gradient. -/
@[simp]
theorem firstStep_gradient (s : State) (h : PhaseValidity s) :
    (firstStep s h).gradient =
      s.amplitude • ![(1 : ℝ), s.p * s.ε ^ 2] := by
  rfl

/-- The first abstract step uses the first two-phase control matrix. -/
@[simp]
theorem firstStep_secantMatrix (s : State) (h : PhaseValidity s) :
    (firstStep s h).secantMatrix = (TwoPhaseControls.first s.ε).matrix := by
  rfl

/-- The first abstract step retains the canonical first-phase ratio. -/
@[simp]
theorem firstStep_tau (s : State) (h : PhaseValidity s) :
    (firstStep s h).tau = (TwoPhaseControls.first s.ε).tau := by
  rfl

/-- The second phase begins with a positive definite inverse-Hessian matrix. -/
theorem secondStep_inverseHessian_posDef (s : State) (h : PhaseValidity s) :
    (Matrix.diagonal
      ![s.ε ^ 4 * (DFP.FirstLeg.spectralFactors s.ε s.p s.h).1,
        (DFP.FirstLeg.spectralFactors s.ε s.p s.h).2] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i
  · dsimp
    exact mul_pos (pow_pos h.ε_pos 4) h.firstSpectralLow_pos
  · dsimp
    exact h.firstSpectralHigh_pos

/-- The second control supplies a positive definite secant matrix. -/
theorem secondStep_secantMatrix_posDef (s : State) (h : PhaseValidity s) :
    (TwoPhaseControls.second s.ε).matrix.PosDef := by
  rw [← TwoPhaseControls.phase_one]
  exact TwoPhaseControls.matrix_posDef s.ε s.ε 1 h.ε_pos le_rfl h.ε_lt_quarter

/-- The second control has a strictly positive line ratio. -/
theorem secondStep_tau_pos (ε : ℝ) :
    0 < (TwoPhaseControls.second ε).tau := by
  rw [← TwoPhaseControls.phase_one]
  exact TwoPhaseControls.tau_pos ε 1

/-- The second phase begins with a nonzero normalized gradient. -/
theorem secondStep_gradient_ne_zero (s : State) (h : PhaseValidity s) :
    s.amplitude •
      ![(DFP.FirstLeg.gradientFactors s.ε s.p s.h).1,
        s.ε ^ 2 * (DFP.FirstLeg.gradientFactors s.ε s.p s.h).2] ≠ 0 := by
  apply smul_ne_zero (ne_of_gt h.amplitude_pos)
  intro hzero
  have hcoord := congrArg (fun x : Fin 2 → ℝ => x 0) hzero
  have hfactorZero : (DFP.FirstLeg.gradientFactors s.ε s.p s.h).1 = 0 := by
    simpa using hcoord
  exact (ne_of_gt h.firstGradientLow_pos) hfactorZero

/-- The exact abstract secant step for the second phase in the middle frame coordinates. -/
def secondStep (s : State) (h : PhaseValidity s) : DFP.AbstractSecantStep (Fin 2) where
  inverseHessian := Matrix.diagonal
    ![s.ε ^ 4 * (DFP.FirstLeg.spectralFactors s.ε s.p s.h).1,
      (DFP.FirstLeg.spectralFactors s.ε s.p s.h).2]
  gradient := s.amplitude •
    ![(DFP.FirstLeg.gradientFactors s.ε s.p s.h).1,
      s.ε ^ 2 * (DFP.FirstLeg.gradientFactors s.ε s.p s.h).2]
  secantMatrix := (TwoPhaseControls.second s.ε).matrix
  tau := (TwoPhaseControls.second s.ε).tau
  inverseHessian_posDef := secondStep_inverseHessian_posDef s h
  secantMatrix_posDef := secondStep_secantMatrix_posDef s h
  tau_pos := secondStep_tau_pos s.ε
  gradient_ne_zero := secondStep_gradient_ne_zero s h

/-- The second abstract step uses the diagonalized first-leg inverse Hessian. -/
@[simp]
theorem secondStep_inverseHessian (s : State) (h : PhaseValidity s) :
    (secondStep s h).inverseHessian = Matrix.diagonal
      ![s.ε ^ 4 * (DFP.FirstLeg.spectralFactors s.ε s.p s.h).1,
        (DFP.FirstLeg.spectralFactors s.ε s.p s.h).2] := by
  rfl

/-- The second abstract step stores the first-leg gradient factors in
middle-frame coordinates. -/
@[simp]
theorem secondStep_gradient (s : State) (h : PhaseValidity s) :
    (secondStep s h).gradient = s.amplitude •
      ![(DFP.FirstLeg.gradientFactors s.ε s.p s.h).1,
        s.ε ^ 2 * (DFP.FirstLeg.gradientFactors s.ε s.p s.h).2] := by
  rfl

/-- The second abstract step uses the second two-phase control matrix. -/
@[simp]
theorem secondStep_secantMatrix (s : State) (h : PhaseValidity s) :
    (secondStep s h).secantMatrix = (TwoPhaseControls.second s.ε).matrix := by
  rfl

/-- The second abstract step retains the canonical second-phase ratio. -/
@[simp]
theorem secondStep_tau (s : State) (h : PhaseValidity s) :
    (secondStep s h).tau = (TwoPhaseControls.second s.ε).tau := by
  rfl

/-- The first abstract step produces the established exact first-leg outputs. -/
theorem firstStep_output (s : State) (h : PhaseValidity s) :
    ((firstStep s h).nextInverseHessian, (firstStep s h).nextGradient) =
      (DFP.FirstLeg.outputMetric s.ε s.p s.h,
        s.amplitude • DFP.FirstLeg.outputGradient s.ε s.p s.h) := by
  exact DFP.FirstLeg.outputEqStep (firstStep s h) s.ε s.p s.h s.amplitude
    rfl rfl rfl rfl

/-- The second abstract step produces the established exact second-leg outputs. -/
theorem secondStep_output (s : State) (h : PhaseValidity s) :
    ((secondStep s h).nextInverseHessian, (secondStep s h).nextGradient) =
      (DFP.SecondLeg.outputMetric s.ε s.p s.h,
        s.amplitude • DFP.SecondLeg.outputGradient s.ε s.p s.h) := by
  exact DFP.SecondLeg.outputEqStep (secondStep s h) s.ε s.p s.h s.amplitude
    rfl rfl rfl rfl

/-- A nonzero low-eigenvector normalization denominator gives a special orthogonal
oriented eigenframe. -/
private theorem lowFrame_mem_specialOrthogonal_of_denom_ne_zero (a b d : ℝ)
    (hdenom : RealSymmetric2.lowDenom a b d ≠ 0) :
    EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [EuclideanPlane.frame_mem_specialOrthogonalGroup_iff]
  have hdenomNonneg : 0 ≤ RealSymmetric2.lowDenom a b d := by
    unfold RealSymmetric2.lowDenom
    positivity
  have hdenomPos : 0 < RealSymmetric2.lowDenom a b d :=
    lt_of_le_of_ne hdenomNonneg (Ne.symm hdenom)
  have hraw : ‖RealSymmetric2.lowRaw a b d‖ ≠ 0 := by
    rw [← RealSymmetric2.lowDenom_eq_norm_lowRaw]
    exact hdenom
  rw [RealSymmetric2.lowVector, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hdenomPos, RealSymmetric2.lowDenom_eq_norm_lowRaw]
  exact inv_mul_cancel₀ hraw

/-- A normalized nonzero low frame diagonalizes its real symmetric matrix without a
choice of coordinate chart. -/
private theorem lowFrame_diagonalizes_of_denom_ne_zero (a b d : ℝ)
    (hdenom : RealSymmetric2.lowDenom a b d ≠ 0) :
    (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose *
          RealSymmetric2.matrix a b d *
        EuclideanPlane.frame (RealSymmetric2.lowVector a b d) =
      Matrix.diagonal
        ![RealSymmetric2.low a b d, RealSymmetric2.high a b d] := by
  let F := EuclideanPlane.frame (RealSymmetric2.lowVector a b d)
  let D := Matrix.diagonal
    ![RealSymmetric2.low a b d, RealSymmetric2.high a b d]
  have hspecial : F ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    exact lowFrame_mem_specialOrthogonal_of_denom_ne_zero a b d hdenom
  have horthogonal : F ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hcancel : F.transpose * F = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp horthogonal
  have hlow : RealSymmetric2.matrix a b d *ᵥ
      WithLp.ofLp (RealSymmetric2.lowVector a b d) =
        RealSymmetric2.low a b d •
          WithLp.ofLp (RealSymmetric2.lowVector a b d) := by
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using
      congrArg WithLp.ofLp (RealSymmetric2.lowVector_eigen a b d)
  have hhigh : RealSymmetric2.matrix a b d *ᵥ
      WithLp.ofLp (RealSymmetric2.highVector a b d) =
        RealSymmetric2.high a b d •
          WithLp.ofLp (RealSymmetric2.highVector a b d) := by
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using
      congrArg WithLp.ofLp (RealSymmetric2.highVector_eigen a b d)
  have hmul : RealSymmetric2.matrix a b d * F = F * D := by
    ext i j
    fin_cases j
    · have hcoord := congrArg (fun v : Fin 2 → ℝ ↦ v i) hlow
      simpa [F, D, EuclideanPlane.frame, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, mul_comm] using hcoord
    · have hcoord := congrArg (fun v : Fin 2 → ℝ ↦ v i) hhigh
      rw [RealSymmetric2.highVector_eq_perp_lowVector] at hcoord
      simpa [F, D, EuclideanPlane.frame, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, mul_comm] using hcoord
  calc
    F.transpose * RealSymmetric2.matrix a b d * F =
        F.transpose * (RealSymmetric2.matrix a b d * F) := by
          rw [Matrix.mul_assoc]
    _ = F.transpose * (F * D) := by rw [hmul]
    _ = (F.transpose * F) * D := by rw [Matrix.mul_assoc]
    _ = D := by rw [hcancel, Matrix.one_mul]

/-- The fixed second-leg gradient coordinates have their removable pointwise
factorization for every parameter triple. -/
private theorem secondLeg_gradientFactorization (ε p h G : ℝ) :
    (DFP.SecondLeg.frame ε p h).transpose *ᵥ
        (G • DFP.SecondLeg.outputGradient ε p h) =
      G • ![(DFP.SecondLeg.gradientFactors ε p h).1,
        ε ^ 2 * (DFP.SecondLeg.gradientFactors ε p h).2] := by
  unfold DFP.SecondLeg.gradientFactors DFP.SecondLeg.frame
    DFP.SecondLeg.outputMetric DFP.SecondLeg.outputGradient
  ext i
  fin_cases i
  · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply,
      RealSymmetric2.lowVector, RealSymmetric2.lowRaw, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    ring
  · simp [EuclideanPlane.frame, EuclideanPlane.perp_apply,
      RealSymmetric2.lowVector, RealSymmetric2.lowRaw, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    ring

/-- The normalization denominator of the fixed second-leg low eigenvector. -/
private def secondLegFrameDenom (s : State) : ℝ :=
  let M := DFP.SecondLeg.outputMetric s.ε s.p s.h
  RealSymmetric2.lowDenom (M 0 0) (M 0 1) (M 1 1)

/-- The raw low-frame coordinate numerator of the second-leg output gradient. -/
private def secondLegGradientLowNumerator (s : State) : ℝ :=
  let M := DFP.SecondLeg.outputMetric s.ε s.p s.h
  let g := DFP.SecondLeg.outputGradient s.ε s.p s.h
  (M 1 1 - RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1)) * g 0 -
    M 0 1 * g 1

/-- The removable second-leg low gradient factor is its raw coordinate divided by
the low-eigenvector normalization denominator. -/
private theorem secondLegGradientLow_eq_div (s : State) :
    (DFP.SecondLeg.gradientFactors s.ε s.p s.h).1 =
      secondLegGradientLowNumerator s / secondLegFrameDenom s := by
  simp [secondLegGradientLowNumerator, secondLegFrameDenom,
    DFP.SecondLeg.gradientFactors, DFP.SecondLeg.outputMetric,
    DFP.SecondLeg.outputGradient]
  ring

/-- Valid second-leg data has a nonzero low-eigenvector normalization denominator. -/
private theorem secondLegFrameDenom_ne_zero (s : State) (h : PhaseValidity s) :
    secondLegFrameDenom s ≠ 0 := by
  intro hzero
  have hfactor := h.secondGradientLow_pos
  rw [secondLegGradientLow_eq_div, hzero, div_zero] at hfactor
  exact lt_irrefl 0 hfactor

/-- The fixed second-leg frame of valid phase data is special orthogonal. -/
private theorem secondLegFrame_mem_specialOrthogonal (s : State) (h : PhaseValidity s) :
    DFP.SecondLeg.frame s.ε s.p s.h ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  let M := DFP.SecondLeg.outputMetric s.ε s.p s.h
  change EuclideanPlane.frame
      (RealSymmetric2.lowVector (M 0 0) (M 0 1) (M 1 1)) ∈
    Matrix.specialOrthogonalGroup (Fin 2) ℝ
  exact lowFrame_mem_specialOrthogonal_of_denom_ne_zero
    (M 0 0) (M 0 1) (M 1 1) (secondLegFrameDenom_ne_zero s h)

/-- A nonzero high eigenvalue exposes the pointwise removable second-leg spectrum. -/
private theorem secondLeg_spectrumFactorization_of_high_ne_zero (ε p h : ℝ)
    (hhigh : (DFP.SecondLeg.spectralFactors ε p h).2 ≠ 0) :
    DFP.SecondLeg.eigenvalues ε p h =
      (ε ^ 4 * (DFP.SecondLeg.spectralFactors ε p h).1,
        (DFP.SecondLeg.spectralFactors ε p h).2) := by
  unfold DFP.SecondLeg.spectralFactors at hhigh
  dsimp at hhigh
  unfold DFP.SecondLeg.eigenvalues DFP.SecondLeg.spectralFactors
    DFP.SecondLeg.outputMetric
  dsimp
  apply Prod.ext
  · rw [← mul_div_assoc]
    apply (eq_div_iff hhigh).2
    rw [RealSymmetric2.low_mul_high]
    ring
  · rfl

/-- Valid second-leg data is diagonalized pointwise by its fixed oriented frame. -/
private theorem secondLeg_frameDiagonalization (s : State) (h : PhaseValidity s) :
    (DFP.SecondLeg.frame s.ε s.p s.h).transpose *
          DFP.SecondLeg.outputMetric s.ε s.p s.h *
        DFP.SecondLeg.frame s.ε s.p s.h =
      Matrix.diagonal
        ![s.ε ^ 4 * (DFP.SecondLeg.spectralFactors s.ε s.p s.h).1,
          (DFP.SecondLeg.spectralFactors s.ε s.p s.h).2] := by
  let M := DFP.SecondLeg.outputMetric s.ε s.p s.h
  let F := EuclideanPlane.frame
    (RealSymmetric2.lowVector (M 0 0) (M 0 1) (M 1 1))
  have hmatrix : M = RealSymmetric2.matrix (M 0 0) (M 0 1) (M 1 1) := by
    unfold M DFP.SecondLeg.outputMetric RealSymmetric2.matrix
    rfl
  have hdiagonal := lowFrame_diagonalizes_of_denom_ne_zero
    (M 0 0) (M 0 1) (M 1 1) (secondLegFrameDenom_ne_zero s h)
  have hspectrum := secondLeg_spectrumFactorization_of_high_ne_zero s.ε s.p s.h
    (ne_of_gt h.secondSpectralHigh_pos)
  have hlow := congrArg Prod.fst hspectrum
  have hhigh := congrArg Prod.snd hspectrum
  rw [DFP.SecondLeg.eigenvalues] at hlow hhigh
  dsimp only at hlow hhigh
  change F.transpose * M * F = _
  calc
    F.transpose * M * F =
        F.transpose * RealSymmetric2.matrix (M 0 0) (M 0 1) (M 1 1) * F :=
      congrArg (fun N ↦ F.transpose * N * F) hmatrix
    _ = Matrix.diagonal
        ![RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1),
          RealSymmetric2.high (M 0 0) (M 0 1) (M 1 1)] := hdiagonal
    _ = Matrix.diagonal
        ![s.ε ^ 4 * (DFP.SecondLeg.spectralFactors s.ε s.p s.h).1,
          (DFP.SecondLeg.spectralFactors s.ε s.p s.h).2] := by
      rw [hlow, hhigh]

/-- The unscaled fixed-frame coordinates of the second-leg output gradient are its
two removable factors. -/
private theorem secondLeg_coordinates_eq_factors (ε p h : ℝ) :
    DFP.SecondLeg.coordinates ε p h =
      ((DFP.SecondLeg.gradientFactors ε p h).1,
        ε ^ 2 * (DFP.SecondLeg.gradientFactors ε p h).2) := by
  have hvector := secondLeg_gradientFactorization ε p h 1
  simp only [one_smul] at hvector
  unfold DFP.SecondLeg.coordinates
  apply Prod.ext
  · exact congrArg (fun v : Fin 2 → ℝ ↦ v 0) hvector
  · exact congrArg (fun v : Fin 2 → ℝ ↦ v 1) hvector

/-- The signed state-map coordinates recover the removable second-leg spectral
diagonal for valid phase data. -/
private theorem stateMap_metricDiagonal (s : State) (h : PhaseValidity s) :
    let q := DFP.TwoLeg.stateMap s.coordinates
    Matrix.diagonal ![q.2.2 * q.2.1 * q.1 ^ 4, q.2.2] =
      Matrix.diagonal
        ![s.ε ^ 4 * (DFP.SecondLeg.spectralFactors s.ε s.p s.h).1,
          (DFP.SecondLeg.spectralFactors s.ε s.p s.h).2] := by
  let spectral := DFP.SecondLeg.spectralFactors s.ε s.p s.h
  let gradient := DFP.SecondLeg.gradientFactors s.ε s.p s.h
  let canonical := DFP.SecondLeg.canonicalFactors s.ε s.p s.h
  have hcanonicalRadius : canonical.1 =
      spectral.1 * gradient.1 / (spectral.2 * gradient.2) := by
    rfl
  have hcanonicalShape : canonical.2 =
      spectral.2 * gradient.2 ^ 2 / (spectral.1 * gradient.1 ^ 2) := by
    rfl
  have hspectralLow : spectral.1 ≠ 0 := ne_of_gt h.secondSpectralLow_pos
  have hspectralHigh : spectral.2 ≠ 0 := ne_of_gt h.secondSpectralHigh_pos
  have hgradientLow : gradient.1 ≠ 0 := ne_of_gt h.secondGradientLow_pos
  have hgradientHigh : gradient.2 ≠ 0 := ne_of_gt h.secondGradientHigh_pos
  have hcanonicalNonneg : 0 ≤ canonical.1 := h.secondRadiusFactor_pos.le
  have hsqrtSquare : Real.sqrt canonical.1 ^ 2 = canonical.1 :=
    Real.sq_sqrt hcanonicalNonneg
  have hsqrtFourth : Real.sqrt canonical.1 ^ 4 = canonical.1 ^ 2 := by
    calc
      Real.sqrt canonical.1 ^ 4 = (Real.sqrt canonical.1 ^ 2) ^ 2 := by ring
      _ = canonical.1 ^ 2 := by rw [hsqrtSquare]
  have hlow : spectral.2 * canonical.2 *
      (s.ε * Real.sqrt canonical.1) ^ 4 = s.ε ^ 4 * spectral.1 := by
    calc
      spectral.2 * canonical.2 * (s.ε * Real.sqrt canonical.1) ^ 4 =
          spectral.2 * canonical.2 * s.ε ^ 4 *
            Real.sqrt canonical.1 ^ 4 := by ring
      _ = spectral.2 * canonical.2 * s.ε ^ 4 * canonical.1 ^ 2 := by
        rw [hsqrtFourth]
      _ = s.ε ^ 4 * spectral.1 := by
        rw [hcanonicalRadius, hcanonicalShape]
        field_simp [hspectralLow, hspectralHigh, hgradientLow, hgradientHigh]
  rw [State.coordinates_def, DFP.TwoLeg.stateMap_apply]
  change Matrix.diagonal
      ![spectral.2 * canonical.2 * (s.ε * Real.sqrt canonical.1) ^ 4,
        spectral.2] =
    Matrix.diagonal ![s.ε ^ 4 * spectral.1, spectral.2]
  ext i j
  fin_cases i
  · fin_cases j
    · simpa using hlow
    · simp
  · fin_cases j
    · simp
    · simp

/-- The second-leg metric is reconstructed from its valid removable spectral
diagonal and fixed oriented frame. -/
private theorem secondLeg_metricReconstruction (s : State) (h : PhaseValidity s) :
    DFP.SecondLeg.frame s.ε s.p s.h *
          Matrix.diagonal
            ![s.ε ^ 4 * (DFP.SecondLeg.spectralFactors s.ε s.p s.h).1,
              (DFP.SecondLeg.spectralFactors s.ε s.p s.h).2] *
        (DFP.SecondLeg.frame s.ε s.p s.h).transpose =
      DFP.SecondLeg.outputMetric s.ε s.p s.h := by
  let F := DFP.SecondLeg.frame s.ε s.p s.h
  let M := DFP.SecondLeg.outputMetric s.ε s.p s.h
  let D := Matrix.diagonal
    ![s.ε ^ 4 * (DFP.SecondLeg.spectralFactors s.ε s.p s.h).1,
      (DFP.SecondLeg.spectralFactors s.ε s.p s.h).2]
  have hspecial : F ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
    secondLegFrame_mem_specialOrthogonal s h
  have horthogonal : F ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hcancel : F * F.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp horthogonal
  have hdiagonal : F.transpose * M * F = D :=
    secondLeg_frameDiagonalization s h
  change F * D * F.transpose = M
  calc
    F * D * F.transpose = F * (F.transpose * M * F) * F.transpose := by
      rw [hdiagonal]
    _ = (F * F.transpose) * M * (F * F.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = M := by rw [hcancel, Matrix.one_mul, Matrix.mul_one]

/-- The successor metric is the second-leg output transported by the physical
middle frame. -/
private theorem next_metric_eq_secondLegTransport (s : State) (h : PhaseValidity s) :
    s.next.metric = s.middleFrame * DFP.SecondLeg.outputMetric s.ε s.p s.h *
      s.middleFrame.transpose := by
  rw [State.metric_def]
  dsimp [State.next]
  rw [stateMap_metricDiagonal s h]
  rw [← secondLeg_metricReconstruction s h]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- The successor's canonical vector, scaled by the final low coordinate, reconstructs
the normalized second-leg output gradient. -/
private theorem stateMap_gradientVector (s : State) (h : PhaseValidity s) :
    let q := DFP.TwoLeg.stateMap s.coordinates
    (DFP.SecondLeg.coordinates s.ε s.p s.h).1 •
        (DFP.SecondLeg.frame s.ε s.p s.h *ᵥ ![(1 : ℝ), q.2.1 * q.1 ^ 2]) =
      DFP.SecondLeg.outputGradient s.ε s.p s.h := by
  let spectral := DFP.SecondLeg.spectralFactors s.ε s.p s.h
  let gradient := DFP.SecondLeg.gradientFactors s.ε s.p s.h
  let canonical := DFP.SecondLeg.canonicalFactors s.ε s.p s.h
  let F := DFP.SecondLeg.frame s.ε s.p s.h
  let g := DFP.SecondLeg.outputGradient s.ε s.p s.h
  have hcanonicalRadius : canonical.1 =
      spectral.1 * gradient.1 / (spectral.2 * gradient.2) := by
    rfl
  have hcanonicalShape : canonical.2 =
      spectral.2 * gradient.2 ^ 2 / (spectral.1 * gradient.1 ^ 2) := by
    rfl
  have hspectralLow : spectral.1 ≠ 0 := ne_of_gt h.secondSpectralLow_pos
  have hspectralHigh : spectral.2 ≠ 0 := ne_of_gt h.secondSpectralHigh_pos
  have hgradientLow : gradient.1 ≠ 0 := ne_of_gt h.secondGradientLow_pos
  have hgradientHigh : gradient.2 ≠ 0 := ne_of_gt h.secondGradientHigh_pos
  have hcanonicalNonneg : 0 ≤ canonical.1 := h.secondRadiusFactor_pos.le
  have hsqrtSquare : Real.sqrt canonical.1 ^ 2 = canonical.1 :=
    Real.sq_sqrt hcanonicalNonneg
  have hshapeRadius : gradient.1 * canonical.2 * canonical.1 = gradient.2 := by
    rw [hcanonicalRadius, hcanonicalShape]
    field_simp [hspectralLow, hspectralHigh, hgradientLow, hgradientHigh]
  have hhighCoordinate : gradient.1 *
      (canonical.2 * (s.ε * Real.sqrt canonical.1) ^ 2) =
        s.ε ^ 2 * gradient.2 := by
    calc
      gradient.1 * (canonical.2 * (s.ε * Real.sqrt canonical.1) ^ 2) =
          s.ε ^ 2 * (gradient.1 * canonical.2 *
            Real.sqrt canonical.1 ^ 2) := by ring
      _ = s.ε ^ 2 * (gradient.1 * canonical.2 * canonical.1) := by
        rw [hsqrtSquare]
      _ = s.ε ^ 2 * gradient.2 := by rw [hshapeRadius]
  have hscaledVector : gradient.1 •
      ![(1 : ℝ), canonical.2 * (s.ε * Real.sqrt canonical.1) ^ 2] =
        ![gradient.1, s.ε ^ 2 * gradient.2] := by
    ext i
    fin_cases i
    · simp
    · simpa using hhighCoordinate
  have hspecial : F ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ :=
    secondLegFrame_mem_specialOrthogonal s h
  have horthogonal : F ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hcancel : F * F.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp horthogonal
  have hfactorization : F.transpose *ᵥ g =
      ![gradient.1, s.ε ^ 2 * gradient.2] := by
    simpa only [F, g, gradient, one_smul] using
      secondLeg_gradientFactorization s.ε s.p s.h 1
  have hrecover : F *ᵥ ![gradient.1, s.ε ^ 2 * gradient.2] = g := by
    rw [← hfactorization, Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  have hcoordinates : DFP.SecondLeg.coordinates s.ε s.p s.h =
      (gradient.1, s.ε ^ 2 * gradient.2) := by
    exact secondLeg_coordinates_eq_factors s.ε s.p s.h
  rw [State.coordinates_def, DFP.TwoLeg.stateMap_apply]
  change (DFP.SecondLeg.coordinates s.ε s.p s.h).1 •
      (F *ᵥ ![(1 : ℝ), canonical.2 * (s.ε * Real.sqrt canonical.1) ^ 2]) = g
  rw [hcoordinates]
  dsimp only
  calc
    gradient.1 •
        (F *ᵥ ![(1 : ℝ), canonical.2 * (s.ε * Real.sqrt canonical.1) ^ 2]) =
      F *ᵥ (gradient.1 •
        ![(1 : ℝ), canonical.2 * (s.ε * Real.sqrt canonical.1) ^ 2]) := by
        rw [Matrix.mulVec_smul]
    _ = F *ᵥ ![gradient.1, s.ε ^ 2 * gradient.2] := by rw [hscaledVector]
    _ = g := hrecover

/-- The successor gradient is the scaled second-leg output transported by the
physical middle frame. -/
private theorem next_gradient_eq_secondLegTransport (s : State) (h : PhaseValidity s) :
    s.next.gradient = WithLp.toLp 2
      (s.middleFrame *ᵥ (s.amplitude • DFP.SecondLeg.outputGradient s.ε s.p s.h)) := by
  have hlocal := stateMap_gradientVector s h
  rw [State.gradient_def]
  dsimp [State.next] at hlocal ⊢
  rw [← WithLp.toLp_smul]
  congr 1
  rw [← Matrix.mulVec_mulVec]
  calc
    (s.amplitude * (DFP.SecondLeg.coordinates s.ε s.p s.h).1) •
        (s.middleFrame *ᵥ
          (DFP.SecondLeg.frame s.ε s.p s.h *ᵥ
            ![(1 : ℝ),
              (DFP.TwoLeg.stateMap s.coordinates).2.1 *
                (DFP.TwoLeg.stateMap s.coordinates).1 ^ 2])) =
      s.middleFrame *ᵥ
        ((s.amplitude * (DFP.SecondLeg.coordinates s.ε s.p s.h).1) •
          (DFP.SecondLeg.frame s.ε s.p s.h *ᵥ
            ![(1 : ℝ),
              (DFP.TwoLeg.stateMap s.coordinates).2.1 *
                (DFP.TwoLeg.stateMap s.coordinates).1 ^ 2])) := by
        rw [Matrix.mulVec_smul]
    _ = s.middleFrame *ᵥ
        (s.amplitude •
          ((DFP.SecondLeg.coordinates s.ε s.p s.h).1 •
            (DFP.SecondLeg.frame s.ε s.p s.h *ᵥ
              ![(1 : ℝ),
                (DFP.TwoLeg.stateMap s.coordinates).2.1 *
                  (DFP.TwoLeg.stateMap s.coordinates).1 ^ 2]))) := by
      rw [mul_smul]
    _ = s.middleFrame *ᵥ
        (s.amplitude • DFP.SecondLeg.outputGradient s.ε s.p s.h) := by
      rw [hlocal]

/-- The normalization denominator of the fixed first-leg low eigenvector. -/
private def firstLegFrameDenom (s : State) : ℝ :=
  let M := DFP.FirstLeg.outputMetric s.ε s.p s.h
  RealSymmetric2.lowDenom (M 0 0) (M 0 1) (M 1 1)

/-- The raw low-frame coordinate numerator of the first-leg output gradient. -/
private def firstLegGradientLowNumerator (s : State) : ℝ :=
  let M := DFP.FirstLeg.outputMetric s.ε s.p s.h
  let g := DFP.FirstLeg.outputGradient s.ε s.p s.h
  (M 1 1 - RealSymmetric2.low (M 0 0) (M 0 1) (M 1 1)) * g 0 -
    M 0 1 * g 1

/-- The removable first-leg low gradient factor is its raw coordinate divided by
the low-eigenvector normalization denominator. -/
private theorem firstLegGradientLow_eq_div (s : State) :
    (DFP.FirstLeg.gradientFactors s.ε s.p s.h).1 =
      firstLegGradientLowNumerator s / firstLegFrameDenom s := by
  simp [firstLegGradientLowNumerator, firstLegFrameDenom,
    DFP.FirstLeg.gradientFactors, DFP.FirstLeg.outputMetric,
    DFP.FirstLeg.outputGradient]
  ring

/-- Valid first-leg data has a nonzero low-eigenvector normalization denominator. -/
private theorem firstLegFrameDenom_ne_zero (s : State) (h : PhaseValidity s) :
    firstLegFrameDenom s ≠ 0 := by
  intro hzero
  have hfactor := h.firstGradientLow_pos
  rw [firstLegGradientLow_eq_div, hzero, div_zero] at hfactor
  exact lt_irrefl 0 hfactor

/-- The fixed first-leg frame of valid phase data is special orthogonal. -/
private theorem firstLegFrame_mem_specialOrthogonal (s : State) (h : PhaseValidity s) :
    DFP.FirstLeg.frame s.ε s.p s.h ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  let M := DFP.FirstLeg.outputMetric s.ε s.p s.h
  change EuclideanPlane.frame
      (RealSymmetric2.lowVector (M 0 0) (M 0 1) (M 1 1)) ∈
    Matrix.specialOrthogonalGroup (Fin 2) ℝ
  exact lowFrame_mem_specialOrthogonal_of_denom_ne_zero
    (M 0 0) (M 0 1) (M 1 1) (firstLegFrameDenom_ne_zero s h)

/-- A valid physical transition preserves special orthogonality of the stored frame. -/
private theorem nextFrame_mem_specialOrthogonal (s : State) (h : PhaseValidity s) :
    s.next.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [State.next_frame, State.middleFrame_def]
  exact mul_mem (mul_mem h.frame_specialOrthogonal
    (firstLegFrame_mem_specialOrthogonal s h))
      (secondLegFrame_mem_specialOrthogonal s h)

/-- A valid physical transition preserves strict positivity of the stored amplitude. -/
private theorem nextAmplitude_pos (s : State) (h : PhaseValidity s) :
    0 < s.next.amplitude := by
  rw [State.next_amplitude, secondLeg_coordinates_eq_factors]
  exact mul_pos h.amplitude_pos h.secondGradientLow_pos

/-- Exact agreement between the first abstract secant step and the physical middle state. -/
structure FirstPhaseExact (s : State) (h : PhaseValidity s) : Prop where
  displacement : s.firstDisplacement =
    WithLp.toLp 2 (s.frame *ᵥ (firstStep s h).displacement)
  metric : s.middleMetric =
    s.frame * (firstStep s h).nextInverseHessian * s.frame.transpose
  gradient : s.middleGradient =
    WithLp.toLp 2 (s.frame *ᵥ (firstStep s h).nextGradient)

namespace FirstPhaseExact

/-- Assemble first-phase exactness from its displacement, metric, and gradient equations. -/
theorem ofEqualities (s : State) (h : PhaseValidity s)
    (h_displacement : s.firstDisplacement =
      WithLp.toLp 2 (s.frame *ᵥ (firstStep s h).displacement))
    (h_metric : s.middleMetric =
      s.frame * (firstStep s h).nextInverseHessian * s.frame.transpose)
    (h_gradient : s.middleGradient =
      WithLp.toLp 2 (s.frame *ᵥ (firstStep s h).nextGradient)) :
    FirstPhaseExact s h := by
  exact ⟨h_displacement, h_metric, h_gradient⟩

/-- The abstract secant step certified by exactness of the first phase. -/
def abstractStep (s : State) (h : PhaseValidity s) (_exact : FirstPhaseExact s h) :
    DFP.AbstractSecantStep (Fin 2) :=
  firstStep s h

end FirstPhaseExact

/-- Exact agreement between the second abstract secant step and the physical successor. -/
structure SecondPhaseExact (s : State) (h : PhaseValidity s) : Prop where
  displacement : s.secondDisplacement =
    WithLp.toLp 2 (s.middleFrame *ᵥ (secondStep s h).displacement)
  metric : s.next.metric =
    s.middleFrame * (secondStep s h).nextInverseHessian * s.middleFrame.transpose
  gradient : s.next.gradient =
    WithLp.toLp 2 (s.middleFrame *ᵥ (secondStep s h).nextGradient)

namespace SecondPhaseExact

/-- Assemble second-phase exactness from its displacement, metric, and gradient equations. -/
theorem ofEqualities (s : State) (h : PhaseValidity s)
    (h_displacement : s.secondDisplacement =
      WithLp.toLp 2 (s.middleFrame *ᵥ (secondStep s h).displacement))
    (h_metric : s.next.metric =
      s.middleFrame * (secondStep s h).nextInverseHessian * s.middleFrame.transpose)
    (h_gradient : s.next.gradient =
      WithLp.toLp 2 (s.middleFrame *ᵥ (secondStep s h).nextGradient)) :
    SecondPhaseExact s h := by
  exact ⟨h_displacement, h_metric, h_gradient⟩

/-- The abstract secant step certified by exactness of the second phase. -/
def abstractStep (s : State) (h : PhaseValidity s) (_exact : SecondPhaseExact s h) :
    DFP.AbstractSecantStep (Fin 2) :=
  secondStep s h

end SecondPhaseExact

/-- A valid physical cycle whose two phases are the corresponding exact abstract DFP steps. -/
structure ExactCycle (s : State) : Prop where
  valid : PhaseValidity s
  first : FirstPhaseExact s valid
  second : SecondPhaseExact s valid

namespace ExactCycle

/-- Assemble an exact cycle from its named validity and two phase specifications. -/
theorem ofPhases (s : State) (valid : PhaseValidity s) (first : FirstPhaseExact s valid)
    (second : SecondPhaseExact s valid) : ExactCycle s := by
  exact ⟨valid, first, second⟩

/-- The ordered pair of abstract secant steps certified by an exact cycle. -/
def abstractSteps (s : State) (h : ExactCycle s) :
    DFP.AbstractSecantStep (Fin 2) × DFP.AbstractSecantStep (Fin 2) :=
  (FirstPhaseExact.abstractStep s h.valid h.first,
    SecondPhaseExact.abstractStep s h.valid h.second)

end ExactCycle

/-- Phase validity implies exact agreement with the first abstract secant step. -/
theorem firstPhaseExact_of_phaseValidity (s : State) (h : PhaseValidity s) :
    FirstPhaseExact s h := by
  refine FirstPhaseExact.ofEqualities s h ?_ ?_ ?_
  · rw [State.firstDisplacement_def]
    rw [DFP.AbstractSecantStep.displacement_def,
      DFP.AbstractSecantStep.preconditionedGradient_def,
      DFP.AbstractSecantStep.stepLength_def]
    dsimp [firstStep]
  · rw [State.middleMetric_def]
    have hmetric : (firstStep s h).nextInverseHessian =
        DFP.FirstLeg.outputMetric s.ε s.p s.h := by
      simpa using congrArg Prod.fst (firstStep_output s h)
    rw [hmetric]
  · rw [State.middleGradient_def]
    have hgradient : (firstStep s h).nextGradient =
        s.amplitude • DFP.FirstLeg.outputGradient s.ε s.p s.h := by
      simpa using congrArg Prod.snd (firstStep_output s h)
    rw [hgradient]
    rw [Matrix.mulVec_smul]
    rw [WithLp.toLp_smul]

/-- Phase validity implies exact agreement with the second abstract secant step. -/
theorem secondPhaseExact_of_phaseValidity (s : State) (h : PhaseValidity s) :
    SecondPhaseExact s h := by
  refine SecondPhaseExact.ofEqualities s h ?_ ?_ ?_
  · rw [State.secondDisplacement_def]
    rw [DFP.AbstractSecantStep.displacement_def,
      DFP.AbstractSecantStep.preconditionedGradient_def,
      DFP.AbstractSecantStep.stepLength_def]
    dsimp [secondStep]
  · have hmetric : (secondStep s h).nextInverseHessian =
        DFP.SecondLeg.outputMetric s.ε s.p s.h := by
      simpa using congrArg Prod.fst (secondStep_output s h)
    rw [hmetric]
    exact next_metric_eq_secondLegTransport s h
  · have hgradient : (secondStep s h).nextGradient =
        s.amplitude • DFP.SecondLeg.outputGradient s.ε s.p s.h := by
      simpa using congrArg Prod.snd (secondStep_output s h)
    rw [hgradient]
    exact next_gradient_eq_secondLegTransport s h

/-- Phase validity supplies the exact two-step abstract cycle certificate. -/
theorem exactCycle_of_phaseValidity (s : State) (h : PhaseValidity s) :
    ExactCycle s := by
  exact ExactCycle.ofPhases s h
    (firstPhaseExact_of_phaseValidity s h)
    (secondPhaseExact_of_phaseValidity s h)

end State

end DFP.TwoPhaseOrbit

namespace DFP

/-- An infinite physical orbit obtained by repeating the fixed exact two-phase transition. -/
structure TwoPhaseOrbit where
  state : ℕ → TwoPhaseOrbit.State
  state_succ : ∀ j, state (j + 1) = (state j).next

namespace TwoPhaseOrbit

/-- Iteration by the physical transition agrees with one further transition at a successor. -/
theorem iterateState_succ (s₀ : State) (j : ℕ) :
    State.next^[j + 1] s₀ = (State.next^[j] s₀).next := by
  simpa [Nat.succ_eq_add_one] using
    (Function.iterate_succ_apply' State.next j s₀)

/-- Generate the infinite orbit from one physical state by `Function.iterate`. -/
def ofState (s₀ : State) : DFP.TwoPhaseOrbit where
  state := fun j ↦ State.next^[j] s₀
  state_succ := iterateState_succ s₀

/-- Generate the physical two-phase orbit from a chosen slow curve and initial scale. -/
def ofSlowCurve (p h : ℝ → ℝ) (ε₀ : ℝ) : DFP.TwoPhaseOrbit :=
  ofState (State.initial p h ε₀)

/-- An iterated orbit starts at its prescribed physical state. -/
theorem ofState_zero (s₀ : State) : (ofState s₀).state 0 = s₀ := by
  rfl

/-- Every iterated orbit applies the complete physical transition at the successor index. -/
theorem ofState_succ (s₀ : State) (j : ℕ) :
    (ofState s₀).state (j + 1) = ((ofState s₀).state j).next := by
  exact (ofState s₀).state_succ j

/-- The slow-curve orbit starts at the explicit canonical physical state. -/
theorem ofSlowCurve_zero (p h : ℝ → ℝ) (ε₀ : ℝ) :
    (ofSlowCurve p h ε₀).state 0 = State.initial p h ε₀ := by
  rfl

/-- Every slow-curve orbit applies the complete physical transition at the successor index. -/
theorem ofSlowCurve_succ (p h : ℝ → ℝ) (ε₀ : ℝ) (j : ℕ) :
    (ofSlowCurve p h ε₀).state (j + 1) =
      ((ofSlowCurve p h ε₀).state j).next := by
  exact (ofSlowCurve p h ε₀).state_succ j

/-- The coordinates of the physical slow-curve orbit are the iterates of the signed
two-leg state map. -/
theorem ofSlowCurve_coordinates (p h : ℝ → ℝ) (ε₀ : ℝ) (j : ℕ) :
    ((ofSlowCurve p h ε₀).state j).coordinates =
      DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
  induction j with
  | zero =>
      rfl
  | succ j ih =>
      rw [ofSlowCurve_succ, State.next_coordinates, ih, Function.iterate_succ_apply']

/-- Every sufficiently small slow-curve orbit has valid phase data at every cycle. -/
theorem ofSlowCurve_phaseValidity (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (h_εbar : εbar ∈ Set.Ioo 0 (1 / 4)) :
    ∃ εmax ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 εmax, ∀ j : ℕ,
      State.PhaseValidity ((ofSlowCurve p h ε₀).state j) := by
  obtain ⟨εfactor, hεfactor, m, hm, hfactors⟩ :=
    DFP.TwoLeg.slowCurveFactorsUniformlyPositive p h h_invariant h_pJet h_hJet
      εbar h_εbar
  obtain ⟨ηgraph, hηgraph, hgraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηpos, hηpos, hpositive⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitPos p h h_invariant h_pJet h_hJet
  let εmax := min εfactor (min ηgraph ηpos)
  have hεmaxPos : 0 < εmax := by
    exact lt_min hεfactor.1 (lt_min hηgraph.1 hηpos)
  have hεmaxBar : εmax ≤ εbar := by
    exact (min_le_left εfactor (min ηgraph ηpos)).trans hεfactor.2
  refine ⟨εmax, ⟨hεmaxPos, hεmaxBar⟩, ?_⟩
  intro ε₀ hε₀
  have hεfactorMem : ε₀ ∈ Set.Ioc 0 εfactor := by
    exact ⟨hε₀.1, hε₀.2.trans (min_le_left εfactor (min ηgraph ηpos))⟩
  have hηgraphMem : ε₀ ∈ Set.Ioc 0 ηgraph := by
    have hεmaxGraph : εmax ≤ ηgraph := by
      exact (min_le_right εfactor (min ηgraph ηpos)).trans (min_le_left ηgraph ηpos)
    exact ⟨hε₀.1, hε₀.2.trans hεmaxGraph⟩
  have hηposMem : ε₀ ∈ Set.Ioc 0 ηpos := by
    have hεmaxPosBound : εmax ≤ ηpos := by
      exact (min_le_right εfactor (min ηgraph ηpos)).trans (min_le_right ηgraph ηpos)
    exact ⟨hε₀.1, hε₀.2.trans hεmaxPosBound⟩
  let orbit := ofSlowCurve p h ε₀
  have hvalidOfDynamic : ∀ j : ℕ,
      (orbit.state j).frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ →
        0 < (orbit.state j).amplitude → State.PhaseValidity (orbit.state j) := by
    intro j hframe hamplitude
    have hcoordinates :
        ((orbit.state j).ε, (orbit.state j).p, (orbit.state j).h) =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      have hraw := ofSlowCurve_coordinates p h ε₀ j
      simpa only [orbit, State.coordinates_def] using hraw
    have hpos := hpositive ε₀ hηposMem j
    dsimp only at hpos
    rw [← hcoordinates] at hpos
    have hgraphAt := hgraph ε₀ hηgraphMem j
    dsimp only at hgraphAt
    rw [← hcoordinates] at hgraphAt
    have hεlt : (orbit.state j).ε < 1 / 4 := by
      calc
        (orbit.state j).ε ≤ ε₀ := hgraphAt.2.2
        _ ≤ εmax := hε₀.2
        _ ≤ εbar := hεmaxBar
        _ < 1 / 4 := h_εbar.2
    have hfactor := hfactors ε₀ hεfactorMem j
    dsimp only at hfactor
    rw [← hcoordinates] at hfactor
    have hfirstSpectralLow :
        0 < (DFP.FirstLeg.spectralFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).1 := by
      exact lt_of_lt_of_le hm (hfactor 0)
    have hfirstSpectralHigh :
        0 < (DFP.FirstLeg.spectralFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).2 := by
      exact lt_of_lt_of_le hm (hfactor 1)
    have hfirstGradientLow :
        0 < (DFP.FirstLeg.gradientFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).1 := by
      exact lt_of_lt_of_le hm (hfactor 2)
    have hfirstGradientHigh :
        0 < (DFP.FirstLeg.gradientFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).2 := by
      exact lt_of_lt_of_le hm (hfactor 3)
    have hfirstRadius :
        0 < (DFP.FirstLeg.canonicalFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).1 := by
      exact lt_of_lt_of_le hm (hfactor 4)
    have hsecondSpectralLow :
        0 < (DFP.SecondLeg.spectralFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).1 := by
      exact lt_of_lt_of_le hm (hfactor 5)
    have hsecondSpectralHigh :
        0 < (DFP.SecondLeg.spectralFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).2 := by
      exact lt_of_lt_of_le hm (hfactor 6)
    have hsecondGradientLow :
        0 < (DFP.SecondLeg.gradientFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).1 := by
      exact lt_of_lt_of_le hm (hfactor 7)
    have hsecondGradientHigh :
        0 < (DFP.SecondLeg.gradientFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).2 := by
      exact lt_of_lt_of_le hm (hfactor 8)
    have hsecondRadius :
        0 < (DFP.SecondLeg.canonicalFactors
          (orbit.state j).ε (orbit.state j).p (orbit.state j).h).1 := by
      exact lt_of_lt_of_le hm (hfactor 9)
    exact State.PhaseValidity.ofComponents (orbit.state j) hframe hpos.1 hεlt
      hpos.2.1 hpos.2.2 hamplitude hfirstSpectralLow hfirstSpectralHigh
      hfirstGradientLow hfirstGradientHigh hfirstRadius hsecondSpectralLow
      hsecondSpectralHigh hsecondGradientLow hsecondGradientHigh hsecondRadius
  have hdynamic : ∀ j : ℕ,
      (orbit.state j).frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ ∧
        0 < (orbit.state j).amplitude := by
    intro j
    induction j with
    | zero =>
        have hzero : orbit.state 0 = State.initial p h ε₀ := by
          simpa only [orbit] using ofSlowCurve_zero p h ε₀
        constructor
        · rw [hzero, State.initial_frame]
          exact one_mem _
        · rw [hzero, State.initial_amplitude]
          norm_num
    | succ j ih =>
        have hvalid := hvalidOfDynamic j ih.1 ih.2
        have hsucc : orbit.state (j + 1) = (orbit.state j).next := by
          simpa only [orbit] using ofSlowCurve_succ p h ε₀ j
        constructor
        · rw [hsucc]
          exact State.nextFrame_mem_specialOrthogonal (orbit.state j) hvalid
        · rw [hsucc]
          exact State.nextAmplitude_pos (orbit.state j) hvalid
  intro j
  exact hvalidOfDynamic j (hdynamic j).1 (hdynamic j).2

/-- For every sufficiently small positive initial scale, every physical cycle has valid
oriented phase data and agrees exactly with both abstract inverse-form DFP steps. -/
theorem ofSlowCurveExact (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (εbar : ℝ) (h_εbar : εbar ∈ Set.Ioo 0 (1 / 4)) :
    ∃ εmax ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 εmax, ∀ j : ℕ,
      State.ExactCycle ((ofSlowCurve p h ε₀).state j) := by
  obtain ⟨εmax, hεmax, hvalid⟩ := ofSlowCurve_phaseValidity p h h_invariant
    h_pJet h_hJet εbar h_εbar
  refine ⟨εmax, hεmax, ?_⟩
  intro ε₀ hε₀ j
  exact State.exactCycle_of_phaseValidity ((ofSlowCurve p h ε₀).state j)
    (hvalid ε₀ hε₀ j)

end TwoPhaseOrbit

end DFP
