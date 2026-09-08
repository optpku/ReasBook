module

import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngle
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
public import ReasLib.Optimization.DFP.TwoPhaseControls.CenterJet
public import ReasLib.Analysis.Asymptotics.UniformRemainder.BigOToExplicit

public section

open Filter
open scoped Matrix Topology

namespace DFP.TwoPhaseOrbit.State

/-! The following small interfaces isolate the scalar and linear-algebra
plumbing used by the physical center identities. -/

/-- Scalar homogeneity of the raw inverse-form DFP displacement. -/
private theorem rawDisplacement_smul {n : Type*} [Fintype n]
    (H A : Matrix n n ℝ) (g : n → ℝ) (τ G : ℝ) :
    let v := H.mulVec g
    let α := τ * (g ⬝ᵥ v) / (v ⬝ᵥ (A.mulVec v))
    let gG := G • g
    let vG := H.mulVec gG
    let αG := τ * (gG ⬝ᵥ vG) / (vG ⬝ᵥ (A.mulVec vG))
    (- (αG • vG)) = G • (- (α • v)) := by
  by_cases hG : G = 0
  · subst G
    simp
  · dsimp only
    rw [Matrix.mulVec_smul]
    simp only [smul_dotProduct, dotProduct_smul, Matrix.mulVec_smul]
    have hGsq : G * G ≠ 0 := mul_ne_zero hG hG
    funext i
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hGsq]

/-- Scalar homogeneity of a raw inverse-form displacement remains valid after
transport by a planar matrix and the `WithLp` embedding. -/
private theorem rawDisplacement_smul_toLp
    (M H A : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ) (τ G : ℝ) :
    let v := H.mulVec g
    let α := τ * (g ⬝ᵥ v) / (v ⬝ᵥ (A.mulVec v))
    let gG := G • g
    let vG := H.mulVec gG
    let αG := τ * (gG ⬝ᵥ vG) / (vG ⬝ᵥ (A.mulVec vG))
    WithLp.toLp 2 (M.mulVec (-(αG • vG))) =
      G • WithLp.toLp 2 (M.mulVec (-(α • v))) := by
  dsimp only
  have h := rawDisplacement_smul H A g τ G
  have hM := congrArg
    (fun z : Fin 2 → ℝ => WithLp.toLp 2 (M.mulVec z)) h
  simpa only [WithLp.toLp_smul, Matrix.mulVec_smul] using hM

/-- The center `x - g` at the intermediate endpoint of a physical two-phase cycle. -/
noncomputable def middleCenter (s : State) : EuclideanSpace ℝ (Fin 2) :=
  s.middlePoint - s.middleGradient

/-- The intermediate center is the difference of the intermediate point and gradient. -/
theorem middleCenter_def (s : State) :
    s.middleCenter = s.middlePoint - s.middleGradient := by
  rfl

/-- The physical center displacement during the first half of a two-phase cycle. -/
noncomputable def halfCenterDisplacement (s : State) : EuclideanSpace ℝ (Fin 2) :=
  s.middleCenter - s.center

/-- The first-half center displacement is the intermediate center minus the initial center. -/
theorem halfCenterDisplacement_def (s : State) :
    s.halfCenterDisplacement = s.middleCenter - s.center := by
  rfl

/-- The physical first-half center displacement is the normalized two-leg observable,
transported by the incoming frame and scaled by the physical amplitude. -/
theorem halfCenterDisplacement_observable (s : State) :
    s.halfCenterDisplacement = s.amplitude • WithLp.toLp 2
      (s.frame *ᵥ (DFP.TwoLeg.observableMap s.coordinates).halfCenterDisplacement) := by
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), s.p * s.ε ^ 2]
  let A := (TwoPhaseControls.first s.ε).matrix
  let τ := (TwoPhaseControls.first s.ε).tau
  have hscale := rawDisplacement_smul H A g₀ τ s.amplitude
  have hobs := congrArg Prod.fst
    (DFP.TwoLeg.observableMap_centerDisplacements s.ε s.p s.h)
  rw [halfCenterDisplacement_def, middleCenter_def, State.center_def,
    State.middlePoint_def, State.middleGradient_def, State.gradient_def]
  rw [State.coordinates_def]
  rw [State.firstDisplacement_def]
  dsimp only
  change s.point +
      WithLp.toLp 2 (s.frame *ᵥ (-(
        (τ * ((s.amplitude • g₀) ⬝ᵥ (H.mulVec (s.amplitude • g₀))) /
          ((H.mulVec (s.amplitude • g₀)) ⬝ᵥ
            (A.mulVec (H.mulVec (s.amplitude • g₀))))) •
        (H.mulVec (s.amplitude • g₀))))) -
      s.amplitude • WithLp.toLp 2 (s.frame *ᵥ DFP.FirstLeg.outputGradient s.ε s.p s.h) -
      (s.point - s.amplitude • WithLp.toLp 2 (s.frame *ᵥ g₀)) =
    s.amplitude • WithLp.toLp 2
      (s.frame *ᵥ (DFP.TwoLeg.observableMap (s.ε, s.p, s.h)).halfCenterDisplacement)
  have hframeObs := congrArg
    (fun z : EuclideanSpace ℝ (Fin 2) => WithLp.toLp 2 (s.frame *ᵥ z)) hobs
  rw [hframeObs]
  dsimp only
  rw [hscale]
  simp only [WithLp.toLp_sub, WithLp.toLp_neg, WithLp.toLp_smul,
    WithLp.ofLp_sub,
    WithLp.ofLp_smul, WithLp.ofLp_neg,
    Matrix.mulVec_sub, Matrix.mulVec_smul]
  module

/-- The physical first displacement is the incoming-frame transport of its
normalized raw displacement, scaled by the physical amplitude. -/
private theorem firstDisplacement_eq_scaledRaw (s : State) :
    let H : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![s.h * s.p * s.ε ^ 4, s.h]
    let g : Fin 2 → ℝ := ![(1 : ℝ), s.p * s.ε ^ 2]
    let v := H *ᵥ g
    let A := (TwoPhaseControls.first s.ε).matrix
    let α := (TwoPhaseControls.first s.ε).tau * (g ⬝ᵥ v) / (v ⬝ᵥ (A *ᵥ v))
    s.firstDisplacement =
      s.amplitude • WithLp.toLp 2 (s.frame *ᵥ (- (α • v))) := by
  dsimp only
  rw [State.firstDisplacement_def]
  dsimp only
  rw [rawDisplacement_smul]
  rw [Matrix.mulVec_smul, WithLp.toLp_smul]

/-- The physical second displacement is the incoming-frame transport of its
normalized first-eigenframe displacement, scaled by the physical amplitude. -/
private theorem secondDisplacement_eq_scaledRaw (s : State) :
    let spectral := DFP.FirstLeg.spectralFactors s.ε s.p s.h
    let gradient := DFP.FirstLeg.gradientFactors s.ε s.p s.h
    let H : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![s.ε ^ 4 * spectral.1, spectral.2]
    let g : Fin 2 → ℝ := ![gradient.1, s.ε ^ 2 * gradient.2]
    let v := H *ᵥ g
    let A := (TwoPhaseControls.second s.ε).matrix
    let α := (TwoPhaseControls.second s.ε).tau * (g ⬝ᵥ v) / (v ⬝ᵥ (A *ᵥ v))
    s.secondDisplacement = s.amplitude • WithLp.toLp 2
      (s.frame *ᵥ (DFP.FirstLeg.frame s.ε s.p s.h *ᵥ (- (α • v)))) := by
  dsimp only
  rw [State.secondDisplacement_def, State.middleFrame_def]
  dsimp only
  rw [rawDisplacement_smul]
  simp only [Matrix.mulVec_smul, WithLp.toLp_smul, Matrix.mulVec_mulVec]

/-- The Euclidean norm of a planar vector is bounded by the sum of the absolute
values of its two coordinates. -/
private theorem euclideanNorm_le_abs_add_abs (v : Fin 2 → ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ |v 0| + |v 1| := by
  have hnorm := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)
  rw [Fin.sum_univ_two] at hnorm
  have hproduct : 0 ≤ |v 0| * |v 1| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [norm_nonneg (WithLp.toLp 2 v), abs_nonneg (v 0), abs_nonneg (v 1),
    sq_abs (v 0), sq_abs (v 1)]

/-- Multiplication by the first standard basis vector extracts the low column of
a physical frame. -/
private theorem frame_mulVec_lowBasis (s : State) :
    WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 0]) = s.lowVector := by
  ext i
  rw [State.lowVector_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Adding a normalized low-coordinate correction before transport agrees with
adding the corresponding physical low-vector correction after scaling. -/
private theorem scaledFullObservable_add_lowCorrection (s : State) :
    s.amplitude • WithLp.toLp 2
        (s.frame *ᵥ (DFP.TwoLeg.observableMap s.coordinates).fullCenterDisplacement) +
      ((116 / 5) * s.amplitude * s.ε ^ 6) • s.lowVector =
    s.amplitude • WithLp.toLp 2 (s.frame *ᵥ
      ![(DFP.TwoLeg.observableMap s.coordinates).fullCenterDisplacement 0 +
          (116 / 5) * s.ε ^ 6,
        (DFP.TwoLeg.observableMap s.coordinates).fullCenterDisplacement 1]) := by
  rw [← frame_mulVec_lowBasis]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- For a valid physical phase, the first-half center-displacement norm is the
amplitude times the norm of its normalized two-leg observable. -/
theorem norm_halfCenterDisplacement (s : State) (h : PhaseValidity s) :
    ‖s.halfCenterDisplacement‖ =
      s.amplitude * ‖(DFP.TwoLeg.observableMap s.coordinates).halfCenterDisplacement‖ := by
  rw [halfCenterDisplacement_observable]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos h.amplitude_pos]
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    s.frame h.frame_specialOrthogonal]

/-- For a valid phase, the successor gradient is the normalized second-leg output,
transported by the middle frame and scaled by the incoming amplitude. -/
private theorem nextGradient_eq_secondOutput (s : State) (h : PhaseValidity s) :
    s.next.gradient = s.amplitude • WithLp.toLp 2
      (s.middleFrame *ᵥ DFP.SecondLeg.outputGradient s.ε s.p s.h) := by
  have hexact := (secondPhaseExact_of_phaseValidity s h).gradient
  have houtput : (secondStep s h).nextGradient =
      s.amplitude • DFP.SecondLeg.outputGradient s.ε s.p s.h := by
    simpa only using congrArg Prod.snd (secondStep_output s h)
  rw [houtput, Matrix.mulVec_smul, WithLp.toLp_smul] at hexact
  exact hexact

/-- The physical full-cycle center displacement is the normalized two-leg observable,
transported by the incoming frame and scaled by the physical amplitude. -/
theorem fullCenterDisplacement_observable (s : State) (hvalid : PhaseValidity s) :
    s.next.center - s.center = s.amplitude • WithLp.toLp 2
      (s.frame *ᵥ (DFP.TwoLeg.observableMap s.coordinates).fullCenterDisplacement) := by
  have hobservable := congrArg Prod.snd
    (DFP.TwoLeg.observableMap_centerDisplacements s.ε s.p s.h)
  have hframeObservable := congrArg
    (fun z : EuclideanSpace ℝ (Fin 2) ↦ WithLp.toLp 2 (s.frame *ᵥ z)) hobservable
  have hnextGradient := nextGradient_eq_secondOutput s hvalid
  rw [State.center_def, State.next_point, State.middlePoint_def, State.center_def]
  rw [hnextGradient, firstDisplacement_eq_scaledRaw,
    secondDisplacement_eq_scaledRaw, State.gradient_def]
  rw [State.coordinates_def]
  dsimp only
  rw [hframeObservable]
  simp only [WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_neg,
    WithLp.toLp_smul, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_neg,
    WithLp.ofLp_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_neg,
    Matrix.mulVec_smul, State.middleFrame_def, Matrix.mulVec_mulVec]
  module

/-- For a valid phase, the full physical center error after removing its leading
low-vector drift is the corrected normalized observable transported by the frame. -/
private theorem fullCenterError_eq_scaledCorrectedObservable
    (s : State) (hvalid : PhaseValidity s) :
    s.next.center - s.center +
        ((116 / 5) * s.amplitude * s.ε ^ 6) • s.lowVector =
      s.amplitude • WithLp.toLp 2 (s.frame *ᵥ
        ![(DFP.TwoLeg.observableMap s.coordinates).fullCenterDisplacement 0 +
            (116 / 5) * s.ε ^ 6,
          (DFP.TwoLeg.observableMap s.coordinates).fullCenterDisplacement 1]) := by
  rw [fullCenterDisplacement_observable s hvalid]
  exact scaledFullObservable_add_lowCorrection s

end DFP.TwoPhaseOrbit.State

namespace DFP.TwoPhaseOrbit

/-- The normalized full-center displacement, after canceling its sixth-order low
term, is a seventh-order vector remainder along every prescribed slow graph. -/
private theorem slowFullCorrectedObservable_isBigO (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦ WithLp.toLp 2
      ![(DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 +
          (116 / 5) * ε ^ 6,
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 1]) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  have hSevenEight : (7 : ℕ) < 8 := by
    norm_num
  have hSevenNine : (7 : ℕ) < 9 := by
    norm_num
  have hEightSeven :
      (fun ε : ℝ ↦ ε ^ 8) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 7) :=
    (Asymptotics.isLittleO_pow_pow hSevenEight).isBigO
  have hNineSeven :
      (fun ε : ℝ ↦ ε ^ 9) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 7) :=
    (Asymptotics.isLittleO_pow_pow hSevenNine).isBigO
  have hLowTail :=
    (DFP.TwoLeg.CenterJet.slowFullLowRemainder p h h_pJet h_hJet).trans hEightSeven
  have hLowSeventh :
      (fun ε : ℝ ↦ (38 / 5 : ℝ) * ε ^ 7) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 7) (𝓝 0)).const_mul_left (38 / 5)
  have hLowSum := hLowTail.add hLowSeventh
  have hLowIdentity (ε : ℝ) :
      ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 -
          (-(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7)) +
          (38 / 5) * ε ^ 7 =
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 +
          (116 / 5) * ε ^ 6 := by
    ring
  have hLow := hLowSum.congr_left hLowIdentity
  have hHighTail :=
    (DFP.TwoLeg.CenterJet.slowFullHighRemainder p h h_pJet h_hJet).trans hNineSeven
  have hEightCorrection :
      (fun ε : ℝ ↦ -(508 / 5 : ℝ) * ε ^ 8) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    hEightSeven.const_mul_left (-(508 / 5))
  have hHighSum := hHighTail.add hEightCorrection
  have hHighIdentity (ε : ℝ) :
      ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 1 -
          (-(508 / 5) * ε ^ 8)) + (-(508 / 5) * ε ^ 8) =
        (DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 1 := by
    ring
  have hHigh := hHighSum.congr_left hHighIdentity
  obtain ⟨Clow, hLowBound⟩ := hLow.bound
  obtain ⟨Chigh, hHighBound⟩ := hHigh.bound
  apply Asymptotics.IsBigO.of_bound (Clow + Chigh)
  filter_upwards [hLowBound, hHighBound] with ε hLowε hHighε
  calc
    ‖WithLp.toLp 2
        ![(DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 +
            (116 / 5) * ε ^ 6,
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 1]‖ ≤
        |(DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 +
            (116 / 5) * ε ^ 6| +
          |(DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 1| := by
      simpa using State.euclideanNorm_le_abs_add_abs
        ![(DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 +
            (116 / 5) * ε ^ 6,
          (DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 1]
    _ =
        ‖(DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 +
            (116 / 5) * ε ^ 6‖ +
          ‖(DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 1‖ := by
      simp only [Real.norm_eq_abs]
    _ ≤ Clow * ‖ε ^ 7‖ + Chigh * ‖ε ^ 7‖ :=
      add_le_add hLowε hHighε
    _ = (Clow + Chigh) * ‖ε ^ 7‖ := by
      ring

/-- Along every sufficiently small invariant slow-curve orbit, the physical
first-half center displacement is bounded asymptotically by the amplitude times
the cube of the cycle scale. -/
theorem slowCurveHalfCenterDisplacement (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      (fun j : ℕ ↦ ‖(orbit.state j).halfCenterDisplacement‖) =O[atTop]
        (fun j : ℕ ↦ (orbit.state j).amplitude * (orbit.state j).ε ^ 3) := by
  have hNormalized := DFP.TwoLeg.CenterJet.slowHalfBound p h h_pJet h_hJet
  obtain ⟨C, hLocalEventually⟩ := hNormalized.bound
  obtain ⟨δ, hδ, hLocal⟩ := Metric.eventually_nhds_iff.mp hLocalEventually
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  have hEighthRange : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) hEighthRange
  let εbar := min (min ηGraph ηValid) (δ / 2)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min (lt_min hηGraph.1 hηValid.1) (half_pos hδ)
  refine ⟨εbar, hεbarPos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 ηValid :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε₀DeltaHalf : ε₀ ≤ δ / 2 :=
    hε₀.2.trans (min_le_right _ _)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [] with j
  let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
  obtain ⟨hGraphCoordinates, hScaleRange⟩ := hGraph ε₀ hε₀Graph j
  have hScalePos : 0 < xj.1 := hScaleRange.1
  have hScaleDelta : xj.1 < δ :=
    hScaleRange.2.trans_lt
      (hε₀DeltaHalf.trans_lt (half_lt_self hδ))
  have hDistance : dist xj.1 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hScalePos]
    exact hScaleDelta
  have hLocalBound := hLocal hDistance
  have hCoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  have hCoordinates' : (orbit.state j).coordinates = xj := by
    simpa only [orbit, xj] using hCoordinates
  have hOrbitCoordinates : (orbit.state j).coordinates =
      (xj.1, p xj.1, h xj.1) := hCoordinates'.trans hGraphCoordinates
  have hScale : (orbit.state j).ε = xj.1 := by
    rw [State.coordinates_def] at hCoordinates'
    exact congrArg Prod.fst hCoordinates'
  have hPhase : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hε₀Valid j
  have hPhysicalNorm := State.norm_halfCenterDisplacement (orbit.state j) hPhase
  have hScaleCubePos : 0 < (orbit.state j).ε ^ 3 :=
    pow_pos hPhase.ε_pos 3
  have hAmplitudeScalePos :
      0 < (orbit.state j).amplitude * (orbit.state j).ε ^ 3 :=
    mul_pos hPhase.amplitude_pos hScaleCubePos
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hPhysicalNorm, hOrbitCoordinates]
  rw [Real.norm_eq_abs, abs_of_pos hAmplitudeScalePos]
  rw [hScale]
  have hScaleCubeNorm : ‖xj.1 ^ 3‖ = xj.1 ^ 3 := by
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos hScalePos 3)]
  rw [hScaleCubeNorm] at hLocalBound
  have hScaledBound :=
    mul_le_mul_of_nonneg_left hLocalBound hPhase.amplitude_pos.le
  calc
    (orbit.state j).amplitude *
        ‖(DFP.TwoLeg.observableMap
          (xj.1, p xj.1, h xj.1)).halfCenterDisplacement‖ ≤
      (orbit.state j).amplitude * (C * xj.1 ^ 3) := hScaledBound
    _ = C * ((orbit.state j).amplitude * xj.1 ^ 3) := by ring

/-- Along all sufficiently small invariant slow-curve orbits, one positive
constant uniformly bounds every physical first-half center displacement by the
amplitude times the cube of the cycle scale. -/
theorem slowCurveHalfCenterDisplacementBound (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Chalf > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
        let s := (DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j
        ‖s.halfCenterDisplacement‖ ≤ Chalf * s.amplitude * s.ε ^ 3 := by
  have hNormalized := DFP.TwoLeg.CenterJet.slowHalfBound p h h_pJet h_hJet
  obtain ⟨C, hLocalEventually⟩ := hNormalized.bound
  obtain ⟨δ, hδ, hLocal⟩ := Metric.eventually_nhds_iff.mp hLocalEventually
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  have hEighthRange : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by
    norm_num
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      (1 / 8) hEighthRange
  let εbar := min (min ηGraph ηValid) (δ / 2)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min (lt_min hηGraph.1 hηValid.1) (half_pos hδ)
  have hεbarLt : εbar < (1 / 4 : ℝ) := by
    have hεbarValid : εbar ≤ ηValid :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hηValidLt : ηValid < (1 / 4 : ℝ) :=
      hηValid.2.trans_lt hEighthRange.2
    exact hεbarValid.trans_lt hηValidLt
  let Chalf := max C 1
  have hOnePos : 0 < (1 : ℝ) := by norm_num
  have hChalfPos : 0 < Chalf := by
    dsimp only [Chalf]
    exact hOnePos.trans_le (le_max_right C 1)
  have hCLe : C ≤ Chalf := by
    dsimp only [Chalf]
    exact le_max_left C 1
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Chalf, hChalfPos, ?_⟩
  intro ε₀ hε₀ j
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 ηValid :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hε₀DeltaHalf : ε₀ ≤ δ / 2 :=
    hε₀.2.trans (min_le_right _ _)
  let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
  obtain ⟨hGraphCoordinates, hScaleRange⟩ := hGraph ε₀ hε₀Graph j
  have hScalePos : 0 < xj.1 := hScaleRange.1
  have hScaleDelta : xj.1 < δ :=
    hScaleRange.2.trans_lt
      (hε₀DeltaHalf.trans_lt (half_lt_self hδ))
  have hDistance : dist xj.1 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hScalePos]
    exact hScaleDelta
  have hLocalBound := hLocal hDistance
  have hCoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  have hCoordinates' : (orbit.state j).coordinates = xj := by
    simpa only [orbit, xj] using hCoordinates
  have hOrbitCoordinates : (orbit.state j).coordinates =
      (xj.1, p xj.1, h xj.1) := hCoordinates'.trans hGraphCoordinates
  have hScale : (orbit.state j).ε = xj.1 := by
    rw [State.coordinates_def] at hCoordinates'
    exact congrArg Prod.fst hCoordinates'
  have hPhase : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hε₀Valid j
  have hPhysicalNorm := State.norm_halfCenterDisplacement (orbit.state j) hPhase
  have hScaleCubeNonneg : 0 ≤ xj.1 ^ 3 := (pow_pos hScalePos 3).le
  have hScaleCubeNorm : ‖xj.1 ^ 3‖ = xj.1 ^ 3 := by
    rw [Real.norm_eq_abs, abs_of_pos (pow_pos hScalePos 3)]
  rw [hScaleCubeNorm] at hLocalBound
  have hConstantBound : C * xj.1 ^ 3 ≤ Chalf * xj.1 ^ 3 :=
    mul_le_mul_of_nonneg_right hCLe hScaleCubeNonneg
  have hLocalChalfBound := hLocalBound.trans hConstantBound
  have hScaledBound :=
    mul_le_mul_of_nonneg_left hLocalChalfBound hPhase.amplitude_pos.le
  rw [hPhysicalNorm, hOrbitCoordinates, hScale]
  calc
    (orbit.state j).amplitude *
        ‖(DFP.TwoLeg.observableMap
          (xj.1, p xj.1, h xj.1)).halfCenterDisplacement‖ ≤
      (orbit.state j).amplitude * (Chalf * xj.1 ^ 3) := hScaledBound
    _ = Chalf * (orbit.state j).amplitude * xj.1 ^ 3 := by ring

/-- Along every sufficiently small invariant slow-curve orbit, one physical cycle
changes the center by `-(116 / 5) * G * ε ^ 6` times the physical low vector,
up to a vector remainder bounded by a constant multiple of `G * ε ^ 7`. -/
theorem slowCurveFullCenterDrift (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Ccenter > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      let s := orbit.state j
      ‖(orbit.state (j + 1)).center - s.center +
        ((116 / 5) * s.amplitude * s.ε ^ 6) • s.lowVector‖ ≤
          Ccenter * s.amplitude * s.ε ^ 7 := by
  have hNormalized := slowFullCorrectedObservable_isBigO p h h_pJet h_hJet
  obtain ⟨Ccenter, hCcenter, δ, hδ, hLocal⟩ :=
    Asymptotics.IsUniformRemainderOn.exists_pos_natPow_bound_of_isBigO hNormalized
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity p h h_invariant h_pJet h_hJet
      ηGraph hηGraph
  let εbar := min ηValid (δ / 2)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηValid.1 (half_pos hδ)
  have hεbarLt : εbar < 1 / 4 := by
    exact lt_of_le_of_lt ((min_le_left _ _).trans hηValid.2) hηGraph.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Ccenter, hCcenter, ?_⟩
  intro ε₀ hε₀ j
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
  have hε₀Valid : ε₀ ∈ Set.Ioc 0 ηValid :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀Valid.2.trans hηValid.2⟩
  have hε₀DeltaHalf : ε₀ ≤ δ / 2 :=
    hε₀.2.trans (min_le_right _ _)
  obtain ⟨hGraphCoordinates, hScaleRange⟩ := hGraph ε₀ hε₀Graph j
  have hScalePos : 0 < xj.1 := hScaleRange.1
  have hScaleDelta : |xj.1| < δ := by
    rw [abs_of_pos hScalePos]
    exact hScaleRange.2.trans_lt
      (hε₀DeltaHalf.trans_lt (half_lt_self hδ))
  have hLocalBound := hLocal xj.1 hScaleDelta
  have hCoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  have hCoordinates' : (orbit.state j).coordinates = xj := by
    simpa only [orbit, xj] using hCoordinates
  have hOrbitCoordinates : (orbit.state j).coordinates =
      (xj.1, p xj.1, h xj.1) := hCoordinates'.trans hGraphCoordinates
  have hScale : (orbit.state j).ε = xj.1 := by
    rw [State.coordinates_def] at hCoordinates'
    exact congrArg Prod.fst hCoordinates'
  have hPhase : State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hε₀Valid j
  have hSuccessor := DFP.TwoPhaseOrbit.ofSlowCurve_succ p h ε₀ j
  have hLocalBound' :
      ‖WithLp.toLp 2
        ![(DFP.TwoLeg.observableMap (xj.1, p xj.1, h xj.1)).fullCenterDisplacement 0 +
            (116 / 5) * xj.1 ^ 6,
          (DFP.TwoLeg.observableMap (xj.1, p xj.1, h xj.1)).fullCenterDisplacement 1]‖ ≤
        Ccenter * xj.1 ^ 7 := by
    simpa only [abs_of_pos hScalePos] using hLocalBound
  rw [hSuccessor]
  rw [State.fullCenterError_eq_scaledCorrectedObservable (orbit.state j) hPhase]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hPhase.amplitude_pos]
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    (orbit.state j).frame hPhase.frame_specialOrthogonal]
  rw [hOrbitCoordinates, hScale]
  calc
    (orbit.state j).amplitude *
        ‖WithLp.toLp 2
          ![(DFP.TwoLeg.observableMap (xj.1, p xj.1, h xj.1)).fullCenterDisplacement 0 +
              (116 / 5) * xj.1 ^ 6,
            (DFP.TwoLeg.observableMap (xj.1, p xj.1, h xj.1)).fullCenterDisplacement 1]‖ ≤
      (orbit.state j).amplitude * (Ccenter * xj.1 ^ 7) :=
        mul_le_mul_of_nonneg_left hLocalBound' hPhase.amplitude_pos.le
    _ = Ccenter * (orbit.state j).amplitude * xj.1 ^ 7 := by
      ring

/-- Any prescribed positive threshold below `1 / 4` admits a smaller threshold
with the same uniform full-cycle center-drift estimate. -/
theorem slowCurveFullCenterDriftBound (p h : ℝ → ℝ)
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
    ∃ εmax ∈ Set.Ioc 0 εbar, ∃ Ccenter > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εmax, ∀ j : ℕ,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        let s := orbit.state j
        ‖(orbit.state (j + 1)).center - s.center +
            ((116 / 5) * s.amplitude * s.ε ^ 6) • s.lowVector‖ ≤
          Ccenter * s.amplitude * s.ε ^ 7 := by
  obtain ⟨εbar', hεbar', Ccenter, hCcenter, hbound⟩ :=
    slowCurveFullCenterDrift p h h_invariant h_pJet h_hJet
  let εmax := min εbar' εbar
  have hεmaxPos : 0 < εmax := by
    dsimp only [εmax]
    exact lt_min hεbar'.1 h_εbar.1
  have hεmaxLe : εmax ≤ εbar := by
    exact min_le_right _ _
  refine ⟨εmax, ⟨hεmaxPos, hεmaxLe⟩, Ccenter, hCcenter, ?_⟩
  intro ε₀ hε₀ j
  apply hbound ε₀
  exact ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩

end DFP.TwoPhaseOrbit
