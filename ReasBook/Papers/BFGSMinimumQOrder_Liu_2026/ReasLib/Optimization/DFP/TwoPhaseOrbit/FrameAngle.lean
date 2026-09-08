module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.Continuity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
import all ReasLib.Geometry.Euclidean.Plane.Rotation
import all ReasLib.Optimization.DFP.TwoPhaseOrbit
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open Filter
open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoPhaseOrbit.State

/-- The physical low eigenvector is the first column of a state's oriented frame. -/
def lowVector (s : State) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i ↦ s.frame i 0)

/-- The coordinates of the physical low eigenvector are the first frame column. -/
theorem lowVector_apply (s : State) (i : Fin 2) :
    s.lowVector i = s.frame i 0 := by
  rfl

/-- The relative oriented frame update performed by the two exact DFP legs. -/
def relativeFrame (s : State) : Matrix (Fin 2) (Fin 2) ℝ :=
  DFP.FirstLeg.frame s.ε s.p s.h * DFP.SecondLeg.frame s.ε s.p s.h

/-- The successor frame is the incoming frame followed by its relative update. -/
theorem next_frame_eq_frame_mul_relativeFrame (s : State) :
    s.next.frame = s.frame * s.relativeFrame := by
  rw [next_frame, relativeFrame, DFP.TwoPhaseOrbit.State.middleFrame_def]
  rw [Matrix.mul_assoc]

/-- The small signed real angle assigned to one relative oriented frame update. -/
def angleIncrement (s : State) : ℝ :=
  EuclideanPlane.SignedAngle.coordinate s.relativeFrame

/-- Every frame-angle increment lies in the local arctangent branch. -/
theorem angleIncrement_mem_interval (s : State) :
    s.angleIncrement ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  exact EuclideanPlane.SignedAngle.coordinate_mem_interval s.relativeFrame

/-- On the signed-angle chart, the frame-angle increment is the unique small real
parameter representing the relative frame. -/
theorem angleIncrement_unique (s : State)
    (h_specialOrthogonal : s.relativeFrame ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (h_chart : s.relativeFrame ∈ EuclideanPlane.SignedAngle.chart)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    EuclideanPlane.rotationMatrix θ = s.relativeFrame ↔ θ = s.angleIncrement := by
  exact EuclideanPlane.SignedAngle.coordinate_unique s.relativeFrame θ
    h_specialOrthogonal h_chart hθ

end DFP.TwoPhaseOrbit.State

namespace DFP.TwoPhaseOrbit

/-- Planar rotation matrices turn addition of real angle representatives into
matrix multiplication. -/
private theorem rotationMatrix_add (theta phi : ℝ) :
    EuclideanPlane.rotationMatrix ((theta + phi : ℝ) : Real.Angle) =
      EuclideanPlane.rotationMatrix theta * EuclideanPlane.rotationMatrix phi := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [EuclideanPlane.rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Real.Angle.cos_add, Real.Angle.sin_add] <;>
    ring

/-- The recursively accumulated real lift of a physical orbit's frame angle. -/
def frameAngle (orbit : DFP.TwoPhaseOrbit) : ℕ → ℝ
  | 0 => 0
  | j + 1 => frameAngle orbit j + (orbit.state j).angleIncrement

/-- The accumulated frame angle starts at zero. -/
theorem frameAngle_zero (orbit : DFP.TwoPhaseOrbit) : orbit.frameAngle 0 = 0 := by
  rfl

/-- The accumulated frame angle advances by the current relative-frame angle. -/
theorem frameAngle_succ (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.frameAngle (j + 1) =
      orbit.frameAngle j + (orbit.state j).angleIncrement := by
  rfl

/-- If an orbit starts in the identity frame and all relative updates remain in the
signed-angle chart, its accumulated angle rotates the initial low vector to the
current physical low vector. -/
theorem frameAngleRepresentsLowVector (orbit : DFP.TwoPhaseOrbit)
    (h_initialFrame : (orbit.state 0).frame = 1)
    (h_specialOrthogonal : ∀ j, (orbit.state j).relativeFrame ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ)
    (h_chart : ∀ j, (orbit.state j).relativeFrame ∈
      EuclideanPlane.SignedAngle.chart) (j : ℕ) :
    (orbit.state j).lowVector =
      EuclideanPlane.rotation (orbit.frameAngle j) (orbit.state 0).lowVector := by
  have hframe : ∀ k : ℕ, (orbit.state k).frame =
      EuclideanPlane.rotationMatrix (orbit.frameAngle k) := by
    intro k
    induction k with
    | zero =>
        rw [h_initialFrame, frameAngle_zero]
        ext i l
        fin_cases i <;> fin_cases l <;>
          simp [EuclideanPlane.rotationMatrix]
    | succ k ih =>
        have hrelative : EuclideanPlane.rotationMatrix
            (orbit.state k).angleIncrement = (orbit.state k).relativeFrame :=
          EuclideanPlane.SignedAngle.rotationMatrix_coordinate
            (orbit.state k).relativeFrame (h_specialOrthogonal k) (h_chart k)
        calc
          (orbit.state (k + 1)).frame =
              (orbit.state k).frame * (orbit.state k).relativeFrame := by
                rw [orbit.state_succ k]
                exact State.next_frame_eq_frame_mul_relativeFrame (orbit.state k)
          _ = EuclideanPlane.rotationMatrix (orbit.frameAngle k) *
              EuclideanPlane.rotationMatrix (orbit.state k).angleIncrement := by
                rw [ih, hrelative]
          _ = EuclideanPlane.rotationMatrix
              ((orbit.frameAngle k + (orbit.state k).angleIncrement : ℝ) :
                Real.Angle) :=
                (rotationMatrix_add _ _).symm
          _ = EuclideanPlane.rotationMatrix (orbit.frameAngle (k + 1)) := by
                rw [frameAngle_succ]
  ext i
  fin_cases i <;>
    simp [State.lowVector, hframe j, h_initialFrame, EuclideanPlane.rotation_apply,
      EuclideanPlane.rotationMatrix, EuclideanPlane.perp_apply]

/-- Every sufficiently small invariant slow-curve orbit has special-orthogonal
relative frames in the signed-angle chart. -/
private theorem slowCurveRelativeFrameConditions (p h : ℝ → ℝ)
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
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      (orbit.state j).relativeFrame ∈
          Matrix.specialOrthogonalGroup (Fin 2) ℝ ∧
        (orbit.state j).relativeFrame ∈ EuclideanPlane.SignedAngle.chart := by
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 :=
      (continuousAt_id : ContinuousAt (fun ε : ℝ ↦ ε) 0).pow 5
    convert hcont.tendsto using 1
    norm_num
  have hpRemainder : Tendsto
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4))
      (𝓝 0) (𝓝 0) :=
    h_pJet.trans_tendsto hpowFive
  have hhRemainder : Tendsto
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) (𝓝 0) (𝓝 0) :=
    h_hJet.trans_tendsto hpowFive
  have hpPolynomial : Tendsto
      (fun ε : ℝ ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)
      (𝓝 0) (𝓝 2) := by
    have hcont : ContinuousAt
        (fun ε : ℝ ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4) 0 := by
      fun_prop
    convert hcont.tendsto using 1
    norm_num
  have hhPolynomial : Tendsto (fun ε : ℝ ↦ 1 + 8 * ε ^ 3) (𝓝 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun ε : ℝ ↦ 1 + 8 * ε ^ 3) 0 := by
      fun_prop
    convert hcont.tendsto using 1
    norm_num
  have hp : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using hpRemainder.add hpPolynomial
  have hh : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using hhRemainder.add hhPolynomial
  have hstate : Tendsto (fun ε : ℝ ↦ (ε, p ε, h ε)) (𝓝 0) (𝓝 (0, 2, 1)) :=
    tendsto_id.prodMk_nhds (hp.prodMk_nhds hh)
  have hfirstLowChart : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0 <
        DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 := by
    apply (DFP.FirstLeg.outputMetricEntry_continuousAt 0 0).eventually_lt
      (DFP.FirstLeg.outputMetricEntry_continuousAt 1 1)
    norm_num [DFP.FirstLeg.outputMetric]
  have hsecondLowChart : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0 <
        DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1 := by
    apply (DFP.SecondLeg.outputMetricEntry_continuousAt 0 0).eventually_lt
      (DFP.SecondLeg.outputMetricEntry_continuousAt 1 1)
    have hbase : DFP.SecondLeg.outputMetric 0 2 1 0 0 <
        DFP.SecondLeg.outputMetric 0 2 1 1 1 := by
      have hdenom : RealSymmetric2.lowDenom 0 0 1 = 1 := by
        norm_num [RealSymmetric2.lowDenom, RealSymmetric2.low,
          RealSymmetric2.gap]
      norm_num [DFP.SecondLeg.outputMetric, DFP.FirstLeg.spectralFactors,
      DFP.FirstLeg.gradientFactors, RealSymmetric2.high, RealSymmetric2.low,
      RealSymmetric2.gap, hdenom]
    simpa only [Prod.fst, Prod.snd] using hbase
  have hrelativeChart : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
        DFP.SecondLeg.frame x.1 x.2.1 x.2.2) 0 0 := by
    have hbase : (DFP.FirstLeg.frame 0 2 1 * DFP.SecondLeg.frame 0 2 1) 0 0 = 1 := by
      have hdenom : RealSymmetric2.lowDenom 0 0 1 = 1 := by
        norm_num [RealSymmetric2.lowDenom, RealSymmetric2.low,
          RealSymmetric2.gap]
      norm_num [DFP.FirstLeg.frame, DFP.SecondLeg.frame,
      DFP.FirstLeg.outputMetric, DFP.SecondLeg.outputMetric,
      DFP.FirstLeg.spectralFactors, DFP.FirstLeg.gradientFactors,
      RealSymmetric2.lowVector, RealSymmetric2.lowRaw, RealSymmetric2.lowDenom,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
      EuclideanPlane.frame, EuclideanPlane.perp_apply, Matrix.mul_apply,
      Fin.sum_univ_two]
    apply continuousAt_const.eventually_lt
      (DFP.TwoLeg.relativeFrameEntry_continuousAt 0 0)
    simpa only [hbase] using (show (0 : ℝ) < 1 by norm_num)
  have hlocal : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
            DFP.SecondLeg.frame x.1 x.2.1 x.2.2 ∈
          Matrix.specialOrthogonalGroup (Fin 2) ℝ ∧
        DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
            DFP.SecondLeg.frame x.1 x.2.1 x.2.2 ∈
          EuclideanPlane.SignedAngle.chart := by
    filter_upwards [hfirstLowChart, hsecondLowChart, hrelativeChart] with
      x hfirst hsecond hchart
    have hfirstFrame : DFP.FirstLeg.frame x.1 x.2.1 x.2.2 ∈
        Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
      simpa only [DFP.FirstLeg.frame] using
        RealSymmetric2.frame_mem_specialOrthogonalGroup
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
          (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1) hfirst
    have hsecondFrame : DFP.SecondLeg.frame x.1 x.2.1 x.2.2 ∈
        Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
      simpa only [DFP.SecondLeg.frame] using
        RealSymmetric2.frame_mem_specialOrthogonalGroup
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
          (DFP.SecondLeg.outputMetric x.1 x.2.1 x.2.2 1 1) hsecond
    exact ⟨mul_mem hfirstFrame hsecondFrame,
      (EuclideanPlane.SignedAngle.mem_chart _).2 hchart⟩
  have hslow : ∀ᶠ ε in 𝓝 (0 : ℝ),
      DFP.FirstLeg.frame ε (p ε) (h ε) * DFP.SecondLeg.frame ε (p ε) (h ε) ∈
          Matrix.specialOrthogonalGroup (Fin 2) ℝ ∧
        DFP.FirstLeg.frame ε (p ε) (h ε) * DFP.SecondLeg.frame ε (p ε) (h ε) ∈
          EuclideanPlane.SignedAngle.chart :=
    hstate.eventually hlocal
  obtain ⟨r, hr, hrule⟩ := Metric.eventually_nhds_iff.mp hslow
  obtain ⟨η₀, hη₀, hforward⟩ := DFP.TwoLeg.slowCurveForwardOrbitOnGraph
    p h h_invariant h_pJet h_hJet
  let εmax := min εbar (min η₀ (r / 2))
  have hεmax_pos : 0 < εmax := by
    dsimp only [εmax]
    exact lt_min h_εbar.1 (lt_min hη₀.1 (half_pos hr))
  have hεmax_bar : εmax ≤ εbar := by
    exact min_le_left _ _
  refine ⟨εmax, ⟨hεmax_pos, hεmax_bar⟩, ?_⟩
  intro ε₀ hε₀ j
  have hεmax_η₀ : εmax ≤ η₀ := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀η₀ : ε₀ ∈ Set.Ioc 0 η₀ :=
    ⟨hε₀.1, le_trans hε₀.2 hεmax_η₀⟩
  let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
  have hxj : xj = (xj.1, p xj.1, h xj.1) ∧ xj.1 ∈ Set.Ioc 0 ε₀ := by
    simpa only [xj] using hforward ε₀ hε₀η₀ j
  have hεmax_r : εmax ≤ r / 2 := by
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hxj_dist : dist xj.1 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hxj.2.1]
    calc
      xj.1 ≤ ε₀ := hxj.2.2
      _ ≤ εmax := hε₀.2
      _ ≤ r / 2 := hεmax_r
      _ < r := half_lt_self hr
  have hconditions := hrule hxj_dist
  have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hcoord_eq : (orbit.state j).coordinates = xj := by
    simpa only [orbit, xj] using hcoordinates
  have hstate_coords :
      ((orbit.state j).ε, (orbit.state j).p, (orbit.state j).h) = xj := by
    simpa only [State.coordinates_def] using hcoord_eq
  have hε : (orbit.state j).ε = xj.1 := congrArg Prod.fst hstate_coords
  have hp : (orbit.state j).p = xj.2.1 :=
    congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.1) hstate_coords
  have hh : (orbit.state j).h = xj.2.2 :=
    congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.2) hstate_coords
  have hxp : p xj.1 = xj.2.1 :=
    (congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.1) hxj.1).symm
  have hxh : h xj.1 = xj.2.2 :=
    (congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.2) hxj.1).symm
  change (orbit.state j).relativeFrame ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ ∧
    (orbit.state j).relativeFrame ∈ EuclideanPlane.SignedAngle.chart
  rw [State.relativeFrame, hε, hp, hh]
  rw [hxp, hxh] at hconditions
  exact hconditions

/-- Along a sufficiently small exact invariant slow-curve orbit, the accumulated frame
angle rotates the initial physical low vector to every cycle-boundary low vector. -/
theorem slowCurveFrameAngleRepresentsLowVector (p h : ℝ → ℝ)
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
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      (orbit.state j).lowVector =
        EuclideanPlane.rotation (orbit.frameAngle j) (orbit.state 0).lowVector := by
  obtain ⟨εmax, hεmax, hconditions⟩ := slowCurveRelativeFrameConditions
    p h h_invariant h_pJet h_hJet εbar h_εbar
  refine ⟨εmax, hεmax, ?_⟩
  intro ε₀ hε₀ j
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hinitial : (orbit.state 0).frame = 1 := by
    rw [show orbit = DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀ by rfl]
    rw [DFP.TwoPhaseOrbit.ofSlowCurve_zero]
    simp [State.initial]
  have hspecial : ∀ k : ℕ,
      (orbit.state k).relativeFrame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    intro k
    simpa only [orbit] using (hconditions ε₀ hε₀ k).1
  have hchart : ∀ k : ℕ,
      (orbit.state k).relativeFrame ∈ EuclideanPlane.SignedAngle.chart := by
    intro k
    simpa only [orbit] using (hconditions ε₀ hε₀ k).2
  exact frameAngleRepresentsLowVector orbit hinitial hspecial hchart j

/-- Each recursive frame-angle difference is the frame-angle field of the complete
observable map at the current normalized state. -/
theorem frameAngleIncrement_eq_observable (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.frameAngle (j + 1) - orbit.frameAngle j =
      (DFP.TwoLeg.observableMap (orbit.state j).coordinates).frameAngleIncrement := by
  rw [frameAngle_succ]
  ring_nf
  rw [State.angleIncrement, State.relativeFrame, State.coordinates_def]
  rw [DFP.TwoLeg.observableMap_frameAngleIncrement]

/-- Along a sufficiently small exact invariant slow-curve orbit, every recursive
frame-angle difference is the unique small angle representing the relative frame. -/
theorem slowCurveFrameAngleIncrementUnique (p h : ℝ → ℝ)
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
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      let δ := orbit.frameAngle (j + 1) - orbit.frameAngle j
      δ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
        ∀ θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
          EuclideanPlane.rotationMatrix θ = (orbit.state j).relativeFrame ↔ θ = δ := by
  obtain ⟨εmax, hεmax, hconditions⟩ := slowCurveRelativeFrameConditions
    p h h_invariant h_pJet h_hJet εbar h_εbar
  refine ⟨εmax, hεmax, ?_⟩
  intro ε₀ hε₀ j
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hrelative := hconditions ε₀ hε₀ j
  have hδ : orbit.frameAngle (j + 1) - orbit.frameAngle j =
      (orbit.state j).angleIncrement := by
    rw [frameAngle_succ]
    ring_nf
  have hinterval : orbit.frameAngle (j + 1) - orbit.frameAngle j ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [hδ]
    exact State.angleIncrement_mem_interval (orbit.state j)
  refine ⟨hinterval, ?_⟩
  intro θ hθ
  rw [hδ]
  exact State.angleIncrement_unique (orbit.state j) hrelative.1 hrelative.2 θ hθ

end DFP.TwoPhaseOrbit
