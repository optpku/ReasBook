module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_10_Cycle_boundary_polar_expansion
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_24_Leading_within_cycle_endpoint_gradient_angle_increments
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_21_Frame_rotation_on_the_slow_curve
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_4_8c0_Quotient_valued_physical_endpoint_polar_angles
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngleLift.FrameAngle
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PolarGradientAngleError
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleGap
public import ReasLib.LinearAlgebra.Matrix.OrthogonalTransport
import all ReasLib.Geometry.Euclidean.Plane.Rotation

public section

noncomputable section

open Filter
open scoped Asymptotics EuclideanSpace Matrix Topology

/- The radial estimate is transported through a unit direction before the orbit
  geometry is used.  This keeps the main theorem independent of the particular
  polar-angle implementation. -/
/-- Scalar little-o remainders remain little-o after multiplication by an
eventually unit vector-valued direction. -/
lemma polarVectorRemainderOfRadialRemainder
    {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter ι} {r a q : ι → ℝ} {u : ι → V}
    (hu : ∀ᶠ i in l, ‖u i‖ = 1)
    (h : (fun i ↦ r i - a i) =o[l] q) :
    (fun i ↦ (r i - a i) • u i) =o[l] q := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hu, h.bound hc] with i hi hri
  simpa [norm_smul, hi] using hri

/- The boundary expansion uses the model vector with second coordinate
  `2 * ε²`; this identity exposes its deviation from the low frame direction. -/
/-- The quadratic boundary model differs from the low frame vector by its
second transported frame column. -/
lemma boundaryModel_sub_lowVector (s : DFP.TwoPhaseOrbit.State) :
    WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 2 * s.ε ^ 2]) - s.lowVector =
      (2 * s.ε ^ 2) • WithLp.toLp 2
        (s.frame *ᵥ ![(0 : ℝ), 1]) := by
  have hlow : WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 0]) = s.lowVector := by
    ext i
    rw [DFP.TwoPhaseOrbit.State.lowVector_apply]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [← hlow]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    ring
  · simp [Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
    ring

/- Orthogonality supplies the unit norm needed by the angle perturbation
  estimate, both for the low column and for the transported second column. -/
/-- The first and second columns of a special-orthogonal frame have unit norm. -/
lemma boundaryFrameColumnNorms (s : DFP.TwoPhaseOrbit.State)
    (hs : s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    ‖s.lowVector‖ = 1 ∧
      ‖WithLp.toLp 2 (s.frame *ᵥ ![(0 : ℝ), 1])‖ = 1 := by
  have hlow : WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 0]) = s.lowVector := by
    ext i
    rw [DFP.TwoPhaseOrbit.State.lowVector_apply]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · rw [← hlow]
    rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup s.frame hs]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  · rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup s.frame hs]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

/- A zero endpoint would force the corresponding gradient to be smaller than the
  uniform positive gradient lower bound once the center tail is cubic. -/
/-- Uniform gradient and center-tail bounds exclude endpoint coincidence with a
limiting center on sufficiently small slow-curve orbits. -/
lemma endpointSubCenterNonzero
    (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ k : ℕ, orbit.endpoint k - Clim ≠ 0 := by
  obtain ⟨εbarGradient, hεbarGradient, gmin, hgmin, gmax, hgminmax,
      hGradient⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointGradientNormUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨εbarCenter, hεbarCenter, Kcenter, hKcenter, hCenter⟩ :=
    DFP.TwoPhaseOrbit.slowCurveCenterTailUniformBound
      p h h_invariant h_pJet h_hJet
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  have hden : 0 < 2 * (Kcenter + 1) := by positivity
  have hfrac : 0 < gmin / (2 * (Kcenter + 1)) := div_pos hgmin hden
  let δ : ℝ := min (1 / 4) (gmin / (2 * (Kcenter + 1)))
  let εbar : ℝ := min εbarGradient (min εbarCenter (min εbarGraph δ))
  have hδpos : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by norm_num) hfrac
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hεbarGradient.1 (lt_min hεbarCenter.1 (lt_min hεbarGraph.1 hδpos))
  have hεbarLt : εbar < 1 / 4 :=
    (min_le_left _ _).trans_lt hεbarGradient.2
  have hKeps_lt (ε₀ : ℝ) (hε₀ : ε₀ ∈ Set.Ioc 0 εbar) :
      Kcenter * ε₀ ^ 3 < gmin := by
    have hεδ : ε₀ ≤ δ := hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have hεnonneg : 0 ≤ ε₀ := hε₀.1.le
    have hεone : ε₀ ≤ 1 := by
      have hδle : δ ≤ 1 / 4 := by
        dsimp only [δ]
        exact min_le_left _ _
      linarith
    have hpow : ε₀ ^ 3 ≤ ε₀ := pow_le_of_le_one hεnonneg hεone (by norm_num)
    have hεfrac : ε₀ ≤ gmin / (2 * (Kcenter + 1)) := hεδ.trans (by
      dsimp only [δ]
      exact min_le_right _ _)
    have hmul : Kcenter * ε₀ ≤
        Kcenter * (gmin / (2 * (Kcenter + 1))) :=
      mul_le_mul_of_nonneg_left hεfrac hKcenter.le
    have hfracLt : Kcenter * (gmin / (2 * (Kcenter + 1))) < gmin := by
      rw [show Kcenter * (gmin / (2 * (Kcenter + 1))) =
        (Kcenter * gmin) / (2 * (Kcenter + 1)) by ring]
      apply (div_lt_iff₀ hden).2
      nlinarith
    exact (mul_le_mul_of_nonneg_left hpow hKcenter.le).trans_lt
      (hmul.trans_lt hfracLt)
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Gradient : ε₀ ∈ Set.Ioc 0 εbarGradient :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Center : ε₀ ∈ Set.Ioc 0 εbarCenter :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 εbarGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  intro Clim hClim k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · intro hzero
    have hzero' : orbit.endpoint (2 * j) - Clim = 0 := by
      simpa only [orbit] using hzero
    have hgradientMem : ‖orbit.endpointGradient (2 * j)‖ ∈ Set.Icc gmin gmax := by
      simpa only [orbit] using hGradient ε₀ hε₀Gradient (2 * j)
    have htail : ‖(orbit.state j).center - Clim‖ +
        ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hCenter ε₀ hε₀Center Clim hClim j
    have hcenter : ‖(orbit.state j).center - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans htail
    have hdecomp : (orbit.state j).gradient =
        (orbit.endpoint (2 * j) - Clim) - ((orbit.state j).center - Clim) := by
      rw [DFP.TwoPhaseOrbit.endpoint_even, DFP.TwoPhaseOrbit.State.center_def]
      abel
    have hgradientBound : ‖(orbit.state j).gradient‖ ≤
        ‖orbit.endpoint (2 * j) - Clim‖ + ‖(orbit.state j).center - Clim‖ := by
      rw [hdecomp]
      exact norm_sub_le _ _
    have hgradientSmall : ‖(orbit.state j).gradient‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      calc
        ‖(orbit.state j).gradient‖ ≤
            ‖orbit.endpoint (2 * j) - Clim‖ + ‖(orbit.state j).center - Clim‖ :=
          hgradientBound
        _ = ‖(orbit.state j).center - Clim‖ := by simp [hzero']
        _ ≤ Kcenter * (orbit.state j).ε ^ 3 := hcenter
    have hgradientLower : gmin ≤ ‖(orbit.state j).gradient‖ := by
      simpa only [DFP.TwoPhaseOrbit.endpointGradient_even] using hgradientMem.1
    exact (not_lt_of_ge hgradientLower)
      ((hgradientSmall.trans (by
        have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
        have hcoord' : (orbit.state j).coordinates =
            DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
          simpa only [orbit] using hcoord
        have hεeq : (orbit.state j).ε =
            (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
          simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hcoord'
        have hforward := hGraph ε₀ hε₀Graph j
        have hforward' : (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 ∈
            Set.Ioc 0 ε₀ := by simpa only using hforward.2
        have hεstate : (orbit.state j).ε ≤ ε₀ := by
          rw [hεeq]
          exact hforward'.2
        have hεstatePos : 0 ≤ (orbit.state j).ε := by
          rw [hεeq]
          exact hforward'.1.le
        have hpowState : (orbit.state j).ε ^ 3 ≤ ε₀ ^ 3 :=
          pow_le_pow_left₀ hεstatePos hεstate 3
        exact mul_le_mul_of_nonneg_left hpowState hKcenter.le)).trans_lt
        (hKeps_lt ε₀ hε₀))
  · intro hzero
    have hzero' : orbit.endpoint (2 * j + 1) - Clim = 0 := by
      simpa only [orbit] using hzero
    have hgradientMem : ‖orbit.endpointGradient (2 * j + 1)‖ ∈ Set.Icc gmin gmax := by
      simpa only [orbit] using hGradient ε₀ hε₀Gradient (2 * j + 1)
    have htail : ‖(orbit.state j).center - Clim‖ +
        ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      simpa only [orbit] using hCenter ε₀ hε₀Center Clim hClim j
    have hmiddle : ‖(orbit.state j).middleCenter - Clim‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans htail
    have hdecomp : (orbit.state j).middleGradient =
        (orbit.endpoint (2 * j + 1) - Clim) -
          ((orbit.state j).middleCenter - Clim) := by
      rw [DFP.TwoPhaseOrbit.endpoint_odd, DFP.TwoPhaseOrbit.State.middleCenter_def]
      abel
    have hgradientBound : ‖(orbit.state j).middleGradient‖ ≤
        ‖orbit.endpoint (2 * j + 1) - Clim‖ +
          ‖(orbit.state j).middleCenter - Clim‖ := by
      rw [hdecomp]
      exact norm_sub_le _ _
    have hgradientSmall : ‖(orbit.state j).middleGradient‖ ≤
        Kcenter * (orbit.state j).ε ^ 3 := by
      calc
        ‖(orbit.state j).middleGradient‖ ≤
            ‖orbit.endpoint (2 * j + 1) - Clim‖ +
              ‖(orbit.state j).middleCenter - Clim‖ := hgradientBound
        _ = ‖(orbit.state j).middleCenter - Clim‖ := by simp [hzero']
        _ ≤ Kcenter * (orbit.state j).ε ^ 3 := hmiddle
    have hgradientLower : gmin ≤ ‖(orbit.state j).middleGradient‖ := by
      simpa only [DFP.TwoPhaseOrbit.endpointGradient_odd] using hgradientMem.1
    exact (not_lt_of_ge hgradientLower)
      ((hgradientSmall.trans (by
        have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
        have hcoord' : (orbit.state j).coordinates =
            DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
          simpa only [orbit] using hcoord
        have hεeq : (orbit.state j).ε =
            (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
          simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hcoord'
        have hforward := hGraph ε₀ hε₀Graph j
        have hforward' : (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 ∈
            Set.Ioc 0 ε₀ := by simpa only using hforward.2
        have hεstate : (orbit.state j).ε ≤ ε₀ := by
          rw [hεeq]
          exact hforward'.2
        have hεstatePos : 0 ≤ (orbit.state j).ε := by
          rw [hεeq]
          exact hforward'.1.le
        have hpowState : (orbit.state j).ε ^ 3 ≤ ε₀ ^ 3 :=
          pow_le_pow_left₀ hεstatePos hεstate 3
        exact mul_le_mul_of_nonneg_left hpowState hKcenter.le)).trans_lt
        (hKeps_lt ε₀ hε₀))
/- The canonical lift theorem consumes a quotient-valued frame bridge.  These
  adapters isolate endpoint and initial-angle normalizations from the asymptotic
  argument. -/
/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): the initial
slow-curve low vector is the first standard basis vector. -/
lemma slowCurveInitialLowVector (p h : ℝ → ℝ) (ε₀ : ℝ) :
    ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state 0).lowVector =
      EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
  rw [DFP.TwoPhaseOrbit.ofSlowCurve_zero]
  ext i
  rw [DFP.TwoPhaseOrbit.State.lowVector_apply,
    DFP.TwoPhaseOrbit.State.initial_frame]
  fin_cases i <;> simp [EuclideanSpace.basisFun_apply, Matrix.one_apply]

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): the initial
lift/frame difference is the physical initial correction angle. -/
lemma endpointPolarLiftFrameBase
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hinitial : (orbit.state 0).lowVector =
      EuclideanSpace.basisFun (Fin 2) ℝ 0) :
    orbit.endpointPolarAngleLift C 0 - orbit.frameAngle 0 =
      (EuclideanPlane.orientation.oangle (orbit.state 0).lowVector
        (orbit.endpoint 0 - C)).toReal := by
  rw [DFP.TwoPhaseOrbit.endpointPolarAngleLift_zero,
    DFP.TwoPhaseOrbit.frameAngle_zero, sub_zero,
    DFP.TwoPhaseOrbit.endpointPolarAngle_def, hinitial]

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): an even
lift/frame quotient equals the oriented angle from the low vector to the endpoint. -/
lemma endpointPolarLiftFrameQuotientAt
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ)
    (hlow : (orbit.state j).lowVector ≠ 0)
    (hangle : EuclideanPlane.orientation.oangle
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) (orbit.state j).lowVector =
        (orbit.frameAngle j : Real.Angle))
    (hradial : orbit.endpoint (2 * j) - C ≠ 0) :
    ((orbit.endpointPolarAngleLift C (2 * j) - orbit.frameAngle j : ℝ) :
        Real.Angle) =
      EuclideanPlane.orientation.oangle (orbit.state j).lowVector
        (orbit.endpoint (2 * j) - C) := by
  have hbasis : (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≠ 0 := by
    intro hzero
    have hcoordinate := congrArg
      (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hzero
    simp [EuclideanSpace.basisFun_apply] at hcoordinate
  change (orbit.endpointPolarAngleLift C (2 * j) : Real.Angle) -
    (orbit.frameAngle j : Real.Angle) = _
  rw [DFP.TwoPhaseOrbit.endpointPolarAngleLift_coe,
    DFP.TwoPhaseOrbit.endpointPolarAngle_def, ← hangle]
  exact EuclideanPlane.orientation.oangle_sub_left hbasis hlow hradial

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): the initial
and all even endpoint quotient identities form one reusable lift interface. -/
lemma endpointPolarLiftFrameQuotient
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2))
    (hinitial : (orbit.state 0).lowVector =
      EuclideanSpace.basisFun (Fin 2) ℝ 0)
    (hlow : ∀ j : ℕ, (orbit.state j).lowVector ≠ 0)
    (hangle : ∀ j : ℕ, EuclideanPlane.orientation.oangle
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) (orbit.state j).lowVector =
        (orbit.frameAngle j : Real.Angle))
    (hradial : ∀ k : ℕ, orbit.endpoint k - C ≠ 0) :
    (orbit.endpointPolarAngleLift C 0 - orbit.frameAngle 0 =
        (EuclideanPlane.orientation.oangle (orbit.state 0).lowVector
          (orbit.endpoint 0 - C)).toReal) ∧
      (∀ j : ℕ,
        ((orbit.endpointPolarAngleLift C (2 * j) - orbit.frameAngle j : ℝ) :
            Real.Angle) =
          EuclideanPlane.orientation.oangle (orbit.state j).lowVector
            (orbit.endpoint (2 * j) - C)) := by
  refine ⟨endpointPolarLiftFrameBase orbit C hinitial, ?_⟩
  intro j
  exact endpointPolarLiftFrameQuotientAt orbit C j (hlow j) (hangle j)
    (hradial (2 * j))

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): the angle
from a valid state's low vector to its gradient is its normalized coordinate angle. -/
lemma lowVectorGradientAngle_toReal (s : DFP.TwoPhaseOrbit.State)
    (hs : DFP.TwoPhaseOrbit.State.PhaseValidity s) :
    (EuclideanPlane.orientation.oangle s.lowVector s.gradient).toReal =
      (EuclideanPlane.orientation.oangle
        (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2))
        (!₂[(1 : ℝ), s.p * s.ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal := by
  -- Express both vectors in the same special-orthogonal frame.
  have hlow : s.lowVector =
      WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 0]) := by
    ext i
    rw [DFP.TwoPhaseOrbit.State.lowVector_apply]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hlow, DFP.TwoPhaseOrbit.State.gradient_def]
  rw [EuclideanPlane.orientation.oangle_smul_right_of_pos _ _ hs.amplitude_pos]
  rw [EuclideanPlane.oangle_specialOrthogonal_mulVec s.frame
    hs.frame_specialOrthogonal 1 0 1 (s.p * s.ε ^ 2)]

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): two
successive small oriented angles compose without leaving the principal branch. -/
lemma oangleToReal_add_small
    (u v w : EuclideanSpace ℝ (Fin 2))
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (ha : |(EuclideanPlane.orientation.oangle u v).toReal| < Real.pi / 16)
    (hb : |(EuclideanPlane.orientation.oangle v w).toReal| < Real.pi / 16) :
    |(EuclideanPlane.orientation.oangle u w).toReal| < Real.pi / 8 := by
  -- Add the two representatives and keep their sum in the principal interval.
  let a := (EuclideanPlane.orientation.oangle u v).toReal
  let b := (EuclideanPlane.orientation.oangle v w).toReal
  have habs : |a + b| < Real.pi / 8 := by
    calc
      |a + b| ≤ |a| + |b| := abs_add_le _ _
      _ < Real.pi / 8 := by linarith [Real.pi_pos]
  have hcoeA : (a : Real.Angle) =
      EuclideanPlane.orientation.oangle u v := Real.Angle.coe_toReal _
  have hcoeB : (b : Real.Angle) =
      EuclideanPlane.orientation.oangle v w := Real.Angle.coe_toReal _
  have hcoe : ((a + b : ℝ) : Real.Angle) =
      EuclideanPlane.orientation.oangle u w := by
    change (a : Real.Angle) + (b : Real.Angle) = _
    rw [hcoeA, hcoeB]
    exact EuclideanPlane.orientation.oangle_add hu hv hw
  have hprincipal : a + b ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hpi : |a + b| < Real.pi := by
      linarith [habs, Real.pi_pos]
    have hbounds := abs_lt.mp hpi
    exact ⟨hbounds.1, hbounds.2.le⟩
  have hreal := congrArg Real.Angle.toReal hcoe
  have hprincipalReal : (((a + b : ℝ) : Real.Angle).toReal) = a + b :=
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hprincipal
  rw [hprincipalReal] at hreal
  rw [← hreal]
  exact habs

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): the
normalized slow-curve gradient angle tends to zero with the scale. -/
lemma slowCurveNormalizedGradientAngleTendsto (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    Tendsto (fun ε : ℝ ↦
      (EuclideanPlane.orientation.oangle
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (!₂[(1 : ℝ), p ε * ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal)
      (𝓝 0) (𝓝 0) := by
  -- Reduce the coordinate angle to `arctan (p ε * ε²)`.
  have hpath := DFP.TwoPhaseOrbit.slowGraphPath_tendsto p h h_pJet h_hJet
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    have hprojection : ContinuousAt
        (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) := by
      fun_prop
    have ht := hprojection.tendsto.comp hpath
    simpa only [Function.comp_def] using ht
  have hsquare : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by
      fun_prop
    simpa using hcontinuous.tendsto
  have hproduct : Tendsto (fun ε : ℝ ↦ p ε * ε ^ 2) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using hpTendsto.mul hsquare
  have harctan : Tendsto (fun ε : ℝ ↦ Real.arctan (p ε * ε ^ 2))
      (𝓝 0) (𝓝 0) := by
    have ht := Real.continuousAt_arctan.tendsto.comp hproduct
    simpa only [Function.comp_def, Real.arctan_zero] using ht
  refine harctan.congr' ?_
  filter_upwards [] with ε
  have hformula := EuclideanPlane.oangle_toReal_eq_arctan_sub_of_pos
    1 0 1 (p ε * ε ^ 2) zero_lt_one zero_lt_one
  have hbasis : EuclideanSpace.basisFun (Fin 2) ℝ 0 =
      (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · simp [EuclideanSpace.basisFun_apply]
    · simp [EuclideanSpace.basisFun_apply]
  rw [hbasis]
  simpa using hformula.symm

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): a slow-graph
iterate gives the scale bound and shape coordinate of the corresponding orbit state. -/
lemma ofSlowCurveScaleAndShape (p h : ℝ → ℝ) (ε₀ : ℝ) (j : ℕ)
    (hx : let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
      xj = (xj.1, p xj.1, h xj.1) ∧ xj.1 ∈ Set.Ioc 0 ε₀) :
    let s := (DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j
    s.ε ∈ Set.Ioc 0 ε₀ ∧ s.p = p s.ε := by
  -- Project the orbit coordinate identity only once at each coordinate.
  dsimp only
  let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
  have hcoordinates :
      ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).coordinates = xj := by
    simpa only [xj] using
      DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  have hε : ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).ε = xj.1 := by
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hcoordinates
  have hp : ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).p = xj.2.1 := by
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.1) hcoordinates
  have hx' : xj = (xj.1, p xj.1, h xj.1) ∧ xj.1 ∈ Set.Ioc 0 ε₀ := by
    simpa only [xj] using hx
  refine ⟨hε.symm ▸ hx'.2, ?_⟩
  calc
    _ = xj.2.1 := hp
    _ = p xj.1 := congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.1) hx'.1
    _ = p ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).ε :=
      congrArg p hε.symm

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): a valid
state on the slow graph inherits the normalized coordinate-angle bound. -/
lemma lowVectorGradientAngleSmallOfShape (p : ℝ → ℝ)
    (s : DFP.TwoPhaseOrbit.State)
    (hs : DFP.TwoPhaseOrbit.State.PhaseValidity s)
    (hp : s.p = p s.ε)
    (hsmall : |(EuclideanPlane.orientation.oangle
      (EuclideanSpace.basisFun (Fin 2) ℝ 0)
      (!₂[(1 : ℝ), p s.ε * s.ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal| <
        Real.pi / 16) :
    |(EuclideanPlane.orientation.oangle s.lowVector s.gradient).toReal| <
      Real.pi / 16 := by
  -- Rewrite the physical angle into the slow-graph coordinate chart.
  rw [lowVectorGradientAngle_toReal s hs, hp]
  have hbasis : (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) =
      EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i
    · simp [EuclideanSpace.basisFun_apply]
    · simp [EuclideanSpace.basisFun_apply]
  rwa [hbasis]

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): on a
small slow-curve orbit, every low-vector-to-gradient angle lies in a fixed
principal subinterval. -/
lemma slowCurveLowGradientAngleSmall (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ η ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ ε₀ ∈ Set.Ioc 0 η,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j : ℕ,
          (orbit.state j).ε ∈ Set.Ioc 0 ε₀ ∧
            (orbit.state j).lowVector ≠ 0 ∧
            |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
              (orbit.state j).gradient).toReal| < Real.pi / 16 := by
  -- Restrict the coordinate-angle convergence to a small metric ball.
  have hangle := slowCurveNormalizedGradientAngleTendsto p h h_pJet h_hJet
  have hball : Metric.ball (0 : ℝ) (Real.pi / 16) ∈ 𝓝 0 :=
    Metric.ball_mem_nhds 0 (by positivity)
  have hsmallEventually : ∀ᶠ ε in 𝓝 (0 : ℝ),
      |(EuclideanPlane.orientation.oangle
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (!₂[(1 : ℝ), p ε * ε ^ 2] : EuclideanSpace ℝ (Fin 2))).toReal| <
          Real.pi / 16 := by
    filter_upwards [hangle.eventually hball] with ε hε
    simpa only [Real.dist_eq, sub_zero] using hε
  obtain ⟨r, hr, hrule⟩ := Metric.eventually_nhds_iff.mp hsmallEventually
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
      p h h_invariant h_pJet h_hJet ηGraph hηGraph
  let η := min ηGraph (min ηValid (r / 2))
  have hη : η ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · dsimp only [η]
      exact lt_min hηGraph.1 (lt_min hηValid.1 (half_pos hr))
    · exact (min_le_left _ _).trans_lt hηGraph.2
  refine ⟨η, hη, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεRadius : ε₀ ≤ r / 2 :=
    hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    have hx := hGraph ε₀ hεGraph j
    simpa only [orbit] using (ofSlowCurveScaleAndShape p h ε₀ j hx).1
  intro j
  -- Transport the coordinate chart bound through the current physical frame.
  have hvalidj : DFP.TwoPhaseOrbit.State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hεValid j
  have hpstate : (orbit.state j).p = p (orbit.state j).ε := by
    have hx := hGraph ε₀ hεGraph j
    simpa only [orbit] using (ofSlowCurveScaleAndShape p h ε₀ j hx).2
  refine ⟨hscale j, ?_, ?_⟩
  · have hnorm := (boundaryFrameColumnNorms (orbit.state j)
      hvalidj.frame_specialOrthogonal).1
    intro hz
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  · apply lowVectorGradientAngleSmallOfShape p (orbit.state j) hvalidj hpstate
    apply hrule
    rw [Real.dist_eq, sub_zero, abs_of_pos (hscale j).1]
    exact ((hscale j).2.trans hεRadius).trans_lt (half_lt_self hr)

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): a small
low-to-gradient angle and a small lifted gradient-to-endpoint correction give
a small physical low-to-endpoint angle. -/
lemma evenPhysicalCorrectionSmallOfLiftDifference
    (orbit : DFP.TwoPhaseOrbit) (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ)
    (hlow : (orbit.state j).lowVector ≠ 0)
    (hgradient : orbit.endpointGradient (2 * j) ≠ 0)
    (hradial : orbit.endpoint (2 * j) - C ≠ 0)
    (hlowGradient :
      |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
        (orbit.state j).gradient).toReal| < Real.pi / 16)
    (hliftGradient :
      |orbit.endpointPolarAngleLift C (2 * j) -
        orbit.endpointGradientAngleLift (2 * j)| < Real.pi / 16) :
    |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
      (orbit.endpoint (2 * j) - C)).toReal| < Real.pi / 8 := by
  -- Identify the small lifted difference with its principal physical angle.
  let d := orbit.endpointPolarAngleLift C (2 * j) -
    orbit.endpointGradientAngleLift (2 * j)
  have hdMem : d ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hbounds := abs_lt.mp hliftGradient
    constructor <;> linarith [Real.pi_pos, hbounds.1, hbounds.2]
  have hprincipal : (((d : ℝ) : Real.Angle).toReal) = d :=
    Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hdMem
  have hcoe := DFP.TwoPhaseOrbit.polarGradientLiftDifference_coe
    orbit C (2 * j) hgradient hradial
  have hreal := congrArg Real.Angle.toReal hcoe
  have hphysical :
      |(EuclideanPlane.orientation.oangle (orbit.state j).gradient
        (orbit.endpoint (2 * j) - C)).toReal| < Real.pi / 16 := by
    rw [DFP.TwoPhaseOrbit.endpointGradient_even] at hreal
    rw [hprincipal] at hreal
    rw [← hreal]
    exact hliftGradient
  have hgradientState : (orbit.state j).gradient ≠ 0 := by
    simpa only [DFP.TwoPhaseOrbit.endpointGradient_even] using hgradient
  exact oangleToReal_add_small (orbit.state j).lowVector
    (orbit.state j).gradient (orbit.endpoint (2 * j) - C)
    hlow hgradientState hradial hlowGradient hphysical

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): boundary
expansion controls the even physical endpoint correction by a quadratic scale. -/
lemma slowCurveEvenPolarPhysicalCorrectionBound (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ η ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Set.Ioc 0 η,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ᶠ j : ℕ in atTop,
              |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
                  (orbit.endpoint (2 * j) - Clim)).toReal| ≤
                K * (orbit.state j).ε ^ 2 := by
-- The boundary remainder is first converted to an eventual norm estimate;
-- uniform radius bounds then turn that perturbation into the angle estimate.
  obtain ⟨ηBoundary, hηBoundary, hBoundary⟩ :=
    DFP.TwoPhaseOrbit.slowCurveBoundaryPolarExpansion
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hAmpUniform⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
      p h h_invariant h_pJet h_hJet ηGraph hηGraph
  let η := min ηBoundary (min ηAmp (min ηGraph ηValid))
  have hη : η ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · dsimp only [η]
      exact lt_min hηBoundary.1 (lt_min hηAmp.1 (lt_min hηGraph.1 hηValid.1))
    · exact (min_le_left _ _).trans_lt hηBoundary.2
  let Kangle : ℝ := Real.pi * (6 * Gmax / Gmin)
  have hKangle : 0 < Kangle := by
    dsimp only [Kangle]
    have hGmax : 0 < Gmax := hGmin.trans_le hGminMax
    exact mul_pos Real.pi_pos (div_pos (by nlinarith) hGmin)
  refine ⟨η, hη, Kangle, hKangle, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεBoundary : ε₀ ∈ Set.Ioc 0 ηBoundary :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεAmp : ε₀ ∈ Set.Ioc 0 ηAmp :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨_, _, _, hAmpBoundsRaw⟩ := hAmpUniform ε₀ hεAmp
  have hAmpBounds (j : ℕ) :
      (orbit.state j).amplitude ∈ Set.Icc Gmin Gmax := by
    simpa only [orbit] using hAmpBoundsRaw j
  have hvalid (j : ℕ) : DFP.TwoPhaseOrbit.State.PhaseValidity (orbit.state j) := by
    simpa only [orbit] using hValid ε₀ hεValid j
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    have hx := hGraph ε₀ hεGraph j
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hc
    have heq : (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
      simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hc'
    rw [heq]
    exact hx.2
  intro Clim hClim
  have hboundary := hBoundary ε₀ hεBoundary Clim hClim
  dsimp only [orbit] at hboundary
  have hGmax : 0 < Gmax := hGmin.trans_le hGminMax
  have hrem : ∀ᶠ j : ℕ in atTop,
      ‖orbit.endpoint (2 * j) - Clim -
          (orbit.state j).amplitude •
            WithLp.toLp 2 ((orbit.state j).frame *ᵥ
              ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2])‖ ≤
        (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by
    filter_upwards [hboundary.eventuallyLE] with j hj
    have hApos : 0 < (orbit.state j).amplitude :=
      lt_of_lt_of_le hGmin (hAmpBounds j).1
    have hepos : 0 < (orbit.state j).ε := (hscale j).1
    simpa only [orbit, DFP.TwoPhaseOrbit.endpoint_even, norm_mul,
      Real.norm_eq_abs, abs_of_pos hApos,
      abs_of_nonneg (sq_nonneg ((orbit.state j).ε))] using hj
  filter_upwards [hrem] with j hj
  have hA : (orbit.state j).amplitude ∈ Set.Icc Gmin Gmax := hAmpBounds j
  have hApos : 0 < (orbit.state j).amplitude := lt_of_lt_of_le hGmin hA.1
  have hepos : 0 < (orbit.state j).ε := (hscale j).1
  have hεquarter : (orbit.state j).ε < (1 / 4 : ℝ) := by
    exact lt_of_le_of_lt ((hscale j).2.trans hε₀.2) hη.2
  have hcols := boundaryFrameColumnNorms (orbit.state j)
    (hvalid j).frame_specialOrthogonal
  have hmodelSub := boundaryModel_sub_lowVector (orbit.state j)
  have hcorrection :
      ‖(orbit.state j).amplitude •
          WithLp.toLp 2 ((orbit.state j).frame *ᵥ
            ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2]) -
        (orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
      2 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by
    rw [← smul_sub, hmodelSub, norm_smul, norm_smul, hcols.2,
      Real.norm_eq_abs, abs_of_pos hApos]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring_nf
    exact le_refl _
  have hpertAmp :
      ‖orbit.endpoint (2 * j) - Clim -
          (orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
        3 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by
    have hdecomp : orbit.endpoint (2 * j) - Clim -
          (orbit.state j).amplitude • (orbit.state j).lowVector =
        (orbit.endpoint (2 * j) - Clim -
            (orbit.state j).amplitude •
              WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2])) +
          ((orbit.state j).amplitude •
              WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2]) -
            (orbit.state j).amplitude • (orbit.state j).lowVector) := by
      abel
    rw [hdecomp]
    calc
      _ ≤ ‖orbit.endpoint (2 * j) - Clim -
            (orbit.state j).amplitude •
              WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2])‖ +
          ‖(orbit.state j).amplitude •
              WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2]) -
            (orbit.state j).amplitude • (orbit.state j).lowVector‖ :=
        norm_add_le _ _
      _ ≤ (orbit.state j).amplitude * (orbit.state j).ε ^ 2 +
          2 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 :=
        add_le_add hj hcorrection
      _ = 3 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by ring
  have hbase : Gmin / 2 ≤ ‖(orbit.state j).amplitude •
      (orbit.state j).lowVector‖ := by
    rw [norm_smul, hcols.1, Real.norm_eq_abs, abs_of_pos hApos]
    nlinarith [hA.1]
  have hendpoint : Gmin / 2 ≤ ‖orbit.endpoint (2 * j) - Clim‖ := by
    have hnormA : ‖(orbit.state j).amplitude • (orbit.state j).lowVector‖ =
        (orbit.state j).amplitude := by
      rw [norm_smul, hcols.1, Real.norm_eq_abs, abs_of_pos hApos]
      ring
    have htriangle : ‖(orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
        ‖orbit.endpoint (2 * j) - Clim‖ +
          ‖orbit.endpoint (2 * j) - Clim -
            (orbit.state j).amplitude • (orbit.state j).lowVector‖ := by
      have hcancellation :
          (orbit.endpoint (2 * j) - Clim) -
              (orbit.endpoint (2 * j) - Clim -
                (orbit.state j).amplitude • (orbit.state j).lowVector) =
            (orbit.state j).amplitude • (orbit.state j).lowVector := by abel
      calc
        ‖(orbit.state j).amplitude • (orbit.state j).lowVector‖ =
            ‖(orbit.endpoint (2 * j) - Clim) -
              (orbit.endpoint (2 * j) - Clim -
                (orbit.state j).amplitude • (orbit.state j).lowVector)‖ := by
          rw [hcancellation]
        _ ≤ _ := norm_sub_le _ _
    have hsmall : 3 * (orbit.state j).amplitude *
        (orbit.state j).ε ^ 2 ≤ (orbit.state j).amplitude / 2 := by
      have hele : (orbit.state j).ε ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
        have hprod : 0 ≤ ((1 / 4 : ℝ) - (orbit.state j).ε) *
            ((1 / 4 : ℝ) + (orbit.state j).ε) := by
          exact mul_nonneg (sub_nonneg.mpr (le_of_lt hεquarter)) (by positivity)
        nlinarith
      nlinarith [hA.1, hA.2, sq_nonneg ((orbit.state j).ε)]
    linarith [hA.1, hbase, hnormA, htriangle, hsmall, hpertAmp]
  have hpert :
      ‖orbit.endpoint (2 * j) - Clim -
          (orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
        3 * Gmax * (orbit.state j).ε ^ 2 := by
    calc
      _ ≤ 3 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := hpertAmp
      _ ≤ 3 * Gmax * (orbit.state j).ε ^ 2 := by
        gcongr
        exact hA.2
  have hangle := DFP.TwoPhaseOrbit.abs_oangle_toReal_le_of_norm_perturbation
    EuclideanPlane.orientation
    ((orbit.state j).amplitude • (orbit.state j).lowVector)
    (orbit.endpoint (2 * j) - Clim) (Gmin / 2)
    (3 * Gmax * (orbit.state j).ε ^ 2) (by positivity) hbase hendpoint hpert
  rw [EuclideanPlane.orientation.oangle_smul_left_of_pos _ _ hApos] at hangle
  have hbound : |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
        (orbit.endpoint (2 * j) - Clim)).toReal| ≤
        Kangle * (orbit.state j).ε ^ 2 := by
    calc
      _ ≤ Real.pi * (3 * Gmax * (orbit.state j).ε ^ 2) / (Gmin / 2) := hangle
      _ = Kangle * (orbit.state j).ε ^ 2 := by
        dsimp only [Kangle]
        field_simp [ne_of_gt hGmin]
        ring
  exact hbound

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): below one
uniform scale, every even physical low-vector correction lies in the principal
eighth-turn interval. -/
lemma slowCurveEvenPolarPhysicalCorrectionSmall (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ η ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ ε₀ ∈ Set.Ioc 0 η,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ j : ℕ,
              |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
                (orbit.endpoint (2 * j) - Clim)).toReal| < Real.pi / 8 := by
  -- Collect the low-gradient chart, cubic lift error, gradient norm, and radial nonzero APIs.
  obtain ⟨ηLow, hηLow, hLow⟩ :=
    slowCurveLowGradientAngleSmall p h h_invariant h_pJet h_hJet
  obtain ⟨ηLift, hηLift, Klift, hKlift, hLift⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePolarGradientAngleErrorUniform
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGradient, hηGradient, gmin, hgmin, gmax, hgminmax, hGradient⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointGradientNormUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηRadial, hηRadial, hRadial⟩ :=
    endpointSubCenterNonzero p h h_invariant h_pJet h_hJet
  let ηCubic := min (1 : ℝ) (Real.pi / (32 * (Klift + 1)))
  have hηCubic : 0 < ηCubic := by
    dsimp only [ηCubic]
    exact lt_min zero_lt_one (div_pos Real.pi_pos (by positivity))
  let η := min ηLow (min ηLift (min ηGradient (min ηRadial ηCubic)))
  have hη : η ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · dsimp only [η]
      exact lt_min hηLow.1 (lt_min hηLift.1
        (lt_min hηGradient.1 (lt_min hηRadial.1 hηCubic)))
    · exact (min_le_left _ _).trans_lt hηLow.2
  refine ⟨η, hη, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεLow : ε₀ ∈ Set.Ioc 0 ηLow :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεLift : ε₀ ∈ Set.Ioc 0 ηLift :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεGradient : ε₀ ∈ Set.Ioc 0 ηGradient :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hεRadial : ε₀ ∈ Set.Ioc 0 ηRadial :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))⟩
  have hεCubic : ε₀ ≤ ηCubic :=
    hε₀.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  intro Clim hClim j
  -- The cubic lift error is smaller than a sixteenth-turn at every index.
  have hlowData := hLow ε₀ hεLow j
  have hscale : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    simpa only [orbit] using hlowData.1
  have hliftBound :
      |orbit.endpointPolarAngleLift Clim (2 * j) -
        orbit.endpointGradientAngleLift (2 * j)| ≤
          Klift * (orbit.state j).ε ^ 3 := by
    simpa only [orbit, Fin.val_zero, Nat.add_zero] using
      hLift ε₀ hεLift Clim hClim j (0 : Fin 2)
  have heOne : (orbit.state j).ε ≤ 1 :=
    hscale.2.trans (hεCubic.trans (min_le_left _ _))
  have heRatio : (orbit.state j).ε ≤ Real.pi / (32 * (Klift + 1)) :=
    hscale.2.trans (hεCubic.trans (min_le_right _ _))
  have hpow : (orbit.state j).ε ^ 3 ≤ (orbit.state j).ε :=
    pow_le_of_le_one hscale.1.le heOne (by norm_num)
  have hratioIdentity :
      Klift * (Real.pi / (32 * (Klift + 1))) =
        (Klift * Real.pi) / (32 * (Klift + 1)) := by
    ring
  have hratioSmall :
      Klift * (Real.pi / (32 * (Klift + 1))) < Real.pi / 32 := by
    rw [hratioIdentity]
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [Real.pi_pos]
  have hliftSmall :
      |orbit.endpointPolarAngleLift Clim (2 * j) -
        orbit.endpointGradientAngleLift (2 * j)| < Real.pi / 16 := by
    calc
      _ ≤ Klift * (orbit.state j).ε ^ 3 := hliftBound
      _ ≤ Klift * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_left hpow hKlift.le
      _ ≤ Klift * (Real.pi / (32 * (Klift + 1))) :=
        mul_le_mul_of_nonneg_left heRatio hKlift.le
      _ < Real.pi / 32 := hratioSmall
      _ < Real.pi / 16 := by nlinarith [Real.pi_pos]
  have hgradient : orbit.endpointGradient (2 * j) ≠ 0 := by
    have hgradientBounds := hGradient ε₀ hεGradient (2 * j)
    exact norm_pos_iff.mp (hgmin.trans_le hgradientBounds.1)
  have hradial : orbit.endpoint (2 * j) - Clim ≠ 0 := by
    simpa only [orbit] using hRadial ε₀ hεRadial Clim hClim (2 * j)
  have hlow : (orbit.state j).lowVector ≠ 0 := by
    simpa only [orbit] using hlowData.2.1
  have hlowGradient :
      |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
        (orbit.state j).gradient).toReal| < Real.pi / 16 := by
    simpa only [orbit] using hlowData.2.2
  exact evenPhysicalCorrectionSmallOfLiftDifference orbit Clim j
    hlow hgradient hradial hlowGradient hliftSmall

/-- Helper for Lemma 4.8c (Two-phase endpoint polar representation): one
threshold supplies both global principal-branch control and the eventual
quadratic physical-correction bound. -/
lemma slowCurveEvenPolarPhysicalCorrectionControl (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ η ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Set.Ioc 0 η,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            (∀ j : ℕ,
              |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
                (orbit.endpoint (2 * j) - Clim)).toReal| < Real.pi / 8) ∧
            ∀ᶠ j : ℕ in atTop,
              |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
                (orbit.endpoint (2 * j) - Clim)).toReal| ≤
                  K * (orbit.state j).ε ^ 2 := by
  -- Intersect the two independently proved uniform thresholds.
  obtain ⟨ηBound, hηBound, K, hK, hBound⟩ :=
    slowCurveEvenPolarPhysicalCorrectionBound p h h_invariant h_pJet h_hJet
  obtain ⟨ηSmall, hηSmall, hSmall⟩ :=
    slowCurveEvenPolarPhysicalCorrectionSmall p h h_invariant h_pJet h_hJet
  let η := min ηBound ηSmall
  have hη : η ∈ Set.Ioo (0 : ℝ) (1 / 4) :=
    ⟨lt_min hηBound.1 hηSmall.1, (min_le_left _ _).trans_lt hηBound.2⟩
  refine ⟨η, hη, K, hK, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεBound : ε₀ ∈ Set.Ioc 0 ηBound :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεSmall : ε₀ ∈ Set.Ioc 0 ηSmall :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  intro Clim hClim
  constructor
  · simpa only [orbit] using hSmall ε₀ hεSmall Clim hClim
  · simpa only [orbit] using hBound ε₀ hεBound Clim hClim

/- A positive antitone scale lets an eventual quadratic estimate be extended over
  the finite initial segment by enlarging its constant. -/
/-- An eventual quadratic bound on a positive antitone sequence extends to all
indices when the bounded quantity has a positive global bound. -/
lemma allIndexSquareBoundOfEventually
    {a ε : ℕ → ℝ} {K B : ℝ}
    (hK : 0 ≤ K) (hB : 0 < B)
    (hε : ∀ n, 0 < ε n) (hanti : Antitone ε)
    (hbound : ∀ n, |a n| ≤ B)
    (hevent : ∀ᶠ n : ℕ in atTop, |a n| ≤ K * ε n ^ 2) :
    ∃ K' > 0, ∀ n, |a n| ≤ K' * ε n ^ 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  have hεN : 0 < ε N := hε N
  have hεNsq : 0 < ε N ^ 2 := sq_pos_of_pos hεN
  let K' : ℝ := max K (B / ε N ^ 2)
  have hratio : 0 < B / ε N ^ 2 := div_pos hB hεNsq
  have hK' : 0 < K' := lt_of_lt_of_le hratio (le_max_right _ _)
  refine ⟨K', hK', ?_⟩
  intro n
  by_cases hn : N ≤ n
  · calc
      |a n| ≤ K * ε n ^ 2 := hN n hn
      _ ≤ K' * ε n ^ 2 := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  · have hnN : n ≤ N := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    have hεle : ε N ≤ ε n := hanti hnN
    have hsq : ε N ^ 2 ≤ ε n ^ 2 := by
      nlinarith [sq_nonneg (ε n - ε N)]
    have hratio_bound : B ≤ (B / ε N ^ 2) * ε n ^ 2 := by
      calc
        B = (B / ε N ^ 2) * ε N ^ 2 := by
          field_simp [ne_of_gt hεNsq]
        _ ≤ (B / ε N ^ 2) * ε n ^ 2 := by
          exact mul_le_mul_of_nonneg_left hsq hratio.le
    calc
      |a n| ≤ B := hbound n
      _ ≤ (B / ε N ^ 2) * ε n ^ 2 := hratio_bound
      _ ≤ K' * ε n ^ 2 := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

/-- Lemma 4.8c (Two-phase endpoint polar representation) (1): for both endpoint
phases of every sufficiently small slow-curve orbit, the endpoint displacement
has the canonical polar direction and current amplitude up to `o(ε_j ^ 2)`,
while its lifted polar angle differs from the cycle frame by `O(ε_j ^ 2)`.
The current amplitude converges to the prescribed positive limit `Glim`. -/
theorem slowCurveEndpointPolarRepresentation (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ σ : Fin 2,
                (fun j : ℕ ↦ orbit.endpoint (2 * j + σ.val) - Clim -
                    (orbit.state j).amplitude •
                      EuclideanPlane.rotation
                        (orbit.endpointPolarAngle Clim (2 * j + σ.val))
                        (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =o[atTop]
                  (fun j : ℕ ↦ (orbit.state j).ε ^ 2) ∧
                (fun j : ℕ ↦ orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                    orbit.frameAngle j) =O[atTop]
                  (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
  have hInvariantState :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')) := by
    simpa only [DFP.TwoLeg.extendedMap] using h_invariant
  obtain ⟨ηRad, hηRad, hRad⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorIsLittleO
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηNonzero, hηNonzero, hNonzero⟩ :=
    endpointSubCenterNonzero
      p h hInvariantState h_pJet h_hJet
  obtain ⟨ηBoundary, hηBoundary, hBoundary⟩ :=
    DFP.TwoPhaseOrbit.slowCurveBoundaryPolarExpansion
      p h hInvariantState h_pJet h_hJet
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hAmpUniform⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds
      p h hInvariantState h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph
      p h hInvariantState h_pJet h_hJet
  obtain ⟨ηNext, hηNext, hNext⟩ :=
    DFP.TwoLeg.slowCurveNextPosLt p h h_pJet h_hJet
  obtain ⟨ηValid, hηValid, hValid⟩ :=
    DFP.TwoPhaseOrbit.ofSlowCurve_phaseValidity
      p h hInvariantState h_pJet h_hJet ηBoundary hηBoundary
  obtain ⟨ηGap, hηGap, hGap⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointPolarAngleGapExplicitBounds
      p h hInvariantState h_pJet h_hJet
  obtain ⟨ηPhysical, hηPhysical, Kphysical, hKphysical, hPhysical⟩ :=
    slowCurveEvenPolarPhysicalCorrectionControl
      p h hInvariantState h_pJet h_hJet
  obtain ⟨ηFrame, hηFrame, hFrameRep⟩ :=
    DFP.TwoPhaseOrbit.slowCurveFrameAngleRepresentsLowVector
      p h hInvariantState h_pJet h_hJet (1 / 8) (by constructor <;> norm_num)
  let ηCorr := min (1 / 8 : ℝ)
    (Real.pi / (16 * (Kphysical + 1)))
  have hηCorr : 0 < ηCorr := by
    dsimp only [ηCorr]
    have hden : 0 < 16 * (Kphysical + 1) := by positivity
    exact lt_min (by norm_num) (div_pos Real.pi_pos hden)
  let ηTail := min ηFrame ηCorr
  let ηPhysicalFrame := min ηPhysical ηTail
  let ηGapPhysical := min ηGap ηPhysicalFrame
  let ηValidGap := min ηValid ηGapPhysical
  let ηGraphValid := min ηGraph (min ηNext ηValidGap)
  let ηAmpGraph := min ηAmp ηGraphValid
  let ηBoundaryAmp := min ηBoundary ηAmpGraph
  let ηNonzeroBoundary := min ηNonzero ηBoundaryAmp
  let εbar := min ηRad ηNonzeroBoundary
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · have hηTail : 0 < ηTail := lt_min hηFrame.1 hηCorr
      have hηPhysicalFrame : 0 < ηPhysicalFrame := lt_min hηPhysical.1 hηTail
      have hηGapPhysical : 0 < ηGapPhysical := lt_min hηGap.1 hηPhysicalFrame
      have hηValidGap : 0 < ηValidGap := lt_min hηValid.1 hηGapPhysical
      have hηGraphValid : 0 < ηGraphValid :=
        lt_min hηGraph.1 (lt_min hηNext hηValidGap)
      have hηAmpGraph : 0 < ηAmpGraph := lt_min hηAmp.1 hηGraphValid
      have hηBoundaryAmp : 0 < ηBoundaryAmp := lt_min hηBoundary.1 hηAmpGraph
      have hηNonzeroBoundary : 0 < ηNonzeroBoundary :=
        lt_min hηNonzero.1 hηBoundaryAmp
      exact lt_min hηRad.1 hηNonzeroBoundary
    · exact (min_le_left _ _).trans_lt hηRad.2
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεRad : ε₀ ∈ Set.Ioc 0 ηRad :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεNonzero : ε₀ ∈ Set.Ioc 0 ηNonzero :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεBoundary : ε₀ ∈ Set.Ioc 0 ηBoundary :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hεAmp : ε₀ ∈ Set.Ioc 0 ηAmp :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))⟩
  have hεValid : ε₀ ∈ Set.Ioc 0 ηValid := by
    constructor
    · exact hε₀.1
    · calc
        ε₀ ≤ min ηRad (min ηNonzero
            (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))))) := hε₀.2
        _ ≤ min ηNonzero (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical))))) := min_le_right _ _
        _ ≤ min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))) := min_le_right _ _
        _ ≤ min ηAmp (min ηGraph (min ηNext (min ηValid ηGapPhysical))) :=
          min_le_right _ _
        _ ≤ min ηGraph (min ηNext (min ηValid ηGapPhysical)) := min_le_right _ _
        _ ≤ min ηNext (min ηValid ηGapPhysical) := min_le_right _ _
        _ ≤ min ηValid ηGapPhysical := min_le_right _ _
        _ ≤ ηValid := min_le_left _ _
  have hεGap : ε₀ ∈ Set.Ioc 0 ηGap := by
    constructor
    · exact hε₀.1
    · calc
        ε₀ ≤ min ηRad (min ηNonzero
            (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))))) := hε₀.2
        _ ≤ min ηNonzero (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical))))) := min_le_right _ _
        _ ≤ min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))) := min_le_right _ _
        _ ≤ min ηAmp (min ηGraph (min ηNext (min ηValid ηGapPhysical))) :=
          min_le_right _ _
        _ ≤ min ηGraph (min ηNext (min ηValid ηGapPhysical)) := min_le_right _ _
        _ ≤ min ηNext (min ηValid ηGapPhysical) := min_le_right _ _
        _ ≤ min ηValid ηGapPhysical := min_le_right _ _
        _ ≤ ηGapPhysical := min_le_right _ _
        _ ≤ min ηGap ηPhysicalFrame := le_rfl
        _ ≤ ηGap := min_le_left _ _
  have hεPhysical : ε₀ ∈ Set.Ioc 0 ηPhysical := by
    constructor
    · exact hε₀.1
    · calc
        ε₀ ≤ min ηRad (min ηNonzero
            (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))))) := hε₀.2
        _ ≤ min ηNonzero (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical))))) := min_le_right _ _
        _ ≤ min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))) := min_le_right _ _
        _ ≤ min ηAmp (min ηGraph (min ηNext (min ηValid ηGapPhysical))) :=
          min_le_right _ _
        _ ≤ min ηGraph (min ηNext (min ηValid ηGapPhysical)) := min_le_right _ _
        _ ≤ min ηNext (min ηValid ηGapPhysical) := min_le_right _ _
        _ ≤ min ηValid ηGapPhysical := min_le_right _ _
        _ ≤ ηGapPhysical := min_le_right _ _
        _ ≤ ηPhysicalFrame := by
          simpa only [ηGapPhysical] using (min_le_right ηGap ηPhysicalFrame)
        _ ≤ ηPhysical := by
          simpa only [ηPhysicalFrame] using (min_le_left ηPhysical ηTail)
  have hεFrame : ε₀ ∈ Set.Ioc 0 ηFrame := by
    constructor
    · exact hε₀.1
    · calc
        ε₀ ≤ min ηRad (min ηNonzero
            (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))))) := hε₀.2
        _ ≤ min ηNonzero (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical))))) := min_le_right _ _
        _ ≤ min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))) := min_le_right _ _
        _ ≤ min ηAmp (min ηGraph (min ηNext (min ηValid ηGapPhysical))) :=
          min_le_right _ _
        _ ≤ min ηGraph (min ηNext (min ηValid ηGapPhysical)) := min_le_right _ _
        _ ≤ min ηNext (min ηValid ηGapPhysical) := min_le_right _ _
        _ ≤ min ηValid ηGapPhysical := min_le_right _ _
        _ ≤ ηGapPhysical := min_le_right _ _
        _ ≤ ηFrame := by
          simpa only [ηGapPhysical, ηPhysicalFrame, ηTail] using
            ((min_le_right ηGap ηPhysicalFrame).trans
              ((min_le_right ηPhysical ηTail).trans (min_le_left ηFrame ηCorr)))
  have hεCorr : ε₀ ∈ Set.Ioc 0 ηCorr := by
    constructor
    · exact hε₀.1
    · calc
        ε₀ ≤ min ηRad (min ηNonzero
            (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))))) := hε₀.2
        _ ≤ min ηNonzero (min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical))))) := min_le_right _ _
        _ ≤ min ηBoundary (min ηAmp (min ηGraph
              (min ηNext (min ηValid ηGapPhysical)))) := min_le_right _ _
        _ ≤ min ηAmp (min ηGraph (min ηNext (min ηValid ηGapPhysical))) :=
          min_le_right _ _
        _ ≤ min ηGraph (min ηNext (min ηValid ηGapPhysical)) := min_le_right _ _
        _ ≤ min ηNext (min ηValid ηGapPhysical) := min_le_right _ _
        _ ≤ min ηValid ηGapPhysical := min_le_right _ _
        _ ≤ ηGapPhysical := min_le_right _ _
        _ ≤ ηCorr := by
          simpa only [ηGapPhysical, ηPhysicalFrame, ηTail] using
            ((min_le_right ηGap ηPhysicalFrame).trans
              ((min_le_right ηPhysical ηTail).trans (min_le_right ηFrame ηCorr)))
  have hεNext : ε₀ ∈ Set.Ioc 0 ηNext := by
    have hεbarNext : εbar ≤ ηNext := by
      dsimp only [εbar, ηNonzeroBoundary, ηBoundaryAmp, ηAmpGraph,
        ηGraphValid]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))))
    exact ⟨hε₀.1, hε₀.2.trans hεbarNext⟩
  intro Clim hClim Glim hGlim hAmp σ
  have hradial := hRad ε₀ hεRad Clim hClim σ
  have hnonzero (j : ℕ) : orbit.endpoint (2 * j + σ.val) - Clim ≠ 0 := by
    simpa only [orbit] using hNonzero ε₀ hεNonzero Clim hClim (2 * j + σ.val)
  constructor
  · have hunit : ∀ j : ℕ, ‖EuclideanPlane.rotation
        (orbit.endpointPolarAngle Clim (2 * j + σ.val))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)‖ = 1 := by
      intro j
      simpa using (EuclideanPlane.rotation
        (orbit.endpointPolarAngle Clim (2 * j + σ.val))).norm_map
        (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    have htransport := polarVectorRemainderOfRadialRemainder
      (l := atTop) (u := fun j : ℕ ↦
        EuclideanPlane.rotation (orbit.endpointPolarAngle Clim (2 * j + σ.val))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (Eventually.of_forall hunit) hradial
    apply htransport.congr'
      (Eventually.of_forall (fun j ↦ ?_)) (Eventually.of_forall (fun _ ↦ rfl))
    have hspec := orbit.endpointPolarAngle_spec Clim (2 * j + σ.val) (hnonzero j)
    rw [hspec]
    module
  · -- The even endpoint is compared with the low frame direction using the
    -- boundary expansion; the odd endpoint then differs by one explicit gap.
    obtain ⟨_, _, _, hAmpBoundsRaw⟩ := hAmpUniform ε₀ hεAmp
    have hAmpBounds (j : ℕ) :
        (orbit.state j).amplitude ∈ Set.Icc Gmin Gmax := by
      simpa only [orbit] using hAmpBoundsRaw j
    have hvalid (j : ℕ) : DFP.TwoPhaseOrbit.State.PhaseValidity (orbit.state j) := by
      simpa only [orbit] using hValid ε₀ hεValid j
    have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
      have hx := hGraph ε₀ hεGraph j
      have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
      have hc' : (orbit.state j).coordinates =
          DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
        simpa only [orbit] using hc
      have heq : (orbit.state j).ε =
          (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
        simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hc'
      rw [heq]
      exact hx.2
    have hcoordinate (j : ℕ) : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using
        DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hscaleEq (j : ℕ) : (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
      simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
        congrArg Prod.fst (hcoordinate j)
    have hforward (j : ℕ) := hGraph ε₀ hεGraph j
    have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := by
      rw [hscaleEq j]
      exact (hforward j).2.1
    have hscaleLeInitial (j : ℕ) : (orbit.state j).ε ≤ ε₀ := by
      rw [hscaleEq j]
      exact (hforward j).2.2
    have hstep (j : ℕ) : (orbit.state (j + 1)).ε < (orbit.state j).ε := by
      have hjPositive : 0 <
          (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
        simpa only [← hscaleEq j] using hscalePos j
      have hjUpper :
          (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 ≤ ηNext :=
        ((hscaleEq j).symm ▸ hscaleLeInitial j).trans hεNext.2
      have hjMem :
          (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 ∈
            Set.Ioc (0 : ℝ) ηNext := ⟨hjPositive, hjUpper⟩
      have hlt := hNext _ hjMem
      have hnextCoordinate : (orbit.state (j + 1)).coordinates =
          DFP.TwoLeg.stateMap
            (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)) := by
        calc
          (orbit.state (j + 1)).coordinates =
              DFP.TwoLeg.stateMap^[j + 1] (ε₀, p ε₀, h ε₀) :=
            hcoordinate (j + 1)
          _ = DFP.TwoLeg.stateMap
              (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)) := by
            rw [Function.iterate_succ_apply']
      have hnextScale := congrArg Prod.fst hnextCoordinate
      calc
        (orbit.state (j + 1)).ε =
            (DFP.TwoLeg.stateMap
              (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀))).1 := by
          simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using hnextScale
        _ = DFP.TwoLeg.signedEpsilon
              (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1
              (p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1)
              (h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) := by
          rw [(hforward j).1]
          simpa only [Prod.fst] using DFP.TwoLeg.stateMap_fst
            (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1
            (p (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1)
            (h (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1)
        _ < (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := hlt.2
        _ = (orbit.state j).ε := (hscaleEq j).symm
    have hscaleAnti (a b : ℕ) (hab : a ≤ b) :
        (orbit.state b).ε ≤ (orbit.state a).ε := by
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ b hab ih => exact (hstep b).le.trans ih
    have hboundary := hBoundary ε₀ hεBoundary Clim hClim
    dsimp only [orbit] at hboundary
    have hgap := hGap ε₀ hεGap Clim hClim
    dsimp only [orbit] at hgap
    have hεPhysical' : ε₀ ∈ Set.Ioc 0 ηPhysical := hεPhysical
    have hεFrame' : ε₀ ∈ Set.Ioc 0 ηFrame := hεFrame
    have hεCorr' : ε₀ ∈ Set.Ioc 0 ηCorr := hεCorr
    have hphysicalControl := hPhysical ε₀ hεPhysical' Clim hClim
    have hphysicalSmall (j : ℕ) :
        |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpoint (2 * j) - Clim)).toReal| < Real.pi / 8 := by
      simpa only [orbit] using hphysicalControl.1 j
    have hinitial : (orbit.state 0).lowVector =
        EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
      simpa only [orbit] using slowCurveInitialLowVector p h ε₀
    have hlow (j : ℕ) : (orbit.state j).lowVector ≠ 0 := by
      have hnorm := (boundaryFrameColumnNorms (orbit.state j)
        (hvalid j).frame_specialOrthogonal).1
      intro hz
      rw [hz] at hnorm
      norm_num at hnorm
    have hbasis : (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≠ 0 := by
      intro hz
      have hcoordinate := congrArg
        (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hz
      simp [EuclideanSpace.basisFun_apply] at hcoordinate
    have hangle (j : ℕ) : EuclideanPlane.orientation.oangle
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) (orbit.state j).lowVector =
          (orbit.frameAngle j : Real.Angle) := by
      have hrot : (orbit.state j).lowVector =
          EuclideanPlane.rotation (orbit.frameAngle j)
            (orbit.state 0).lowVector := by
        simpa only [orbit] using hFrameRep ε₀ hεFrame' j
      rw [hrot, hinitial]
      simpa only [EuclideanPlane.rotation] using
        EuclideanPlane.orientation.oangle_rotation_self_right hbasis
          (orbit.frameAngle j)
    have hradialAll (k : ℕ) : orbit.endpoint k - Clim ≠ 0 := by
      simpa only [orbit] using hNonzero ε₀ hεNonzero Clim hClim k
    have hbridge := endpointPolarLiftFrameQuotient orbit Clim hinitial hlow hangle hradialAll
    have hgapSmall (k : ℕ) :
        |(orbit.endpointPolarAngle Clim (k + 1) -
          orbit.endpointPolarAngle Clim k).toReal| < Real.pi / 8 := by
      rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · have hb := hgap.2 j 0
        have hnonneg : 0 ≤ orbit.endpointPolarAngleLift Clim (2 * j) -
            orbit.endpointPolarAngleLift Clim (2 * j + 1) := by
          exact (show 0 ≤ (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 by positivity).trans hb.1
        have habs : |orbit.endpointPolarAngleLift Clim (2 * j + 1) -
            orbit.endpointPolarAngleLift Clim (2 * j)| ≤
            (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
          calc
            _ = |-(orbit.endpointPolarAngleLift Clim (2 * j) -
                orbit.endpointPolarAngleLift Clim (2 * j + 1))| := by
              congr 1 <;> ring
            _ = orbit.endpointPolarAngleLift Clim (2 * j) -
                orbit.endpointPolarAngleLift Clim (2 * j + 1) := by
              rw [abs_neg, abs_of_nonneg hnonneg]
            _ ≤ _ := hb.2
        rw [← orbit.endpointPolarAngleLift_succ_sub Clim (2 * j)]
        have he : (orbit.state j).ε ≤ (1 / 8 : ℝ) :=
          (hscale j).2.trans (hεCorr.2.trans (min_le_left _ _))
        have hsquare : (orbit.state j).ε ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
          have hleft : 0 ≤ (1 / 8 : ℝ) - (orbit.state j).ε :=
            sub_nonneg.mpr he
          have hright : 0 ≤ (1 / 8 : ℝ) + (orbit.state j).ε :=
            add_nonneg (by norm_num) (hscale j).1.le
          nlinarith [mul_nonneg hleft hright]
        exact habs.trans_lt (by
          nlinarith [Real.one_le_pi_div_two, hsquare])
      · have hb := hgap.2 j 1
        have hnonneg : 0 ≤ orbit.endpointPolarAngleLift Clim (2 * j + 1) -
            orbit.endpointPolarAngleLift Clim (2 * j + 2) := by
          exact (show 0 ≤ (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 by positivity).trans hb.1
        have habs : |orbit.endpointPolarAngleLift Clim (2 * j + 2) -
            orbit.endpointPolarAngleLift Clim (2 * j + 1)| ≤
            (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
          calc
            _ = |-(orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                orbit.endpointPolarAngleLift Clim (2 * j + 2))| := by
              congr 1 <;> ring
            _ = orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                orbit.endpointPolarAngleLift Clim (2 * j + 2) := by
              rw [abs_neg, abs_of_nonneg hnonneg]
            _ ≤ _ := hb.2
        rw [← orbit.endpointPolarAngleLift_succ_sub Clim (2 * j + 1)]
        have he : (orbit.state j).ε ≤ (1 / 8 : ℝ) :=
          (hscale j).2.trans (hεCorr.2.trans (min_le_left _ _))
        have hsquare : (orbit.state j).ε ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
          have hleft : 0 ≤ (1 / 8 : ℝ) - (orbit.state j).ε :=
            sub_nonneg.mpr he
          have hright : 0 ≤ (1 / 8 : ℝ) + (orbit.state j).ε :=
            add_nonneg (by norm_num) (hscale j).1.le
          nlinarith [mul_nonneg hleft hright]
        exact habs.trans_lt (by
          nlinarith [Real.one_le_pi_div_two, hsquare])
    -- Route correction: an eventual correction estimate cannot fix the initial
    -- `2π` branch.  The all-index smallness component fixes that branch, while
    -- the boundary expansion below supplies the quantitative Big-O estimate.
    have hprincipal (j : ℕ) :
        (EuclideanPlane.orientation.oangle (orbit.state j).lowVector
            (orbit.endpoint (2 * j) - Clim)).toReal +
            (orbit.endpointPolarAngle Clim (2 * j + 1) -
              orbit.endpointPolarAngle Clim (2 * j)).toReal +
            (orbit.endpointPolarAngle Clim ((2 * j + 1) + 1) -
              orbit.endpointPolarAngle Clim (2 * j + 1)).toReal -
            (orbit.frameAngle (j + 1) - orbit.frameAngle j) ∈
          Set.Ioc (-Real.pi) Real.pi := by
      rcases abs_lt.mp (hphysicalSmall j) with ⟨haLower, haUpper⟩
      rcases abs_lt.mp (hgapSmall (2 * j)) with ⟨hbLower, hbUpper⟩
      rcases abs_lt.mp (hgapSmall (2 * j + 1)) with ⟨hcLower, hcUpper⟩
      have hδ : orbit.frameAngle (j + 1) - orbit.frameAngle j =
          (orbit.state j).angleIncrement := by
        rw [DFP.TwoPhaseOrbit.frameAngle_succ]
        ring_nf
      have hd : orbit.frameAngle (j + 1) - orbit.frameAngle j ∈
          Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        simpa only [hδ] using (orbit.state j).angleIncrement_mem_interval
      constructor <;> linarith [Real.pi_pos, hd.1, hd.2]
    have hlift (j : ℕ) :
        orbit.endpointPolarAngleLift Clim (2 * j) -
        orbit.frameAngle j =
        (EuclideanPlane.orientation.oangle (orbit.state j).lowVector
          (orbit.endpoint (2 * j) - Clim)).toReal := by
      exact DFP.TwoPhaseOrbit.endpointPolarAngleLift_even_eq_frameAngle_add_correction_of_mem_Ioc
        orbit Clim hbridge.1 hbridge.2 hprincipal j
    have hGmax : 0 < Gmax := hGmin.trans_le hGminMax
    let Kangle : ℝ := Real.pi * (6 * Gmax / Gmin)
    have hKangle : 0 < Kangle := by
      dsimp only [Kangle]
      positivity
    have hrem : ∀ᶠ j : ℕ in atTop,
        ‖orbit.endpoint (2 * j) - Clim -
            (orbit.state j).amplitude •
              WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2])‖ ≤
          (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by
      filter_upwards [hboundary.eventuallyLE] with j hj
      have hApos : 0 < (orbit.state j).amplitude :=
        lt_of_lt_of_le hGmin (hAmpBounds j).1
      have hepos : 0 < (orbit.state j).ε := (hscale j).1
      simpa only [orbit, DFP.TwoPhaseOrbit.endpoint_even, norm_mul, norm_pow,
        Real.norm_eq_abs, abs_of_pos hApos,
        abs_of_pos hepos] using hj
    have hEven :
        (fun j : ℕ ↦ orbit.endpointPolarAngleLift Clim (2 * j) -
          orbit.frameAngle j) =O[atTop]
          (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨Kangle, ?_⟩
      filter_upwards [hrem] with j hj
      have hA : (orbit.state j).amplitude ∈ Set.Icc Gmin Gmax := hAmpBounds j
      have hApos : 0 < (orbit.state j).amplitude := lt_of_lt_of_le hGmin hA.1
      have hepos : 0 < (orbit.state j).ε := (hscale j).1
      have hεquarter : (orbit.state j).ε < (1 / 4 : ℝ) := by
        exact lt_of_le_of_lt (hscale j).2
          (lt_of_le_of_lt hε₀.2 hεbar.2)
      have hcols := boundaryFrameColumnNorms (orbit.state j)
        (hvalid j).frame_specialOrthogonal
      have hmodelSub := boundaryModel_sub_lowVector (orbit.state j)
      have hcorrection :
          ‖(orbit.state j).amplitude •
              WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2]) -
            (orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
            2 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by
        rw [← smul_sub, hmodelSub, norm_smul, norm_smul, hcols.2,
          Real.norm_eq_abs, abs_of_pos hApos]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        ring_nf
        exact le_rfl
      have hpertAmp :
          ‖orbit.endpoint (2 * j) - Clim -
              (orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
            3 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by
        have hdecomp : orbit.endpoint (2 * j) - Clim -
              (orbit.state j).amplitude • (orbit.state j).lowVector =
            (orbit.endpoint (2 * j) - Clim -
                (orbit.state j).amplitude •
                  WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                    ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2])) +
              ((orbit.state j).amplitude •
                  WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                    ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2]) -
                (orbit.state j).amplitude • (orbit.state j).lowVector) := by
          abel
        rw [hdecomp]
        calc
          ‖orbit.endpoint (2 * j) - Clim -
                (orbit.state j).amplitude •
                  WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                    ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2]) +
              ((orbit.state j).amplitude •
                  WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                    ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2]) -
                (orbit.state j).amplitude • (orbit.state j).lowVector)‖ ≤
              ‖orbit.endpoint (2 * j) - Clim -
                (orbit.state j).amplitude •
                  WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                    ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2])‖ +
                ‖(orbit.state j).amplitude •
                  WithLp.toLp 2 ((orbit.state j).frame *ᵥ
                    ![(1 : ℝ), 2 * (orbit.state j).ε ^ 2]) -
                  (orbit.state j).amplitude • (orbit.state j).lowVector‖ :=
            norm_add_le _ _
          _ ≤ (orbit.state j).amplitude * (orbit.state j).ε ^ 2 +
              2 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 :=
            add_le_add hj hcorrection
          _ = 3 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := by ring
      have hbase : Gmin / 2 ≤ ‖(orbit.state j).amplitude •
          (orbit.state j).lowVector‖ := by
        rw [norm_smul, hcols.1, Real.norm_eq_abs, abs_of_pos hApos]
        nlinarith [hA.1]
      have hendpoint : Gmin / 2 ≤ ‖orbit.endpoint (2 * j) - Clim‖ := by
        have hnormA : ‖(orbit.state j).amplitude • (orbit.state j).lowVector‖ =
            (orbit.state j).amplitude := by
          rw [norm_smul, hcols.1, Real.norm_eq_abs, abs_of_pos hApos]
          ring
        have htriangle : ‖(orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
            ‖orbit.endpoint (2 * j) - Clim‖ +
              ‖orbit.endpoint (2 * j) - Clim -
                (orbit.state j).amplitude • (orbit.state j).lowVector‖ := by
          have hcancellation :
              (orbit.endpoint (2 * j) - Clim) -
                  (orbit.endpoint (2 * j) - Clim -
                    (orbit.state j).amplitude • (orbit.state j).lowVector) =
                (orbit.state j).amplitude • (orbit.state j).lowVector := by abel
          calc
            ‖(orbit.state j).amplitude • (orbit.state j).lowVector‖ =
                ‖(orbit.endpoint (2 * j) - Clim) -
                  (orbit.endpoint (2 * j) - Clim -
                    (orbit.state j).amplitude • (orbit.state j).lowVector)‖ := by
              rw [hcancellation]
            _ ≤ _ := norm_sub_le _ _
        have hsmall : 3 * (orbit.state j).amplitude *
            (orbit.state j).ε ^ 2 ≤ (orbit.state j).amplitude / 2 := by
          have hele : (orbit.state j).ε ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
            have hprod : 0 ≤ ((1 / 4 : ℝ) - (orbit.state j).ε) *
                ((1 / 4 : ℝ) + (orbit.state j).ε) := by
              exact mul_nonneg (sub_nonneg.mpr (le_of_lt hεquarter)) (by positivity)
            nlinarith
          nlinarith [hA.1, hA.2, sq_nonneg ((orbit.state j).ε)]
        have hpertHalf :
            ‖orbit.endpoint (2 * j) - Clim -
                (orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
              (orbit.state j).amplitude / 2 := hpertAmp.trans hsmall
        linarith [hA.1, hnormA, hbase, htriangle, hpertHalf]
      have hpert :
          ‖orbit.endpoint (2 * j) - Clim -
              (orbit.state j).amplitude • (orbit.state j).lowVector‖ ≤
            3 * Gmax * (orbit.state j).ε ^ 2 := by
        calc
          _ ≤ 3 * (orbit.state j).amplitude * (orbit.state j).ε ^ 2 := hpertAmp
          _ ≤ 3 * Gmax * (orbit.state j).ε ^ 2 := by
            gcongr
            exact hA.2
      have hangle := DFP.TwoPhaseOrbit.abs_oangle_toReal_le_of_norm_perturbation
        EuclideanPlane.orientation
        ((orbit.state j).amplitude • (orbit.state j).lowVector)
        (orbit.endpoint (2 * j) - Clim) (Gmin / 2)
        (3 * Gmax * (orbit.state j).ε ^ 2) (by positivity) hbase hendpoint hpert
      rw [EuclideanPlane.orientation.oangle_smul_left_of_pos _ _ hApos] at hangle
      rw [Real.norm_eq_abs, hlift j]
      calc
        |(EuclideanPlane.orientation.oangle (orbit.state j).lowVector
            (orbit.endpoint (2 * j) - Clim)).toReal| ≤
            Real.pi * (3 * Gmax * (orbit.state j).ε ^ 2) / (Gmin / 2) := hangle
        _ = Kangle * (orbit.state j).ε ^ 2 := by
          dsimp only [Kangle]
          field_simp [ne_of_gt hGmin]
          ring
        _ = Kangle * ‖(orbit.state j).ε ^ 2‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hOdd :
        (fun j : ℕ ↦ orbit.endpointPolarAngleLift Clim (2 * j + 1) -
          orbit.frameAngle j) =O[atTop]
          (fun j : ℕ ↦ (orbit.state j).ε ^ 2) := by
      obtain ⟨KEven, hEvenBound⟩ := Asymptotics.isBigO_iff.mp hEven
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨KEven + (5 / 2 : ℝ), ?_⟩
      filter_upwards [hEvenBound, Eventually.of_forall (fun j ↦ hgap.2 j 0)] with j hjEven hjGap
      have hsub : orbit.endpointPolarAngleLift Clim (2 * j + 1) -
          orbit.frameAngle j =
          (orbit.endpointPolarAngleLift Clim (2 * j) - orbit.frameAngle j) -
            (orbit.endpointPolarAngleLift Clim (2 * j) -
              orbit.endpointPolarAngleLift Clim (2 * j + 1)) := by ring
      rw [hsub]
      have hε : 0 ≤ (orbit.state j).ε ^ 2 := sq_nonneg _
      have hjEven' :
          |orbit.endpointPolarAngleLift Clim (2 * j) - orbit.frameAngle j| ≤
            KEven * (orbit.state j).ε ^ 2 := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hε] using hjEven
      have hjGap' :
          |orbit.endpointPolarAngleLift Clim (2 * j) -
              orbit.endpointPolarAngleLift Clim (2 * j + 1)| ≤
            (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
        have hnonneg : 0 ≤ orbit.endpointPolarAngleLift Clim (2 * j) -
            orbit.endpointPolarAngleLift Clim (2 * j + 1) := by
          have hlow : 0 ≤ (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by positivity
          exact hlow.trans (by simpa using hjGap.1)
        rw [abs_of_nonneg hnonneg]
        simpa using hjGap.2
      calc
        |(orbit.endpointPolarAngleLift Clim (2 * j) - orbit.frameAngle j) -
            (orbit.endpointPolarAngleLift Clim (2 * j) -
              orbit.endpointPolarAngleLift Clim (2 * j + 1))| ≤
            |orbit.endpointPolarAngleLift Clim (2 * j) - orbit.frameAngle j| +
              |orbit.endpointPolarAngleLift Clim (2 * j) -
                orbit.endpointPolarAngleLift Clim (2 * j + 1)| := abs_sub _ _
        _ ≤ KEven * (orbit.state j).ε ^ 2 +
              (5 / 2 : ℝ) * (orbit.state j).ε ^ 2 :=
            add_le_add hjEven' hjGap'
        _ = (KEven + (5 / 2 : ℝ)) * (orbit.state j).ε ^ 2 := by ring
        _ = (KEven + (5 / 2 : ℝ)) * ‖(orbit.state j).ε ^ 2‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hε]
    fin_cases σ
    · simpa using hEven
    · simpa using hOdd

/- Lemma 4.8c (Two-phase endpoint polar representation) (2): the cycle-boundary
specialization is the existing second-order physical-frame expansion. -/
#check (DFP.TwoPhaseOrbit.slowCurveBoundaryPolarExpansion :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          (fun j : ℕ ↦
              let s := orbit.state j
              s.point - Clim -
                s.amplitude • WithLp.toLp 2 (s.frame *ᵥ ![(1 : ℝ), 2 * s.ε ^ 2])) =o[atTop]
            (fun j : ℕ ↦
              let s := orbit.state j
              s.amplitude * s.ε ^ 2))
