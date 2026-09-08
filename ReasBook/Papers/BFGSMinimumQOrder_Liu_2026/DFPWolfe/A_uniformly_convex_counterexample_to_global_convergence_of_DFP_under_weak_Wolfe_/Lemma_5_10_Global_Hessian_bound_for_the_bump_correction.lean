module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_5_5_Uniform_supportwise_value_gradient_and_Hessian_bounds
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_5_8_Global_C_2_extension_of_the_disjoint_bump_sum
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.ShrinkingSupport
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumWeightedBounds
import ReasLib.Analysis.Calculus.Gradient.HessianNorm

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

/-- Lemma 5.10 (Global Hessian bound for the bump correction): one positive
constant chosen before the final initial scale bounds the Hessian of the global
bump correction at every point by that constant times the initial scale. -/
theorem slowCurveBumpCorrectionHessianBound (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
                Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ z : EuclideanSpace ℝ (Fin 2),
                  ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z‖ ≤ K * ε₀ := by
  let curve := DFP.TwoLeg.SlowCurve.ofAsymptotics
    p h h_pJet h_hJet h_invariant
  obtain ⟨ηHessian, hηHessian, Khessian, hKhessian, hHessian⟩ :=
    slowCurveBumpSecondFDerivUniformBound
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηZero, hηZero, hZero⟩ :=
    slowCurveBumpCorrection_hessian_eqOn_zero
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηRadius, hηRadius, cLower, hcLower, cUpper, hcUpper, hRadius⟩ :=
    curve.interpolationRadiusUniformBounds
  obtain ⟨ηBalls, hηBalls, hBalls⟩ :=
    curve.pairwiseDisjointInterpolationClosedBalls
  obtain ⟨ηShrink, hηShrink, hShrink⟩ :=
    curve.interpolationRadiusTendstoZero
  obtain ⟨ηCluster, hηCluster, hCluster⟩ :=
    curve.endpointClusterPt_mem_limitCircle
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph
      p h h_invariant h_pJet h_hJet
  let εbar := min ηHessian
    (min ηZero (min ηRadius (min ηBalls (min ηShrink (min ηCluster ηGraph)))))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηHessian.1
      (lt_min hηZero.1 (lt_min hηRadius.1
        (lt_min hηBalls.1 (lt_min hηShrink.1 (lt_min hηCluster.1 hηGraph.1)))))
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηHessian.2
  have hεbarLeHessian : εbar ≤ ηHessian := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hεbarLeZero : εbar ≤ ηZero := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεbarLeRadius : εbar ≤ ηRadius := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hεbarLeBalls : εbar ≤ ηBalls := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεbarLeShrink : εbar ≤ ηShrink := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεbarLeCluster : εbar ≤ ηCluster := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
  have hεbarLeGraph : εbar ≤ ηGraph := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Khessian, hKhessian, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεHessian : ε₀ ∈ Ioc 0 ηHessian :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeHessian⟩
  have hεZero : ε₀ ∈ Ioc 0 ηZero :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeZero⟩
  have hεRadius : ε₀ ∈ Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeRadius⟩
  have hεBalls : ε₀ ∈ Ioc 0 ηBalls :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeBalls⟩
  have hεShrink : ε₀ ∈ Ioc 0 ηShrink :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeShrink⟩
  have hεCluster : ε₀ ∈ Ioc 0 ηCluster :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeCluster⟩
  have hεGraph : ε₀ ∈ Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeGraph⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hClimCurve : Tendsto
      (fun j : ℕ ↦
        ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j).center)
      atTop (𝓝 Clim) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hClim
  have hGlimTendstoCurve : Tendsto
      (fun j : ℕ ↦
        ((DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀).state j).amplitude)
      atTop (𝓝 Glim) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hGlimTendsto
  have hHessianData := hHessian ε₀ hεHessian Clim hClim
    Glim hGlim hGlimTendsto
  have hZeroData := hZero ε₀ hεZero Clim hClim
    Glim hGlim hGlimTendsto
  have hRadiusData (k : ℕ) : orbit.interpolationRadius Clim Glim k ∈ Icc
      (cLower * (orbit.state (k / 2)).ε ^ 2)
      (cUpper * (orbit.state (k / 2)).ε ^ 2) := by
    have hData := hRadius ε₀ hεRadius Clim hClimCurve
      Glim hGlim hGlimTendstoCurve k
    simpa only [orbit, curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high,
      DFP.TwoPhaseOrbit.endpointRadius_def] using hData
  have hBallsData : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k)) := by
    have hData := hBalls ε₀ hεBalls Clim hClimCurve
      Glim hGlim hGlimTendstoCurve
    simpa only [orbit, curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using hData
  have hShrinkData :
      Tendsto (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k)
        atTop (𝓝 0) := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using
        hShrink ε₀ hεShrink Clim hClimCurve Glim hGlim hGlimTendstoCurve
  have hClusterData : ∀ y, MapClusterPt y atTop orbit.endpoint →
      y ∈ DFP.TwoPhaseOrbit.limitCircle Clim Glim := by
    simpa only [curve, DFP.TwoLeg.SlowCurve.ofAsymptotics_shape,
      DFP.TwoLeg.SlowCurve.ofAsymptotics_high] using
        hCluster ε₀ hεCluster Clim hClimCurve Glim hGlim hGlimTendstoCurve
  have hCoordinates (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hOrbitCoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hOrbitCoordinates' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hOrbitCoordinates
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hOrbitCoordinates'
  have hScale (j : ℕ) : (orbit.state j).ε ∈ Ioc 0 ε₀ := by
    have hOrbitScale := (hGraph ε₀ hεGraph j).2
    rw [hCoordinates j]
    exact hOrbitScale
  have hRadiusPos (k : ℕ) : 0 < orbit.interpolationRadius Clim Glim k := by
    have hScaledPos : 0 < cLower * (orbit.state (k / 2)).ε ^ 2 :=
      mul_pos hcLower (pow_pos (hScale (k / 2)).1 2)
    exact hScaledPos.trans_le (hRadiusData k).1
  have hRadiusNonneg (k : ℕ) : 0 ≤ orbit.interpolationRadius Clim Glim k :=
    (hRadiusPos k).le
  have hSupport (k : ℕ) : tsupport (orbit.endpointBump Clim Glim k) ⊆
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius Clim Glim k) :=
    DFP.TwoPhaseOrbit.endpointBump_tsupport_subset_interpolationClosedBall
      orbit Clim Glim hRadiusPos k
  have hTwoLe : (2 : WithTop ℕ∞) ≤ ∞ := by
    have hTwoNat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr hTwoNat
  have hSmooth (k : ℕ) : ContDiff ℝ 2 (orbit.endpointBump Clim Glim k) :=
    (DFP.TwoPhaseOrbit.contDiff_endpointBump orbit Clim Glim k).of_le hTwoLe
  have hWeight (k : ℕ) :
      0 ≤ (orbit.state (k / 2)).ε ∧ (orbit.state (k / 2)).ε ≤ ε₀ :=
    ⟨(hScale (k / 2)).1.le, (hScale (k / 2)).2⟩
  have hIteratedBound (k : ℕ) (z : EuclideanSpace ℝ (Fin 2))
      (hz : z ∈ tsupport (orbit.endpointBump Clim Glim k)) :
      ‖iteratedFDeriv ℝ 2 (orbit.endpointBump Clim Glim k) z‖ ≤
        Khessian * (orbit.state (k / 2)).ε := by
    rw [← norm_secondFDeriv_eq_norm_iteratedFDeriv_two]
    exact hHessianData k z hz
  have hClosed : IsClosed (DFP.TwoPhaseOrbit.limitCircle Clim Glim) :=
    DFP.TwoPhaseOrbit.isClosed_limitCircle Clim Glim hGlim
  have hFunction : orbit.bumpCorrection Clim Glim =
      (fun y ↦ ∑ᶠ k : ℕ, orbit.endpointBump Clim Glim k y) := by
    funext y
    exact DFP.TwoPhaseOrbit.bumpCorrection_apply orbit Clim Glim y
  intro z
  by_cases hzCircle : z ∈ DFP.TwoPhaseOrbit.limitCircle Clim Glim
  · have hzZero : EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z = 0 := by
      simpa only [Pi.zero_apply] using hZeroData hzCircle
    rw [hzZero, norm_zero]
    exact mul_nonneg hKhessian.le hε₀.1.le
  · have hzComplement : z ∈ (DFP.TwoPhaseOrbit.limitCircle Clim Glim)ᶜ := by
      simpa only [Set.mem_compl_iff] using hzCircle
    rw [EuclideanPlane.hessian_def,
      norm_fderiv_gradient_eq_norm_iteratedFDeriv_two, hFunction]
    exact norm_iteratedFDeriv_finsum_le_of_weighted_tsupport_bound
      2 2 (DFP.TwoPhaseOrbit.limitCircle Clim Glim) orbit.endpoint
      (orbit.interpolationRadius Clim Glim)
      (fun k ↦ orbit.endpointBump Clim Glim k)
      (fun k ↦ (orbit.state (k / 2)).ε) Khessian ε₀
      hKhessian.le hε₀.1.le hClosed hClusterData hRadiusNonneg hShrinkData
      hBallsData hSupport hSmooth hWeight hIteratedBound hzComplement le_rfl
