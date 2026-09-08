module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumC2Jets
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.JetDecay
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.ShrinkingSupport
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumWeightedBounds
import ReasLib.Analysis.Calculus.Gradient.HessianNorm
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointBump.Interpolation

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace DFP.TwoLeg.SlowCurve

/-- An invariant slow curve admits a common small-scale threshold on which the
endpoint-bump correction is twice continuously differentiable and has zero
value, gradient, and Hessian on its limiting circle. -/
theorem bumpCorrectionContDiffTwoAndZeroJets (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ContDiff ℝ 2 (orbit.bumpCorrection Clim Glim) ∧
                EqOn (orbit.bumpCorrection Clim Glim) 0
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∧
                EqOn (gradient (orbit.bumpCorrection Clim Glim)) 0
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∧
                EqOn (EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim)) 0
                  (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  obtain ⟨ηRadius, hηRadius, hRadius⟩ := curve.interpolationRadius_pos
  obtain ⟨ηShrink, hηShrink, hShrink⟩ := curve.interpolationRadiusTendstoZero
  obtain ⟨ηCluster, hηCluster, hCluster⟩ := curve.endpointClusterPt_mem_limitCircle
  obtain ⟨ηBalls, hηBalls, hBalls⟩ := curve.pairwiseDisjointInterpolationClosedBalls
  obtain ⟨ηCircle, hηCircle, hCircle⟩ :=
    curve.interpolationClosedBallDisjointLimitCircle
  obtain ⟨ηJets, hηJets, hJets⟩ := curve.endpointBumpSecondOrderJetsVanish
  let εbar := min ηRadius
    (min ηShrink (min ηCluster (min ηBalls (min ηCircle ηJets))))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηRadius.1
      (lt_min hηShrink.1 (lt_min hηCluster.1
        (lt_min hηBalls.1 (lt_min hηCircle.1 hηJets.1))))
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηRadius.2
  have hεbarLeRadius : εbar ≤ ηRadius := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hεbarLeShrink : εbar ≤ ηShrink := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεbarLeCluster : εbar ≤ ηCluster := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hεbarLeBalls : εbar ≤ ηBalls := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεbarLeCircle : εbar ≤ ηCircle := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεbarLeJets : εbar ≤ ηJets := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεRadius : ε₀ ∈ Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeRadius⟩
  have hεShrink : ε₀ ∈ Ioc 0 ηShrink :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeShrink⟩
  have hεCluster : ε₀ ∈ Ioc 0 ηCluster :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeCluster⟩
  have hεBalls : ε₀ ∈ Ioc 0 ηBalls :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeBalls⟩
  have hεCircle : ε₀ ∈ Ioc 0 ηCircle :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeCircle⟩
  have hεJets : ε₀ ∈ Ioc 0 ηJets :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeJets⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hRadiusPos : ∀ k : ℕ, 0 < orbit.interpolationRadius Clim Glim k := by
    simpa only [orbit] using
      hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto
  have hRadiusZero : Tendsto
      (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k) atTop (𝓝 0) := by
    simpa only [orbit] using
      hShrink ε₀ hεShrink Clim hClim Glim hGlim hGlimTendsto
  have hBallsData : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k)) := by
    simpa only [orbit] using
      hBalls ε₀ hεBalls Clim hClim Glim hGlim hGlimTendsto
  have hCircleData : ∀ k : ℕ, Disjoint
      (Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k))
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
    simpa only [orbit] using
      hCircle ε₀ hεCircle Clim hClim Glim hGlim hGlimTendsto
  let Γ : Set (EuclideanSpace ℝ (Fin 2)) :=
    DFP.TwoPhaseOrbit.limitCircle Clim Glim
  have hClosed : IsClosed Γ := by
    simpa only [Γ] using DFP.TwoPhaseOrbit.isClosed_limitCircle Clim Glim hGlim
  have hClusterData : ∀ y, MapClusterPt y atTop orbit.endpoint → y ∈ Γ := by
    intro y hy
    simpa only [Γ, orbit] using
      (hCluster ε₀ hεCluster Clim hClim Glim hGlim hGlimTendsto y hy)
  have hSupport (k : ℕ) : tsupport (orbit.endpointBump Clim Glim k) ⊆
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k) :=
    DFP.TwoPhaseOrbit.endpointBump_tsupport_subset_interpolationClosedBall
      orbit Clim Glim hRadiusPos k
  have hTwoLe : (2 : WithTop ℕ∞) ≤ ∞ := by
    have hTwoNat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr hTwoNat
  have hSmooth (k : ℕ) : ContDiff ℝ 2 (orbit.endpointBump Clim Glim k) :=
    (DFP.TwoPhaseOrbit.contDiff_endpointBump orbit Clim Glim k).of_le hTwoLe
  have hJetsData := hJets ε₀ hεJets Clim hClim Glim hGlim hGlimTendsto
  have hValueDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (orbit.endpointBump Clim Glim k) →
        Metric.infDist z Γ < δ →
          ‖orbit.endpointBump Clim Glim k z‖ / Metric.infDist z Γ ^ 2 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hJetsData η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z _ hz hzδ
    simpa only [Γ, orbit] using (hbound k z hz hzδ).1
  have hGradientDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (orbit.endpointBump Clim Glim k) →
        Metric.infDist z Γ < δ →
          ‖fderiv ℝ (orbit.endpointBump Clim Glim k) z‖ /
              Metric.infDist z Γ < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hJetsData η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z _ hz hzδ
    simpa only [Γ, orbit] using (hbound k z hz hzδ).2.1
  have hHessianDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (orbit.endpointBump Clim Glim k) →
        Metric.infDist z Γ < δ →
          ‖fderiv ℝ (fderiv ℝ (orbit.endpointBump Clim Glim k)) z‖ < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hJetsData η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z _ hz hzδ
    simpa only [Γ, orbit] using (hbound k z hz hzδ).2.2
  have hCertificate :=
    EuclideanPlane.contDiff_two_indicator_compl_finsum_eqOn_zero_jets
      Γ orbit.endpoint (fun k ↦ orbit.interpolationRadius Clim Glim k)
      (fun k ↦ orbit.endpointBump Clim Glim k) hClosed hClusterData
      (fun k ↦ (hRadiusPos k).le) hRadiusZero hBallsData hSupport hSmooth
      hValueDecay hGradientDecay hHessianDecay
  have hFunctionEq :
      Γᶜ.indicator (fun z ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k z) =
        orbit.bumpCorrection Clim Glim := by
    funext z
    by_cases hz : z ∈ Γ
    · have hzComplement : z ∉ Γᶜ := by
        simpa only [Set.mem_compl_iff, not_not] using hz
      rw [indicator_of_notMem hzComplement]
      have hZero (k : ℕ) : orbit.endpointBump Clim Glim k z = 0 := by
        by_contra hk
        have hzSupport : z ∈ tsupport (orbit.endpointBump Clim Glim k) :=
          subset_tsupport (orbit.endpointBump Clim Glim k) hk
        have hzBall := hSupport k hzSupport
        exact Set.disjoint_left.mp (hCircleData k) hzBall hz
      rw [DFP.TwoPhaseOrbit.bumpCorrection_apply]
      exact (finsum_eq_zero_of_forall_eq_zero (fun k ↦ hZero k)).symm
    · have hzComplement : z ∈ Γᶜ := by
        simpa only [Set.mem_compl_iff] using hz
      rw [indicator_of_mem hzComplement]
      exact (DFP.TwoPhaseOrbit.bumpCorrection_apply orbit Clim Glim z).symm
  rw [hFunctionEq] at hCertificate
  exact hCertificate

/-- The Hessian norm of the endpoint-bump correction along an invariant slow curve is
bounded globally by a constant times the initial scale, uniformly over sufficiently small
initial scales. -/
theorem bumpCorrectionHessianBound (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ z : EuclideanSpace ℝ (Fin 2),
                  ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z‖ ≤
                    K * ε₀ := by
  obtain ⟨ηRegular, hηRegular, hRegular⟩ :=
    curve.bumpCorrectionContDiffTwoAndZeroJets
  obtain ⟨ηSupport, hηSupport, cSupport, hcSupport, hSupport⟩ :=
    curve.supportInfDistLinearLower
  obtain ⟨ηShrink, hηShrink, hShrink⟩ := curve.interpolationRadiusTendstoZero
  obtain ⟨ηCluster, hηCluster, hCluster⟩ := curve.endpointClusterPt_mem_limitCircle
  obtain ⟨ηBalls, hηBalls, hBalls⟩ := curve.pairwiseDisjointInterpolationClosedBalls
  obtain ⟨ηBounds, hηBounds, Kvalue, hKvalue, Kgradient, hKgradient,
      Khessian, hKhessian, hBounds⟩ := curve.endpointBumpUniformBounds
  let εbar := min ηRegular
    (min ηSupport (min ηShrink (min ηCluster (min ηBalls ηBounds))))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηRegular.1
      (lt_min hηSupport.1 (lt_min hηShrink.1
        (lt_min hηCluster.1 (lt_min hηBalls.1 hηBounds.1))))
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηRegular.2
  have hεbarLeRegular : εbar ≤ ηRegular := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hεbarLeSupport : εbar ≤ ηSupport := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεbarLeShrink : εbar ≤ ηShrink := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεbarLeCluster : εbar ≤ ηCluster := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεbarLeBalls : εbar ≤ ηBalls := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεbarLeBounds : εbar ≤ ηBounds := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, Khessian, hKhessian, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεRegular : ε₀ ∈ Ioc 0 ηRegular :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeRegular⟩
  have hεSupport : ε₀ ∈ Ioc 0 ηSupport :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeSupport⟩
  have hεShrink : ε₀ ∈ Ioc 0 ηShrink :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeShrink⟩
  have hεCluster : ε₀ ∈ Ioc 0 ηCluster :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeCluster⟩
  have hεBalls : ε₀ ∈ Ioc 0 ηBalls :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeBalls⟩
  have hεBounds : ε₀ ∈ Ioc 0 ηBounds :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeBounds⟩
  intro Clim hClim Glim hGlim hGlimTendsto z
  have hRegularData := hRegular ε₀ hεRegular Clim hClim Glim hGlim hGlimTendsto
  have hSupportData := hSupport ε₀ hεSupport Clim hClim Glim hGlim hGlimTendsto
  have hRadiusPos : ∀ k : ℕ, 0 < orbit.interpolationRadius Clim Glim k := by
    simpa only [orbit] using hSupportData.2.1
  have hRadiusZero : Tendsto
      (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k) atTop (𝓝 0) := by
    simpa only [orbit] using
      hShrink ε₀ hεShrink Clim hClim Glim hGlim hGlimTendsto
  have hBallsData : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k)) := by
    simpa only [orbit] using
      hBalls ε₀ hεBalls Clim hClim Glim hGlim hGlimTendsto
  let Γ : Set (EuclideanSpace ℝ (Fin 2)) :=
    DFP.TwoPhaseOrbit.limitCircle Clim Glim
  have hClosed : IsClosed Γ := by
    simpa only [Γ] using DFP.TwoPhaseOrbit.isClosed_limitCircle Clim Glim hGlim
  have hClusterData : ∀ y, MapClusterPt y atTop orbit.endpoint → y ∈ Γ := by
    intro y hy
    simpa only [Γ, orbit] using
      hCluster ε₀ hεCluster Clim hClim Glim hGlim hGlimTendsto y hy
  have hSupportSubset (k : ℕ) : tsupport (orbit.endpointBump Clim Glim k) ⊆
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k) :=
    DFP.TwoPhaseOrbit.endpointBump_tsupport_subset_interpolationClosedBall
      orbit Clim Glim hRadiusPos k
  have hTwoLe : (2 : WithTop ℕ∞) ≤ ∞ := by
    have hTwoNat : (2 : ℕ∞) ≤ ⊤ := le_top
    exact WithTop.coe_le_coe.mpr hTwoNat
  have hSmooth (k : ℕ) : ContDiff ℝ 2 (orbit.endpointBump Clim Glim k) :=
    (DFP.TwoPhaseOrbit.contDiff_endpointBump orbit Clim Glim k).of_le hTwoLe
  have hBoundsData := hBounds ε₀ hεBounds Clim hClim Glim hGlim hGlimTendsto
  have hWeight : ∀ k : ℕ, 0 ≤ (orbit.state (k / 2)).ε ∧
      (orbit.state (k / 2)).ε ≤ ε₀ := by
    intro k
    constructor
    · exact (hSupportData.1 (k / 2)).1.le
    · exact (hSupportData.1 (k / 2)).2
  have hBoundIterated : ∀ k z, z ∈ tsupport (orbit.endpointBump Clim Glim k) →
      ‖iteratedFDeriv ℝ 2 (orbit.endpointBump Clim Glim k) z‖ ≤
        Khessian * (orbit.state (k / 2)).ε := by
    intro k z hz
    rw [← norm_secondFDeriv_eq_norm_iteratedFDeriv_two]
    exact (hBoundsData k z hz).2.2
  by_cases hz : z ∈ Γ
  · have hzero := hRegularData.2.2.2 hz
    calc
      ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z‖ = 0 := by
        rw [hzero]
        simp
      _ ≤ Khessian * ε₀ := mul_nonneg hKhessian.le hε₀.1.le
  · have houtside := norm_iteratedFDeriv_finsum_le_of_weighted_tsupport_bound
      2 2 Γ orbit.endpoint
      (fun k : ℕ ↦ orbit.interpolationRadius Clim Glim k)
      (fun k : ℕ ↦ orbit.endpointBump Clim Glim k)
      (fun k : ℕ ↦ (orbit.state (k / 2)).ε) Khessian ε₀ hKhessian.le hε₀.1.le
      hClosed hClusterData
      (fun k ↦ (hRadiusPos k).le) hRadiusZero hBallsData hSupportSubset hSmooth
      hWeight hBoundIterated hz le_rfl
    have hBumpEq : orbit.bumpCorrection Clim Glim =
        (fun y ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k y) := by
      funext y
      exact DFP.TwoPhaseOrbit.bumpCorrection_apply orbit Clim Glim y
    calc
      ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z‖ =
          ‖iteratedFDeriv ℝ 2 (orbit.bumpCorrection Clim Glim) z‖ := by
            rw [EuclideanPlane.hessian_def]
            exact norm_fderiv_gradient_eq_norm_iteratedFDeriv_two
              (orbit.bumpCorrection Clim Glim) z
      _ = ‖iteratedFDeriv ℝ 2
          (fun y ↦ ∑ᶠ k, orbit.endpointBump Clim Glim k y) z‖ := by
            rw [hBumpEq]
      _ ≤ Khessian * ε₀ := houtside

/-- The endpoint-bump correction along an invariant slow curve is globally twice
continuously differentiable, vanishes on its limiting circle, interpolates the prescribed
endpoint jets, and has Hessian norm bounded linearly by the initial scale. -/
theorem bumpCorrectionExtension (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Ioo (0 : ℝ) (1 / 4), ∃ K > 0,
      ∀ ε₀ ∈ Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ContDiff ℝ 2 (orbit.bumpCorrection Clim Glim) ∧
                  EqOn (orbit.bumpCorrection Clim Glim) 0
                    (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∧
                  (∀ k : ℕ,
                    orbit.bumpCorrection Clim Glim (orbit.endpoint k) = 0) ∧
                  (∀ k : ℕ,
                    gradient (orbit.bumpCorrection Clim Glim) (orbit.endpoint k) =
                      orbit.endpointCorrection Clim k) ∧
                  ∀ z : EuclideanSpace ℝ (Fin 2),
                    ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z‖ ≤
                      K * ε₀ := by
  obtain ⟨ηRegular, hηRegular, hRegular⟩ :=
    curve.bumpCorrectionContDiffTwoAndZeroJets
  obtain ⟨ηHessian, hηHessian, K, hK, hHessian⟩ :=
    curve.bumpCorrectionHessianBound
  obtain ⟨ηRadius, hηRadius, hRadius⟩ := curve.interpolationRadius_pos
  obtain ⟨ηBalls, hηBalls, hBalls⟩ := curve.pairwiseDisjointInterpolationClosedBalls
  let εbar := min ηRegular (min ηHessian (min ηRadius ηBalls))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηRegular.1 (lt_min hηHessian.1 (lt_min hηRadius.1 hηBalls.1))
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηRegular.2
  have hεbarLeRegular : εbar ≤ ηRegular := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hεbarLeHessian : εbar ≤ ηHessian := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεbarLeRadius : εbar ≤ ηRadius := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεbarLeBalls : εbar ≤ ηBalls := by
    dsimp only [εbar]
    exact (min_le_right ηRegular (min ηHessian (min ηRadius ηBalls))).trans
      ((min_le_right ηHessian (min ηRadius ηBalls)).trans
        (min_le_right ηRadius ηBalls))
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, K, hK, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεRegular : ε₀ ∈ Ioc 0 ηRegular :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeRegular⟩
  have hεHessian : ε₀ ∈ Ioc 0 ηHessian :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeHessian⟩
  have hεRadius : ε₀ ∈ Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeRadius⟩
  have hεBalls : ε₀ ∈ Ioc 0 ηBalls :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeBalls⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hRegularData := hRegular ε₀ hεRegular Clim hClim Glim hGlim hGlimTendsto
  have hHessianData := hHessian ε₀ hεHessian Clim hClim Glim hGlim hGlimTendsto
  have hRadiusPos : ∀ k : ℕ, 0 < orbit.interpolationRadius Clim Glim k := by
    simpa only [orbit] using
      hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto
  have hBallsData : Set.univ.PairwiseDisjoint (fun k : ℕ ↦
      Metric.closedBall (orbit.endpoint k)
        (orbit.interpolationRadius Clim Glim k)) := by
    simpa only [orbit] using
      hBalls ε₀ hεBalls Clim hClim Glim hGlim hGlimTendsto
  have hEndpointZero : ∀ k : ℕ,
      orbit.bumpCorrection Clim Glim (orbit.endpoint k) = 0 := by
    intro k
    exact DFP.TwoPhaseOrbit.bumpCorrection_endpoint orbit Clim Glim
      hRadiusPos hBallsData k
  have hEndpointGradient : ∀ k : ℕ,
      gradient (orbit.bumpCorrection Clim Glim) (orbit.endpoint k) =
        orbit.endpointCorrection Clim k := by
    intro k
    exact DFP.TwoPhaseOrbit.bumpCorrection_gradient_endpoint orbit Clim Glim
      hRadiusPos hBallsData k
  have hHessianBound : ∀ z : EuclideanSpace ℝ (Fin 2),
      ‖EuclideanPlane.hessian (orbit.bumpCorrection Clim Glim) z‖ ≤ K * ε₀ := by
    simpa only [orbit] using hHessianData
  refine ⟨hRegularData.1, hRegularData.2.1, hEndpointZero,
    hEndpointGradient, hHessianBound⟩

end DFP.TwoLeg.SlowCurve
