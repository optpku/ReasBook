module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointIsolation.ShrinkingSupport
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointDistance
import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeTailUniform
import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation
import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity
import ReasLib.Topology.MetricSpace.SupportDistance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

noncomputable section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoLeg.SlowCurve

/-- Below one slow-curve threshold, a single pair of comparison constants works
for every family supported in the interpolation balls of the same orbit. -/
theorem supportInfDistBoundsUniformInSupport (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∃ cLower > 0, ∃ cUpper > 0,
                ∀ support : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
                  (∀ k, support k ⊆ Metric.closedBall (orbit.endpoint k)
                    (orbit.interpolationRadius Clim Glim k)) →
                    ∀ᶠ k : ℕ in atTop, ∀ z ∈ support k,
                      Metric.infDist z
                          (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∈ Set.Icc
                        (cLower * (orbit.state (k / 2)).ε)
                        (cUpper * (orbit.state (k / 2)).ε) := by
  obtain ⟨ηDist, hηDist, hDist⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointLimitCircleDistanceEquivalent
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  obtain ⟨ηLittle, hηLittle, hLittle⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointRadiusIsLittleODistance
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  obtain ⟨ηRadius, hηRadius, _, _, cRadiusUpper, hcRadiusUpper, hRadius⟩ :=
    curve.interpolationRadiusUniformBounds
  obtain ⟨ηPos, hηPos, hPos⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitPos
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  let εbar := min ηDist (min ηLittle (min ηRadius ηPos))
  have hεbarPos : 0 < εbar :=
    lt_min hηDist.1 (lt_min hηLittle.1 (lt_min hηRadius.1 hηPos))
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηDist.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεDist : ε₀ ∈ Set.Ioc 0 ηDist :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεLittle : ε₀ ∈ Set.Ioc 0 ηLittle :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hεPos : ε₀ ∈ Set.Ioc 0 ηPos :=
    ⟨hε₀.1, hε₀.2.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  have hcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    have hraw := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates
      curve.shape curve.high ε₀ j
    have hraw' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀) := by
      simpa only [orbit] using hraw
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hraw'
  have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := by
    rw [hcoord j]
    exact (hPos ε₀ hεPos j).1
  intro Clim hClim Glim hGlim hGlimTendsto
  let d : ℕ → ℝ := fun k ↦ Metric.infDist (orbit.endpoint k)
    (DFP.TwoPhaseOrbit.limitCircle Clim Glim)
  let scale : ℕ → ℝ := fun k ↦ (orbit.state (k / 2)).ε
  let radius : ℕ → ℝ := fun k ↦ orbit.interpolationRadius Clim Glim k
  let q : ℝ := (13 / 3 : ℝ) * Glim
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hscale (k : ℕ) : 0 < scale k := by
    simpa only [scale] using hscalePos (k / 2)
  have hDistance : d ~[atTop] (fun k ↦ q * scale k) := by
    simpa only [d, q, scale, orbit] using
      hDist ε₀ hεDist Clim hClim Glim hGlim hGlimTendsto
  have hEndpointRadiusLittle : (fun k ↦ scale k ^ 2) =o[atTop] d := by
    simpa only [scale, d, orbit] using
      hLittle ε₀ hεLittle Clim hClim Glim hGlim hGlimTendsto
  have hRadiusBigO : radius =O[atTop] (fun k ↦ scale k ^ 2) := by
    apply Asymptotics.IsBigO.of_bound cRadiusUpper
    filter_upwards [] with k
    have hBounds :=
      hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto k
    have hRadiusNonneg : 0 ≤ radius k := by
      exact DFP.TwoPhaseOrbit.interpolationRadius_nonneg orbit Clim Glim k
    simpa only [radius, scale, DFP.TwoPhaseOrbit.endpointRadius_def,
      Real.norm_eq_abs, abs_of_nonneg hRadiusNonneg,
      abs_of_nonneg (sq_nonneg (orbit.state (k / 2)).ε)] using hBounds.2
  have hRadiusLittle : radius =o[atTop] d :=
    hRadiusBigO.trans_isLittleO hEndpointRadiusLittle
  let ballSupport : ℕ → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun k ↦ Metric.closedBall (orbit.endpoint k) (radius k)
  have hballSubset : ∀ k, ballSupport k ⊆
      Metric.closedBall (orbit.endpoint k) (radius k) := by
    intro k
    exact Set.Subset.rfl
  obtain ⟨cLower, hcLower, cUpper, hcUpper, hball⟩ :=
    Metric.eventually_infDist_mem_Icc_of_support_radius_isLittleO
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim) orbit.endpoint scale radius
      ballSupport q hq hscale hDistance hRadiusLittle hballSubset
  refine ⟨cLower, hcLower, cUpper, hcUpper, ?_⟩
  intro support hsupport
  filter_upwards [hball] with k hk
  intro z hz
  exact hk z (hsupport k hz)

/-- For any one family supported in the interpolation balls of a sufficiently
small invariant slow-curve orbit, distance from support points to the limiting
circle is eventually comparable to the current cycle scale.

This compatibility form follows from `supportInfDistBoundsUniformInSupport`,
whose constants are chosen before the support family. -/
theorem supportInfDistUniformBounds (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim : EuclideanSpace ℝ (Fin 2),
        Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ support : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
                (∀ k, support k ⊆ Metric.closedBall (orbit.endpoint k)
                  (orbit.interpolationRadius Clim Glim k)) →
                  ∃ cLower > 0, ∃ cUpper > 0,
                    ∀ᶠ k : ℕ in atTop, ∀ z ∈ support k,
                      Metric.infDist z
                          (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ∈ Set.Icc
                        (cLower * (orbit.state (k / 2)).ε)
                        (cUpper * (orbit.state (k / 2)).ε) := by
  obtain ⟨εbar, hεbar, hbounds⟩ :=
    curve.supportInfDistBoundsUniformInSupport
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimTendsto support hsupport
  obtain ⟨cLower, hcLower, cUpper, hcUpper, hall⟩ :=
    hbounds ε₀ hε₀ Clim hClim Glim hGlim hGlimTendsto
  exact ⟨cLower, hcLower, cUpper, hcUpper, hall support hsupport⟩

/-- For a sufficiently small invariant slow curve, every family supported in
the interpolation balls stays at least a fixed positive multiple of the cycle
scale away from the limiting circle, uniformly over every index. -/
theorem supportInfDistLinearLowerBound (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cSupport > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ support : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
                  (∀ k, support k ⊆ Metric.closedBall (orbit.endpoint k)
                    (orbit.interpolationRadius Clim Glim k)) →
                    ∀ k : ℕ, ∀ z ∈ support k,
                      cSupport * (orbit.state (k / 2)).ε ≤
                        Metric.infDist z
                          (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  obtain ⟨ηTail, hηTail, ωG, hωGSpec, hTail⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeTailUniform
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  obtain ⟨ηPhase, hηPhase, ωR, hωRSpec, hPhase⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorUniform
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hAmp⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  obtain ⟨ηRadius, hηRadius, cRadiusLower, hcRadiusLower,
      cRadiusUpper, hcRadiusUpper, hRadius⟩ :=
    curve.interpolationRadiusUniformBounds
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  let a : ℝ := (13 / 3) * Gmin
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hωGSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωG η < a / 4 := by
    exact (tendsto_order.1 hωGSpec.2.2).2 (a / 4) (by positivity)
  have hωRSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωR η < a / 4 := by
    exact (tendsto_order.1 hωRSpec.2.2).2 (a / 4) (by positivity)
  let ηCap := min ηTail (min ηPhase (min ηAmp (min ηRadius ηGraph)))
  have hηCap : 0 < ηCap := by
    dsimp only [ηCap]
    exact lt_min hηTail.1
      (lt_min hηPhase.1 (lt_min hηAmp.1 (lt_min hηRadius.1 hηGraph.1)))
  have hηCapMem : Set.Ioc (0 : ℝ) ηCap ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT hηCap
  obtain ⟨η, hωGη, hωRη, hη⟩ :=
    Filter.Eventually.exists (hωGSmall.and (hωRSmall.and hηCapMem))
  have hηTailMem : η ∈ Set.Ioc 0 ηTail := by
    refine ⟨hη.1, hη.2.trans ?_⟩
    dsimp only [ηCap]
    exact min_le_left _ _
  have hηPhaseMem : η ∈ Set.Ioc 0 ηPhase := by
    refine ⟨hη.1, hη.2.trans ?_⟩
    dsimp only [ηCap]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hηAmpLe : η ≤ ηAmp := by
    refine hη.2.trans ?_
    dsimp only [ηCap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hηRadiusLe : η ≤ ηRadius := by
    refine hη.2.trans ?_
    dsimp only [ηCap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηGraphLe : η ≤ ηGraph := by
    refine hη.2.trans ?_
    dsimp only [ηCap]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  let radiusCap := a / (8 * cRadiusUpper)
  have hRadiusCap : 0 < radiusCap := by
    dsimp only [radiusCap]
    positivity
  let εbar := min η radiusCap
  have hεbarPos : 0 < εbar := lt_min hη.1 hRadiusCap
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt (hηTailMem.2.trans_lt hηTail.2)
  let cSupport := a / 4
  have hcSupport : 0 < cSupport := by
    dsimp only [cSupport]
    positivity
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, cSupport, hcSupport, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεη : ε₀ ∈ Set.Ioc 0 η := by
    refine ⟨hε₀.1, hε₀.2.trans ?_⟩
    dsimp only [εbar]
    exact min_le_left _ _
  have hεAmp : ε₀ ∈ Set.Ioc 0 ηAmp :=
    ⟨hε₀.1, hεη.2.trans hηAmpLe⟩
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hεη.2.trans hηRadiusLe⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hεη.2.trans hηGraphLe⟩
  have hεRadiusCap : ε₀ ≤ radiusCap := by
    refine hε₀.2.trans ?_
    dsimp only [εbar]
    exact min_le_right _ _
  obtain ⟨GlimBounded, hGlimBounded, hGlimBoundedTendsto, hAmplitudeBounds⟩ :=
    hAmp ε₀ hεAmp
  intro Clim hClim Glim hGlim hGlimTendsto
  have hGlimEq : GlimBounded = Glim :=
    tendsto_nhds_unique hGlimBoundedTendsto hGlimTendsto
  have hGminGlim : Gmin ≤ Glim := by
    rw [← hGlimEq]
    exact hGlimBounded.1
  have hTailData := hTail η hηTailMem ε₀ hεη Glim hGlim hGlimTendsto
  have hPhaseData := hPhase η hηPhaseMem ε₀ hεη Clim hClim
  have hRadiusData := hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto
  have hωGNonneg : 0 ≤ ωG η := hωGSpec.1 η hηTailMem
  have hωRNonneg : 0 ≤ ωR η := hωRSpec.1 η hηPhaseMem
  have hcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates
      curve.shape curve.high ε₀ j
    have hc' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀) := by
      simpa only [orbit] using hc
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using congrArg Prod.fst hc'
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    obtain ⟨_, hs⟩ := hGraph ε₀ hεGraph j
    rw [hcoord j]
    exact hs
  have hEndpointStructured (j : ℕ) (σ : Fin 2) :
      (a / 2) * (orbit.state j).ε ≤
        Metric.infDist (orbit.endpoint (2 * j + σ.val))
          (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
    let e := (orbit.state j).ε
    have hePos : 0 < e := (hscale j).1
    have heLeOne : e ≤ 1 := by
      exact (hscale j).2.trans
        (hε₀.2.trans (hεbarLt.le.trans (by norm_num)))
    have heSq : e ^ 2 ≤ e := by
      nlinarith [mul_nonneg hePos.le (sub_nonneg.mpr heLeOne)]
    have htail := hTailData j
    have hphase := hPhaseData j σ
    have htailLower := (abs_le.mp htail).1
    have hphaseLower := (abs_le.mp hphase).1
    have hcoeff : a ≤ (13 / 3 : ℝ) * Glim := by
      dsimp only [a]
      exact mul_le_mul_of_nonneg_left hGminGlim (by norm_num)
    have hlead : a * e ≤ (13 / 3 : ℝ) * Glim * e :=
      mul_le_mul_of_nonneg_right hcoeff hePos.le
    have hErrG : ωG η * e < (a / 4) * e :=
      mul_lt_mul_of_pos_right hωGη hePos
    have hErrRLe : ωR η * e ^ 2 ≤ ωR η * e :=
      mul_le_mul_of_nonneg_left heSq hωRNonneg
    have hErrR : ωR η * e < (a / 4) * e :=
      mul_lt_mul_of_pos_right hωRη hePos
    have hlinear : (a / 2) * e ≤
        ‖orbit.endpoint (2 * j + σ.val) - Clim‖ - Glim := by
      dsimp only [e] at htailLower hphaseLower hlead hErrG hErrRLe hErrR ⊢
      nlinarith
    rw [DFP.TwoPhaseOrbit.infDist_limitCircle Clim Glim hGlim]
    exact hlinear.trans (le_abs_self _)
  have hEndpointLinear (k : ℕ) :
      (a / 2) * (orbit.state (k / 2)).ε ≤
        Metric.infDist (orbit.endpoint k)
          (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · simpa using hEndpointStructured j (0 : Fin 2)
    · have hhalf : (2 * j + 1) / 2 = j := by
        simpa using Nat.mul_add_div (m := 2) (by norm_num) j 1
      rw [hhalf]
      simpa using hEndpointStructured j (1 : Fin 2)
  intro support hsupport k z hz
  let e := (orbit.state (k / 2)).ε
  let ρ := orbit.interpolationRadius Clim Glim k
  have hePos : 0 < e := by
    simpa only [e] using (hscale (k / 2)).1
  have heCap : e ≤ radiusCap :=
    (hscale (k / 2)).2.trans hεRadiusCap
  have hρBounds : ρ ∈ Set.Icc
      (cRadiusLower * e ^ 2) (cRadiusUpper * e ^ 2) := by
    simpa only [ρ, e, DFP.TwoPhaseOrbit.endpointRadius_def] using hRadiusData k
  have hρSmall : ρ ≤ (a / 8) * e := by
    calc
      ρ ≤ cRadiusUpper * e ^ 2 := hρBounds.2
      _ = (cRadiusUpper * e) * e := by ring
      _ ≤ (cRadiusUpper * e) * radiusCap := by
        exact mul_le_mul_of_nonneg_left heCap
          (mul_nonneg hcRadiusUpper.le hePos.le)
      _ = (a / 8) * e := by
        dsimp only [radiusCap]
        field_simp [hcRadiusUpper.ne']
  have hzDist : dist z (orbit.endpoint k) ≤ ρ := by
    simpa only [Metric.mem_closedBall] using hsupport k hz
  have htriangle : Metric.infDist (orbit.endpoint k)
      (DFP.TwoPhaseOrbit.limitCircle Clim Glim) ≤
        Metric.infDist z (DFP.TwoPhaseOrbit.limitCircle Clim Glim) +
          dist z (orbit.endpoint k) := by
    simpa only [dist_comm] using
      (Metric.infDist_le_infDist_add_dist
        (s := DFP.TwoPhaseOrbit.limitCircle Clim Glim)
        (x := orbit.endpoint k) (y := z))
  have hEndpoint := hEndpointLinear k
  change a / 4 * e ≤
    Metric.infDist z (DFP.TwoPhaseOrbit.limitCircle Clim Glim)
  have hsmall : a / 8 * e ≤ a / 4 * e := by
    nlinarith [mul_pos ha hePos]
  have hdistQuarter : dist z (orbit.endpoint k) ≤ a / 4 * e :=
    hzDist.trans (hρSmall.trans hsmall)
  have hEndpoint' : a / 2 * e ≤
      Metric.infDist (orbit.endpoint k)
        (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
    simpa only [e] using hEndpoint
  calc
    a / 4 * e = a / 2 * e - a / 4 * e := by ring
    _ ≤ Metric.infDist (orbit.endpoint k)
          (DFP.TwoPhaseOrbit.limitCircle Clim Glim) - dist z (orbit.endpoint k) :=
      sub_le_sub hEndpoint' hdistQuarter
    _ ≤ Metric.infDist z (DFP.TwoPhaseOrbit.limitCircle Clim Glim) :=
      sub_le_iff_le_add.mpr htriangle

/-- Compatibility certificate combining the pure support-distance lower bound
with the scale interval and interpolation-radius positivity used by downstream
decay estimates. -/
theorem supportInfDistLinearLower (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cSupport > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                (∀ j : ℕ, (orbit.state j).ε ∈ Set.Ioc 0 ε₀) ∧
                  (∀ k : ℕ, 0 < orbit.interpolationRadius Clim Glim k) ∧
                    ∀ support : ℕ → Set (EuclideanSpace ℝ (Fin 2)),
                      (∀ k, support k ⊆ Metric.closedBall (orbit.endpoint k)
                        (orbit.interpolationRadius Clim Glim k)) →
                        ∀ k : ℕ, ∀ z ∈ support k,
                          cSupport * (orbit.state (k / 2)).ε ≤
                            Metric.infDist z
                              (DFP.TwoPhaseOrbit.limitCircle Clim Glim) := by
  obtain ⟨ηLower, hηLower, cSupport, hcSupport, hLower⟩ :=
    curve.supportInfDistLinearLowerBound
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  obtain ⟨ηRadius, hηRadius, hRadius⟩ := curve.interpolationRadius_pos
  let εbar := min ηLower (min ηGraph ηRadius)
  have hεbarPos : 0 < εbar :=
    lt_min hηLower.1 (lt_min hηGraph.1 hηRadius.1)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηLower.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, cSupport, hcSupport, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hεLower : ε₀ ∈ Set.Ioc 0 ηLower :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεRadius : ε₀ ∈ Set.Ioc 0 ηRadius :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  intro Clim hClim Glim hGlim hGlimTendsto
  have hLowerData :=
    hLower ε₀ hεLower Clim hClim Glim hGlim hGlimTendsto
  have hRadiusData :=
    hRadius ε₀ hεRadius Clim hClim Glim hGlim hGlimTendsto
  have hcoord (j : ℕ) :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1 := by
    have hraw := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates
      curve.shape curve.high ε₀ j
    have hraw' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀) := by
      simpa only [orbit] using hraw
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hraw'
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    obtain ⟨_, hs⟩ := hGraph ε₀ hεGraph j
    rw [hcoord j]
    exact hs
  exact ⟨hscale, hRadiusData, hLowerData⟩

end DFP.TwoLeg.SlowCurve
