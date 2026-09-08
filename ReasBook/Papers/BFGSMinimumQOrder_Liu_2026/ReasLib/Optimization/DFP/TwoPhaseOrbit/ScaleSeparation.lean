module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeTailUniform
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds

public section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- Chronologically ordered endpoints on sufficiently small invariant slow-curve orbits
with a fixed scale gap have a uniform first-order radial separation. -/
theorem slowCurveDifferentScaleRadialGap (p h : ℝ → ℝ)
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
    (κ : ℝ) (hκ : κ ∈ Set.Ioo (1 / Real.sqrt 2) 1) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cε > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun i : ℕ ↦ (orbit.state i).amplitude) atTop (𝓝 Glim) →
                ∀ j ℓ : ℕ, ∀ σ τ : Fin 2,
                  2 * j + σ.val < 2 * ℓ + τ.val →
                    (orbit.state ℓ).ε ≤ κ * (orbit.state j).ε →
                      cε * (orbit.state j).ε ≤
                        |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
                          ‖orbit.endpoint (2 * ℓ + τ.val) - Clim‖| := by
  obtain ⟨ηG, hηG, ωG, hωGSpec, hG⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeTailUniform
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηR, hηR, ωR, hωRSpec, hR⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorUniform
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηA, hηA, Gmin, hGmin, Gmax, hGminMax, hA⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let m : ℝ := (13 / 3) * Gmin * (1 - κ)
  have hthirteen : 0 < (13 / 3 : ℝ) := by norm_num
  have hsixteen : 0 < (16 : ℝ) := by norm_num
  have hm : 0 < m := by
    dsimp only [m]
    exact mul_pos (mul_pos hthirteen hGmin) (sub_pos.mpr hκ.2)
  let δ : ℝ := m / 16
  have hδ : 0 < δ := div_pos hm hsixteen
  have hGSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωG η < δ :=
    (tendsto_order.1 hωGSpec.2.2).2 δ hδ
  have hRSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωR η < δ :=
    (tendsto_order.1 hωRSpec.2.2).2 δ hδ
  let ηCap := min (min ηG ηR) (min ηA ηGraph)
  have hηCap : 0 < ηCap := by
    dsimp only [ηCap]
    exact lt_min (lt_min hηG.1 hηR.1) (lt_min hηA.1 hηGraph.1)
  have hCapMem : Set.Ioc (0 : ℝ) ηCap ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT hηCap
  have hChoice : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      ωG η < δ ∧ ωR η < δ ∧ η ∈ Set.Ioc 0 ηCap := by
    filter_upwards [hGSmall, hRSmall, hCapMem] with η hηGSmall hηRSmall hηCapMem
    exact ⟨hηGSmall, hηRSmall, hηCapMem⟩
  obtain ⟨εbar, hωGSmall, hωRSmall, hεbarCap⟩ := Filter.Eventually.exists hChoice
  have hCapG : ηCap ≤ ηG := by
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hCapR : ηCap ≤ ηR := by
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hCapA : ηCap ≤ ηA := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hCapGraph : ηCap ≤ ηGraph := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hεbarG : εbar ∈ Set.Ioc 0 ηG :=
    ⟨hεbarCap.1, hεbarCap.2.trans hCapG⟩
  have hεbarR : εbar ∈ Set.Ioc 0 ηR :=
    ⟨hεbarCap.1, hεbarCap.2.trans hCapR⟩
  have hεbarA : εbar ∈ Set.Ioc 0 ηA :=
    ⟨hεbarCap.1, hεbarCap.2.trans hCapA⟩
  have hεbarGraph : εbar ∈ Set.Ioc 0 ηGraph :=
    ⟨hεbarCap.1, hεbarCap.2.trans hCapGraph⟩
  have hεbarLt : εbar < (1 / 4 : ℝ) := hεbarG.2.trans_lt hηG.2
  let cε : ℝ := m / 2
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hcε : 0 < cε := div_pos hm htwo
  refine ⟨εbar, ⟨hεbarCap.1, hεbarLt⟩, cε, hcε, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀G : ε₀ ∈ Set.Ioc 0 εbar := hε₀
  have hε₀A : ε₀ ∈ Set.Ioc 0 ηA :=
    ⟨hε₀.1, hε₀.2.trans hεbarA.2⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans hεbarGraph.2⟩
  obtain ⟨GlimBounded, hGlimBounded, hGlimBoundedTendsto, hAmplitudeBounds⟩ :=
    hA ε₀ hε₀A
  intro Clim hClim Glim hGlim hGlimTendsto j ℓ σ τ _ hScaleGap
  have hGlimEq : GlimBounded = Glim :=
    tendsto_nhds_unique hGlimBoundedTendsto hGlimTendsto
  have hGminGlim : Gmin ≤ Glim := by
    rw [← hGlimEq]
    exact hGlimBounded.1
  have hεeq (n : ℕ) :
      (orbit.state n).ε =
        (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ n
    have hfst := congrArg Prod.fst hcoord
    simpa [orbit, DFP.TwoPhaseOrbit.State.coordinates_def] using hfst
  have hεjPos : 0 < (orbit.state j).ε := by
    rw [hεeq j]
    exact (hGraph ε₀ hε₀Graph j).2.1
  have hεℓPos : 0 < (orbit.state ℓ).ε := by
    rw [hεeq ℓ]
    exact (hGraph ε₀ hε₀Graph ℓ).2.1
  have hεjLeBar : (orbit.state j).ε ≤ εbar := by
    rw [hεeq j]
    exact (hGraph ε₀ hε₀Graph j).2.2.trans hε₀.2
  have hεℓLeJ : (orbit.state ℓ).ε ≤ (orbit.state j).ε := by
    calc
      (orbit.state ℓ).ε ≤ κ * (orbit.state j).ε := hScaleGap
      _ ≤ 1 * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_right hκ.2.le hεjPos.le
      _ = (orbit.state j).ε := one_mul _
  have hεjLeOne : (orbit.state j).ε ≤ 1 := by
    have hquarter : (1 / 4 : ℝ) ≤ 1 := by norm_num
    exact hεjLeBar.trans (hεbarLt.le.trans hquarter)
  have hεℓLeOne : (orbit.state ℓ).ε ≤ 1 := hεℓLeJ.trans hεjLeOne
  have hScaleDiff :
      (1 - κ) * (orbit.state j).ε ≤
        (orbit.state j).ε - (orbit.state ℓ).ε := by
    linarith
  have hCoeff : (13 / 3 : ℝ) * Gmin ≤ (13 / 3 : ℝ) * Glim :=
    mul_le_mul_of_nonneg_left hGminGlim hthirteen.le
  have hMain :
      m * (orbit.state j).ε ≤
        (13 / 3 : ℝ) * Glim *
          ((orbit.state j).ε - (orbit.state ℓ).ε) := by
    calc
      m * (orbit.state j).ε =
          ((13 / 3 : ℝ) * Gmin) * ((1 - κ) * (orbit.state j).ε) := by
            dsimp only [m]
            ring
      _ ≤ ((13 / 3 : ℝ) * Glim) * ((1 - κ) * (orbit.state j).ε) :=
        mul_le_mul_of_nonneg_right hCoeff
          (mul_nonneg (sub_pos.mpr hκ.2).le hεjPos.le)
      _ ≤ ((13 / 3 : ℝ) * Glim) *
          ((orbit.state j).ε - (orbit.state ℓ).ε) :=
        mul_le_mul_of_nonneg_left hScaleDiff
          (mul_nonneg hthirteen.le hGlim.le)
  have hωGNonneg : 0 ≤ ωG εbar := hωGSpec.1 εbar hεbarG
  have hωRNonneg : 0 ≤ ωR εbar := hωRSpec.1 εbar hεbarR
  have hAmpJRaw := hG εbar hεbarG ε₀ hε₀G Glim hGlim hGlimTendsto j
  have hAmpLRaw := hG εbar hεbarG ε₀ hε₀G Glim hGlim hGlimTendsto ℓ
  have hRadJRaw := hR εbar hεbarR ε₀ hε₀G Clim hClim j σ
  have hRadLRaw := hR εbar hεbarR ε₀ hε₀G Clim hClim ℓ τ
  have hAmpJ :
      |(orbit.state j).amplitude - Glim -
          (13 / 3 : ℝ) * Glim * (orbit.state j).ε| ≤
        δ * (orbit.state j).ε := by
    exact hAmpJRaw.trans
      (mul_le_mul_of_nonneg_right hωGSmall.le hεjPos.le)
  have hAmpL :
      |(orbit.state ℓ).amplitude - Glim -
          (13 / 3 : ℝ) * Glim * (orbit.state ℓ).ε| ≤
        δ * (orbit.state j).ε := by
    calc
      |(orbit.state ℓ).amplitude - Glim -
          (13 / 3 : ℝ) * Glim * (orbit.state ℓ).ε| ≤
          ωG εbar * (orbit.state ℓ).ε := hAmpLRaw
      _ ≤ ωG εbar * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_left hεℓLeJ hωGNonneg
      _ ≤ δ * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_right hωGSmall.le hεjPos.le
  have hεjSqLe : (orbit.state j).ε ^ 2 ≤ (orbit.state j).ε := by
    nlinarith
  have hεℓSqLeJ : (orbit.state ℓ).ε ^ 2 ≤ (orbit.state j).ε := by
    have hεℓSqLe : (orbit.state ℓ).ε ^ 2 ≤ (orbit.state ℓ).ε := by
      nlinarith
    exact hεℓSqLe.trans hεℓLeJ
  have hRadJ :
      |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
          (orbit.state j).amplitude| ≤ δ * (orbit.state j).ε := by
    calc
      |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
          (orbit.state j).amplitude| ≤
          ωR εbar * (orbit.state j).ε ^ 2 := hRadJRaw
      _ ≤ ωR εbar * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_left hεjSqLe hωRNonneg
      _ ≤ δ * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_right hωRSmall.le hεjPos.le
  have hRadL :
      |‖orbit.endpoint (2 * ℓ + τ.val) - Clim‖ -
          (orbit.state ℓ).amplitude| ≤ δ * (orbit.state j).ε := by
    calc
      |‖orbit.endpoint (2 * ℓ + τ.val) - Clim‖ -
          (orbit.state ℓ).amplitude| ≤
          ωR εbar * (orbit.state ℓ).ε ^ 2 := hRadLRaw
      _ ≤ ωR εbar * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_left hεℓSqLeJ hωRNonneg
      _ ≤ δ * (orbit.state j).ε :=
        mul_le_mul_of_nonneg_right hωRSmall.le hεjPos.le
  have hSigned : cε * (orbit.state j).ε ≤
      ‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
        ‖orbit.endpoint (2 * ℓ + τ.val) - Clim‖ := by
    have hAmpJBounds := abs_le.mp hAmpJ
    have hAmpLBounds := abs_le.mp hAmpL
    have hRadJBounds := abs_le.mp hRadJ
    have hRadLBounds := abs_le.mp hRadL
    dsimp only [cε, δ] at *
    nlinarith
  exact hSigned.trans (le_abs_self _)

/-- Chronologically ordered endpoints on sufficiently small invariant slow-curve orbits
with a fixed scale gap are separated in endpoint distance at squared-scale order. -/
theorem slowCurveDifferentScaleEndpointSeparation (p h : ℝ → ℝ)
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
    (κ : ℝ) (hκ : κ ∈ Set.Ioo (1 / Real.sqrt 2) 1) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ c > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun i : ℕ ↦ (orbit.state i).amplitude) atTop (𝓝 Glim) →
                ∀ j ℓ : ℕ, ∀ σ τ : Fin 2,
                  2 * j + σ.val < 2 * ℓ + τ.val →
                    (orbit.state ℓ).ε ≤ κ * (orbit.state j).ε →
                      c * (orbit.state j).ε ^ 2 ≤
                        dist (orbit.endpoint (2 * j + σ.val))
                          (orbit.endpoint (2 * ℓ + τ.val)) := by
  obtain ⟨ηRad, hηRad, c, hc, hRad⟩ :=
    slowCurveDifferentScaleRadialGap p h h_invariant h_pJet h_hJet κ hκ
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min ηRad ηGraph
  have hεbarPos : 0 < εbar := lt_min hηRad.1 hηGraph.1
  have hεbarLt : εbar < (1 / 4 : ℝ) := (min_le_left _ _).trans_lt hηRad.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, c, hc, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hε₀Rad : ε₀ ∈ Set.Ioc 0 ηRad :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  intro Clim hClim Glim hGlim hGlimTendsto j ℓ σ τ hOrder hScaleGap
  have hGap := hRad ε₀ hε₀Rad Clim hClim Glim hGlim hGlimTendsto
    j ℓ σ τ hOrder hScaleGap
  have hεeq :
      (orbit.state j).ε =
        (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hfst := congrArg Prod.fst hcoord
    simpa [orbit, DFP.TwoPhaseOrbit.State.coordinates_def] using hfst
  have hεjPos : 0 < (orbit.state j).ε := by
    rw [hεeq]
    exact (hGraph ε₀ hε₀Graph j).2.1
  have hεjLeOne : (orbit.state j).ε ≤ 1 := by
    rw [hεeq]
    have hquarter : (1 / 4 : ℝ) ≤ 1 := by norm_num
    exact ((hGraph ε₀ hε₀Graph j).2.2.trans hε₀.2).trans
      (hεbarLt.le.trans hquarter)
  have hSq : (orbit.state j).ε ^ 2 ≤ (orbit.state j).ε := by
    nlinarith
  have hScaled : c * (orbit.state j).ε ^ 2 ≤ c * (orbit.state j).ε :=
    mul_le_mul_of_nonneg_left hSq hc.le
  have hReverse :
      |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
          ‖orbit.endpoint (2 * ℓ + τ.val) - Clim‖| ≤
        dist (orbit.endpoint (2 * j + σ.val))
          (orbit.endpoint (2 * ℓ + τ.val)) := by
    calc
      |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
          ‖orbit.endpoint (2 * ℓ + τ.val) - Clim‖| ≤
          ‖(orbit.endpoint (2 * j + σ.val) - Clim) -
            (orbit.endpoint (2 * ℓ + τ.val) - Clim)‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖orbit.endpoint (2 * j + σ.val) -
            orbit.endpoint (2 * ℓ + τ.val)‖ := by
        congr 1
        abel
      _ = dist (orbit.endpoint (2 * j + σ.val))
          (orbit.endpoint (2 * ℓ + τ.val)) := by
        rw [dist_eq_norm]
  exact hScaled.trans (hGap.trans hReverse)

end DFP.TwoPhaseOrbit
