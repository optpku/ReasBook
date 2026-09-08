module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleGap
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngle
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation
public import ReasLib.Geometry.Euclidean.Plane.ComplexPolar

public section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- Comparable slow-curve endpoints with a definite principal angular gap have a
uniform separation proportional to the square of the earlier endpoint scale. -/
theorem slowCurveAngularGapEndpointSeparation (p h : ℝ → ℝ)
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
    (κ : ℝ) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ c > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun i : ℕ ↦ (orbit.state i).amplitude) atTop (𝓝 Glim) →
                ∀ j ℓ : ℕ, ∀ σ τ : Fin 2,
                  2 * j + σ.val < 2 * ℓ + τ.val →
                    κ * (orbit.state j).ε < (orbit.state ℓ).ε →
                      (orbit.state j).ε ^ 2 / 4 ≤
                          |(orbit.endpointPolarAngle Clim (2 * j + σ.val) -
                            orbit.endpointPolarAngle Clim (2 * ℓ + τ.val)).toReal| →
                        c * (orbit.state j).ε ^ 2 ≤
                          dist (orbit.endpoint (2 * j + σ.val))
                            (orbit.endpoint (2 * ℓ + τ.val)) := by
  obtain ⟨ηA, hηA, Gmin, hGmin, Gmax, hGminMax, hA⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηR, hηR, ωR, hωRSpec, hR⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorUniform
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let ηCap := min ηR (min (1 / 4 : ℝ) (Real.sqrt (Gmin / 2)))
  have hηCap : 0 < ηCap := by
    dsimp only [ηCap]
    have hsqrt : 0 < Real.sqrt (Gmin / 2) := by positivity
    exact lt_min hηR.1 (lt_min (by norm_num) hsqrt)
  have hωSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωR η < 1 := by
    exact (tendsto_order.1 hωRSpec.2.2).2 1 (by norm_num)
  have hηCapMem : Set.Ioc (0 : ℝ) ηCap ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT hηCap
  obtain ⟨ηω, hωηω, hηω⟩ :=
    Filter.Eventually.exists (hωSmall.and hηCapMem)
  let εbar := min (min ηA ηω) ηGraph
  have hεbarPos : 0 < εbar := lt_min (lt_min hηA.1 hηω.1) hηGraph.1
  have hεbarLt : εbar < (1 / 4 : ℝ) := by
    have hηωLt : ηω < (1 / 4 : ℝ) :=
      (hηω.2.trans (min_le_left _ _)).trans_lt hηR.2
    calc
      εbar ≤ min ηA ηω := min_le_left _ _
      _ ≤ ηω := min_le_right _ _
      _ < (1 / 4 : ℝ) := hηωLt
  let c := Gmin / (4 * Real.pi)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, c, hc, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεbarLeA : εbar ≤ ηA := (min_le_left _ _).trans (min_le_left _ _)
  have hεbarLeω : εbar ≤ ηω := (min_le_left _ _).trans (min_le_right _ _)
  have hεA : ε₀ ∈ Set.Ioc 0 ηA :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeA⟩
  have hεω : ε₀ ∈ Set.Ioc 0 ηω :=
    ⟨hε₀.1, hε₀.2.trans hεbarLeω⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  obtain ⟨GlimBounded, hGlimBounded, hGlimBoundedTendsto, hAmplitudeBounds⟩ :=
    hA ε₀ hεA
  intro Clim hClim Glim hGlim hGlimTendsto j ℓ σ τ hidx hscale hangle
  have hGlimEq : GlimBounded = Glim :=
    tendsto_nhds_unique hGlimBoundedTendsto hGlimTendsto
  have hGminGlim : Gmin ≤ Glim := by
    rw [← hGlimEq]
    exact hGlimBounded.1
  have hηωLeR : ηω ≤ ηR := hηω.2.trans (min_le_left _ _)
  have hεR : ε₀ ∈ Set.Ioc 0 ηR :=
    ⟨hε₀.1, (hε₀.2.trans hεbarLeω).trans hηωLeR⟩
  have hεcoord (n : ℕ) :
      (orbit.state n).ε =
        (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := by
    have hc' := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ n
    simpa only [orbit, DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hc'
  have hscalePos (n : ℕ) : 0 < (orbit.state n).ε := by
    rw [hεcoord n]
    exact (hGraph ε₀ hεGraph n).2.1
  have hscaleLe (n : ℕ) : (orbit.state n).ε ≤ ε₀ := by
    rw [hεcoord n]
    exact (hGraph ε₀ hεGraph n).2.2
  have hradialBound (n : ℕ) (q : Fin 2) :
      |‖orbit.endpoint (2 * n + q.val) - Clim‖ -
          (orbit.state n).amplitude| ≤ Gmin / 2 := by
    have hηωR : ηω ∈ Set.Ioc 0 ηR := ⟨hηω.1, hηωLeR⟩
    have hr := hR ηω hηωR ε₀ hεω Clim hClim n q
    have hsq : (orbit.state n).ε ^ 2 ≤ Gmin / 2 := by
      have hηωSqrt : ηω ≤ Real.sqrt (Gmin / 2) :=
        hηω.2.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hle : (orbit.state n).ε ≤ Real.sqrt (Gmin / 2) :=
        (hscaleLe n).trans ((hε₀.2.trans hεbarLeω).trans hηωSqrt)
      have hsquare : (orbit.state n).ε ^ 2 ≤ (Real.sqrt (Gmin / 2)) ^ 2 := by
        nlinarith [hscalePos n]
      calc
        (orbit.state n).ε ^ 2 ≤ (Real.sqrt (Gmin / 2)) ^ 2 := hsquare
        _ = Gmin / 2 := Real.sq_sqrt (by positivity)
    have hprod : ωR ηω * (orbit.state n).ε ^ 2 ≤ Gmin / 2 := by
      calc
        ωR ηω * (orbit.state n).ε ^ 2 ≤ 1 * (orbit.state n).ε ^ 2 :=
          mul_le_mul_of_nonneg_right (le_of_lt hωηω) (sq_nonneg _)
        _ ≤ Gmin / 2 := by simpa only [one_mul] using hsq
    exact hr.trans hprod
  have hpolarLower (n : ℕ) (q : Fin 2) :
      Gmin / 2 ≤ ‖orbit.endpoint (2 * n + q.val) - Clim‖ := by
    have hamp : (orbit.state n).amplitude ∈ Set.Icc Gmin Gmax := by
      simpa only [orbit] using hAmplitudeBounds n
    have hr := abs_le.mp (hradialBound n q)
    linarith [hamp.1]
  have hne (n : ℕ) (q : Fin 2) :
      orbit.endpoint (2 * n + q.val) - Clim ≠ 0 := by
    intro hz
    have hp := hpolarLower n q
    rw [hz] at hp
    simp at hp
    linarith
  have hrep (n : ℕ) (q : Fin 2) :
      orbit.endpoint (2 * n + q.val) - Clim =
        ‖orbit.endpoint (2 * n + q.val) - Clim‖ •
          EuclideanPlane.rotation
            (orbit.endpointPolarAngle Clim (2 * n + q.val))
            (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
    exact orbit.endpointPolarAngle_spec Clim (2 * n + q.val) (hne n q)
  have hrot (n : ℕ) (q : Fin 2) :
      EuclideanPlane.rotation
          ((orbit.endpointPolarAngle Clim (2 * n + q.val)).toReal : Real.Angle) =
        EuclideanPlane.rotation
          (orbit.endpointPolarAngle Clim (2 * n + q.val)) := by
    rw [Real.Angle.coe_toReal]
  have hrep' (n : ℕ) (q : Fin 2) :
      orbit.endpoint (2 * n + q.val) - Clim =
        ‖orbit.endpoint (2 * n + q.val) - Clim‖ •
          EuclideanPlane.rotation
            ((orbit.endpointPolarAngle Clim (2 * n + q.val)).toReal : Real.Angle)
            (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
    rw [hrot n q]
    exact hrep n q
  have hz (n : ℕ) (q : Fin 2) :
      dist (orbit.endpoint (2 * n + q.val) - Clim)
          (‖orbit.endpoint (2 * n + q.val) - Clim‖ •
            EuclideanPlane.rotation
              ((orbit.endpointPolarAngle Clim (2 * n + q.val)).toReal : Real.Angle)
              (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ 0 := by
    rw [← hrep' n q]
    simp
  have hpolar := EuclideanPlane.polarDistance_ge_max_principal_sub_errors
    (c := Clim) (z₁ := orbit.endpoint (2 * j + σ.val))
    (z₂ := orbit.endpoint (2 * ℓ + τ.val)) (rMin := Gmin / 2)
    (r₁ := ‖orbit.endpoint (2 * j + σ.val) - Clim‖)
    (r₂ := ‖orbit.endpoint (2 * ℓ + τ.val) - Clim‖)
    (θ₁ := (orbit.endpointPolarAngle Clim (2 * j + σ.val)).toReal)
    (θ₂ := (orbit.endpointPolarAngle Clim (2 * ℓ + τ.val)).toReal)
    (hrMin := by positivity) (hr₁ := hpolarLower j σ) (hr₂ := hpolarLower ℓ τ)
    (e₁ := 0) (e₂ := 0) (hz₁ := hz j σ) (hz₂ := hz ℓ τ)
  have hangle' :
      2 * (Gmin / 2) / Real.pi *
          |(orbit.endpointPolarAngle Clim (2 * j + σ.val) -
            orbit.endpointPolarAngle Clim (2 * ℓ + τ.val)).toReal| ≤
        dist (orbit.endpoint (2 * j + σ.val))
          (orbit.endpoint (2 * ℓ + τ.val)) := by
    have hpolar0 :
        max |‖orbit.endpoint (2 * j + σ.val) - Clim‖ -
              ‖orbit.endpoint (2 * ℓ + τ.val) - Clim‖|
            (2 * (Gmin / 2) / Real.pi *
              |(((orbit.endpointPolarAngle Clim (2 * j + σ.val)).toReal -
                  (orbit.endpointPolarAngle Clim (2 * ℓ + τ.val)).toReal : ℝ) :
                Real.Angle).toReal|) ≤
          dist (orbit.endpoint (2 * j + σ.val))
            (orbit.endpoint (2 * ℓ + τ.val)) := by
      simpa only [sub_zero] using hpolar
    have hpolar' := le_trans (le_max_right _ _) hpolar0
    simpa only [Real.Angle.coe_sub, Real.Angle.coe_toReal] using hpolar'
  have hmain : c * (orbit.state j).ε ^ 2 ≤
      2 * (Gmin / 2) / Real.pi *
        |(orbit.endpointPolarAngle Clim (2 * j + σ.val) -
          orbit.endpointPolarAngle Clim (2 * ℓ + τ.val)).toReal| := by
    have hmul := mul_le_mul_of_nonneg_left hangle
      (div_nonneg (le_of_lt hGmin) (le_of_lt Real.pi_pos))
    calc
      c * (orbit.state j).ε ^ 2 =
          (Gmin / Real.pi) * ((orbit.state j).ε ^ 2 / 4) := by
            dsimp only [c]
            ring
      _ ≤ (Gmin / Real.pi) *
          |(orbit.endpointPolarAngle Clim (2 * j + σ.val) -
            orbit.endpointPolarAngle Clim (2 * ℓ + τ.val)).toReal| := hmul
      _ = 2 * (Gmin / 2) / Real.pi *
          |(orbit.endpointPolarAngle Clim (2 * j + σ.val) -
            orbit.endpointPolarAngle Clim (2 * ℓ + τ.val)).toReal| := by ring
  exact hmain.trans hangle'

/-- Consecutive slow-curve endpoints have a uniform separation proportional to the
square of the scale of the cycle containing the earlier endpoint. -/
theorem slowCurveAdjacentEndpointSeparation (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cAdj > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun k : ℕ ↦ (orbit.state k).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun k : ℕ ↦ (orbit.state k).amplitude) atTop (𝓝 Glim) →
                ∀ j : ℕ, ∀ i : Fin 2,
                    cAdj * (orbit.state j).ε ^ 2 ≤
                    dist (orbit.endpoint (2 * j + i.val))
                      (orbit.endpoint (2 * j + i.val + 1)) := by
  obtain ⟨ηA, hηA, Gmin, hGmin, Gmax, hGminMax, hA⟩ :=
    DFP.TwoPhaseOrbit.slowCurveAmplitudeUniformBounds
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηR, hηR, ωR, hωRSpec, hR⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePhaseRadiusErrorUniform
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηGap, hηGap, hGap⟩ :=
    DFP.TwoPhaseOrbit.slowCurveEndpointPolarAngleGapLowerBound
      p h h_invariant h_pJet h_hJet
  let ηCap := min ηR (min (1 / 4 : ℝ) (Real.sqrt (Gmin / 2)))
  have hηCap : 0 < ηCap := by
    dsimp only [ηCap]
    have hsqrt : 0 < Real.sqrt (Gmin / 2) := by positivity
    exact lt_min hηR.1 (lt_min (by norm_num) hsqrt)
  have hωSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωR η < 1 := by
    exact (tendsto_order.1 hωRSpec.2.2).2 1 (by norm_num)
  have hηCapMem : Set.Ioc (0 : ℝ) ηCap ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT hηCap
  obtain ⟨ηω, hωηω, hηω⟩ :=
    Filter.Eventually.exists (hωSmall.and hηCapMem)
  let εbar := min (min (min ηA ηω) ηGraph) ηGap
  have hεbarPos : 0 < εbar :=
    lt_min (lt_min (lt_min hηA.1 hηω.1) hηGraph.1) hηGap.1
  have hεbarLt : εbar < (1 / 4 : ℝ) := by
    have hηωLt : ηω < (1 / 4 : ℝ) :=
      (hηω.2.trans (min_le_left _ _)).trans_lt hηR.2
    calc
      εbar ≤ min (min (min ηA ηω) ηGraph) ηGap := le_rfl
      _ ≤ min (min ηA ηω) ηGraph := min_le_left _ _
      _ ≤ min ηA ηω := min_le_left _ _
      _ ≤ ηω := min_le_right _ _
      _ < (1 / 4 : ℝ) := hηωLt
  let cAdj := Gmin / (4 * Real.pi)
  have hcAdj : 0 < cAdj := by
    dsimp only [cAdj]
    positivity
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, cAdj, hcAdj, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεbarLeA : εbar ≤ ηA := by
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεbarLeω : εbar ≤ ηω := by
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεA : ε₀ ∈ Set.Ioc 0 ηA := ⟨hε₀.1, hε₀.2.trans hεbarLeA⟩
  have hεω : ε₀ ∈ Set.Ioc 0 ηω := ⟨hε₀.1, hε₀.2.trans hεbarLeω⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hεGap : ε₀ ∈ Set.Ioc 0 ηGap :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  obtain ⟨GlimBounded, hGlimBounded, hGlimBoundedTendsto, hAmplitudeBounds⟩ :=
    hA ε₀ hεA
  intro Clim hClim Glim hGlim hGlimTendsto j i
  have hGlimEq : GlimBounded = Glim :=
    tendsto_nhds_unique hGlimBoundedTendsto hGlimTendsto
  have hεcoord (n : ℕ) :
      (orbit.state n).ε =
        (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := by
    have hc' := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ n
    simpa only [orbit, DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hc'
  have hηωLeR : ηω ≤ ηR := hηω.2.trans (min_le_left _ _)
  have hηωR : ηω ∈ Set.Ioc 0 ηR := ⟨hηω.1, hηωLeR⟩
  have hscalePos (n : ℕ) : 0 < (orbit.state n).ε := by
    rw [hεcoord n]
    exact (hGraph ε₀ hεGraph n).2.1
  have hscaleLe (n : ℕ) : (orbit.state n).ε ≤ ε₀ := by
    rw [hεcoord n]
    exact (hGraph ε₀ hεGraph n).2.2
  have hradialBound (n : ℕ) (q : Fin 2) :
      |‖orbit.endpoint (2 * n + q.val) - Clim‖ -
          (orbit.state n).amplitude| ≤ Gmin / 2 := by
    have hr := hR ηω hηωR ε₀ hεω Clim hClim n q
    have hsq : (orbit.state n).ε ^ 2 ≤ Gmin / 2 := by
      have hηωSqrt : ηω ≤ Real.sqrt (Gmin / 2) :=
        hηω.2.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hle : (orbit.state n).ε ≤ Real.sqrt (Gmin / 2) :=
        (hscaleLe n).trans ((hε₀.2.trans hεbarLeω).trans hηωSqrt)
      have hsquare : (orbit.state n).ε ^ 2 ≤ (Real.sqrt (Gmin / 2)) ^ 2 := by
        nlinarith [hscalePos n]
      calc
        (orbit.state n).ε ^ 2 ≤ (Real.sqrt (Gmin / 2)) ^ 2 := hsquare
        _ = Gmin / 2 := Real.sq_sqrt (by positivity)
    have hprod : ωR ηω * (orbit.state n).ε ^ 2 ≤ Gmin / 2 := by
      calc
        ωR ηω * (orbit.state n).ε ^ 2 ≤ 1 * (orbit.state n).ε ^ 2 :=
          mul_le_mul_of_nonneg_right (le_of_lt hωηω) (sq_nonneg _)
        _ ≤ Gmin / 2 := by simpa only [one_mul] using hsq
    exact hr.trans hprod
  have hpolarLower (n : ℕ) (q : Fin 2) :
      Gmin / 2 ≤ ‖orbit.endpoint (2 * n + q.val) - Clim‖ := by
    have hamp : (orbit.state n).amplitude ∈ Set.Icc Gmin Gmax := by
      simpa only [orbit] using hAmplitudeBounds n
    have hr := abs_le.mp (hradialBound n q)
    linarith [hamp.1]
  have hne (n : ℕ) (q : Fin 2) :
      orbit.endpoint (2 * n + q.val) - Clim ≠ 0 := by
    intro hz
    have hp := hpolarLower n q
    rw [hz] at hp
    simp at hp
    linarith
  have hrep' (n : ℕ) (q : Fin 2) :
      orbit.endpoint (2 * n + q.val) - Clim =
        ‖orbit.endpoint (2 * n + q.val) - Clim‖ •
          EuclideanPlane.rotation
            ((orbit.endpointPolarAngle Clim (2 * n + q.val)).toReal : Real.Angle)
            (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
    have hr := orbit.endpointPolarAngle_spec Clim (2 * n + q.val) (hne n q)
    simpa only [Real.Angle.coe_toReal] using hr
  have hz (n : ℕ) (q : Fin 2) :
      dist (orbit.endpoint (2 * n + q.val) - Clim)
          (‖orbit.endpoint (2 * n + q.val) - Clim‖ •
            EuclideanPlane.rotation
              ((orbit.endpointPolarAngle Clim (2 * n + q.val)).toReal : Real.Angle)
              (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ 0 := by
    rw [← hrep' n q]
    simp
  have hChord (n m : ℕ) (q r : Fin 2)
      (hangle : (orbit.state j).ε ^ 2 / 4 ≤
        |(orbit.endpointPolarAngle Clim (2 * n + q.val) -
          orbit.endpointPolarAngle Clim (2 * m + r.val)).toReal|) :
      cAdj * (orbit.state j).ε ^ 2 ≤
        dist (orbit.endpoint (2 * n + q.val))
          (orbit.endpoint (2 * m + r.val)) := by
    have hpolar := EuclideanPlane.polarDistance_ge_max_principal_sub_errors
      (c := Clim) (z₁ := orbit.endpoint (2 * n + q.val))
      (z₂ := orbit.endpoint (2 * m + r.val)) (rMin := Gmin / 2)
      (r₁ := ‖orbit.endpoint (2 * n + q.val) - Clim‖)
      (r₂ := ‖orbit.endpoint (2 * m + r.val) - Clim‖)
      (θ₁ := (orbit.endpointPolarAngle Clim (2 * n + q.val)).toReal)
      (θ₂ := (orbit.endpointPolarAngle Clim (2 * m + r.val)).toReal)
      (hrMin := by positivity) (hr₁ := hpolarLower n q) (hr₂ := hpolarLower m r)
      (e₁ := 0) (e₂ := 0) (hz₁ := hz n q) (hz₂ := hz m r)
    have hangle' :
        2 * (Gmin / 2) / Real.pi *
            |(orbit.endpointPolarAngle Clim (2 * n + q.val) -
              orbit.endpointPolarAngle Clim (2 * m + r.val)).toReal| ≤
          dist (orbit.endpoint (2 * n + q.val))
            (orbit.endpoint (2 * m + r.val)) := by
      have hpolar0 :
          max |‖orbit.endpoint (2 * n + q.val) - Clim‖ -
                ‖orbit.endpoint (2 * m + r.val) - Clim‖|
              (2 * (Gmin / 2) / Real.pi *
                |(((orbit.endpointPolarAngle Clim (2 * n + q.val)).toReal -
                    (orbit.endpointPolarAngle Clim (2 * m + r.val)).toReal : ℝ) :
                  Real.Angle).toReal|) ≤
            dist (orbit.endpoint (2 * n + q.val))
              (orbit.endpoint (2 * m + r.val)) := by
        simpa only [sub_zero] using hpolar
      have hpolar' := le_trans (le_max_right _ _) hpolar0
      simpa only [Real.Angle.coe_sub, Real.Angle.coe_toReal] using hpolar'
    have hmul := mul_le_mul_of_nonneg_left hangle
      (div_nonneg (le_of_lt hGmin) (le_of_lt Real.pi_pos))
    calc
      cAdj * (orbit.state j).ε ^ 2 =
          (Gmin / Real.pi) * ((orbit.state j).ε ^ 2 / 4) := by
            dsimp only [cAdj]
            ring
      _ ≤ (Gmin / Real.pi) *
          |(orbit.endpointPolarAngle Clim (2 * n + q.val) -
            orbit.endpointPolarAngle Clim (2 * m + r.val)).toReal| := hmul
      _ = 2 * (Gmin / 2) / Real.pi *
          |(orbit.endpointPolarAngle Clim (2 * n + q.val) -
            orbit.endpointPolarAngle Clim (2 * m + r.val)).toReal| := by ring
      _ ≤ _ := hangle'
  have hgapAngle (n : ℕ) (q : Fin 2) :
      (orbit.state n).ε ^ 2 / 4 ≤
        |(orbit.endpointPolarAngle Clim (2 * n + q.val) -
          orbit.endpointPolarAngle Clim (2 * n + q.val + 1)).toReal| := by
    have hg :
        orbit.endpointPolarAngleLift Clim (2 * n + q.val) -
            orbit.endpointPolarAngleLift Clim (2 * n + q.val + 1) ≥
          (1 / 2 : ℝ) * (orbit.state n).ε ^ 2 := by
      simpa only [orbit] using hGap ε₀ hεGap Clim hClim n q
    have hsub := orbit.endpointPolarAngleLift_succ_sub Clim (2 * n + q.val)
    have habs :
        |(orbit.endpointPolarAngle Clim (2 * n + q.val) -
          orbit.endpointPolarAngle Clim (2 * n + q.val + 1)).toReal| =
          orbit.endpointPolarAngleLift Clim (2 * n + q.val) -
            orbit.endpointPolarAngleLift Clim (2 * n + q.val + 1) := by
      calc
        |(orbit.endpointPolarAngle Clim (2 * n + q.val) -
            orbit.endpointPolarAngle Clim (2 * n + q.val + 1)).toReal| =
            |(orbit.endpointPolarAngle Clim (2 * n + q.val + 1) -
              orbit.endpointPolarAngle Clim (2 * n + q.val)).toReal| := by
                rw [show (orbit.endpointPolarAngle Clim (2 * n + q.val) -
                    orbit.endpointPolarAngle Clim (2 * n + q.val + 1)) =
                    -(orbit.endpointPolarAngle Clim (2 * n + q.val + 1) -
                      orbit.endpointPolarAngle Clim (2 * n + q.val)) by abel,
                  Real.Angle.abs_toReal_neg]
        _ = |-(orbit.endpointPolarAngleLift Clim (2 * n + q.val) -
              orbit.endpointPolarAngleLift Clim (2 * n + q.val + 1))| := by
                rw [← hsub]
                congr 1
                ring
        _ = orbit.endpointPolarAngleLift Clim (2 * n + q.val) -
            orbit.endpointPolarAngleLift Clim (2 * n + q.val + 1) := by
              have hnonneg :
                  0 ≤ orbit.endpointPolarAngleLift Clim (2 * n + q.val) -
                    orbit.endpointPolarAngleLift Clim (2 * n + q.val + 1) := by
                nlinarith [hg, sq_nonneg ((orbit.state n).ε)]
              rw [abs_neg, abs_of_nonneg hnonneg]
    rw [habs]
    nlinarith [hg, sq_nonneg ((orbit.state n).ε)]
  fin_cases i
  · exact hChord j j (0 : Fin 2) (1 : Fin 2) (by simpa using hgapAngle j (0 : Fin 2))
  · have hidx : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    have hgap := hgapAngle j (1 : Fin 2)
    simp only [Fin.val_one] at hgap
    rw [hidx] at hgap
    have hch := hChord j (j + 1) (1 : Fin 2) (0 : Fin 2) (by
      simpa using hgap)
    simpa only [orbit, Fin.val_one, Fin.val_zero, hidx, Nat.add_zero] using hch

end DFP.TwoPhaseOrbit
