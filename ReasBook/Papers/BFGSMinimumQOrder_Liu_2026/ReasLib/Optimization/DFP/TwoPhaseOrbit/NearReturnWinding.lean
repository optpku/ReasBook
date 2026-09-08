module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleGap
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity
import ReasLib.Topology.Circle.AngleLift

public section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- A near-return decomposition of two lifted endpoint angles has positive winding
number when the later endpoint is chronologically and radially separated. -/
theorem slowCurveNearReturnWindingNumber_pos (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5))
    (κ : ℝ) (_hκ : κ ∈ Set.Ioo (1 / Real.sqrt 2) 1) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
            ∀ j ℓ : ℕ, ∀ σ τ : Fin 2,
              2 * j + σ.val < 2 * ℓ + τ.val →
                κ * (orbit.state j).ε < (orbit.state ℓ).ε →
                  ∀ (m : ℤ) (ζ : ℝ),
                    orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                        orbit.endpointPolarAngleLift Clim (2 * ℓ + τ.val) =
                      2 * Real.pi * (m : ℝ) + ζ →
                        |ζ| < (orbit.state j).ε ^ 2 / 4 →
                          1 ≤ m := by
  obtain ⟨ηAngle, hηAngle, cθ, hcθ, Cθ, hCθ, hAngle⟩ :=
    slowCurveEndpointPolarAngleGapUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηLower, hηLower, hLower⟩ :=
    slowCurveEndpointPolarAngleGapLowerBound p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min (min ηAngle ηLower) ηGraph
  have hεbar : εbar ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · dsimp only [εbar]
      exact lt_min (lt_min hηAngle.1 hηLower.1) hηGraph.1
    · calc
        εbar ≤ min ηAngle ηLower := min_le_left _ _
        _ ≤ ηAngle := min_le_left _ _
        _ < 1 / 4 := hηAngle.2
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεAngle : ε₀ ∈ Set.Ioc 0 ηAngle :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hεLower : ε₀ ∈ Set.Ioc 0 ηLower :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  intro Clim hClim
  have hanti := (hAngle ε₀ hεAngle Clim hClim).1
  have hgap := hLower ε₀ hεLower Clim hClim
  intro j ℓ σ τ hchron _hscaleCompare m ζ heq hζ
  let k := 2 * j + σ.val
  let n := 2 * ℓ + τ.val
  have hchron' : k < n := by simpa only [k, n] using hchron
  have hsuccLe : k + 1 ≤ n := Nat.succ_le_iff.mpr hchron'
  have hangleOrder : orbit.endpointPolarAngleLift Clim n ≤
      orbit.endpointPolarAngleLift Clim (k + 1) :=
    hanti.antitone hsuccLe
  have hfirstGap : (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 ≤
      orbit.endpointPolarAngleLift Clim k -
        orbit.endpointPolarAngleLift Clim (k + 1) := by
    simpa only [k] using hgap j σ
  have htotalLower : (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 ≤
      orbit.endpointPolarAngleLift Clim k - orbit.endpointPolarAngleLift Clim n := by
    linarith
  let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
  have hxj := hGraph ε₀ hεGraph j
  have hcoordinates := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
  have hcoordinates' : (orbit.state j).coordinates = xj := by
    simpa only [orbit, xj] using hcoordinates
  have hscaleEq : (orbit.state j).ε = xj.1 := by
    simpa only [DFP.TwoPhaseOrbit.State.coordinates_def] using
      congrArg Prod.fst hcoordinates'
  have hscalePos : 0 < (orbit.state j).ε := by
    rw [hscaleEq]
    exact hxj.2.1
  have hζUpper : ζ < (orbit.state j).ε ^ 2 / 4 :=
    (le_abs_self ζ).trans_lt hζ
  have hζGap : ζ < orbit.endpointPolarAngleLift Clim k -
      orbit.endpointPolarAngleLift Clim (k + 1) := by
    nlinarith [sq_pos_of_pos hscalePos]
  exact Real.Angle.windingNumber_pos_of_antitone
    (orbit.endpointPolarAngleLift Clim) hanti.antitone hchron'
    (by simpa only [k, n] using heq) hζGap

end DFP.TwoPhaseOrbit
