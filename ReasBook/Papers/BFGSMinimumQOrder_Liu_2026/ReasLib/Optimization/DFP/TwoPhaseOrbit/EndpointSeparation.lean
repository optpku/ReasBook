module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointDistance
import ReasLib.Optimization.DFP.TwoPhaseOrbit.ScaleSeparation
import ReasLib.Optimization.DFP.TwoPhaseOrbit.AngularGapSeparation
import ReasLib.Optimization.DFP.TwoPhaseOrbit.NearReturnWinding
import ReasLib.Optimization.DFP.TwoPhaseOrbit.NearReturnEndpointSeparation
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity
import ReasLib.Topology.MetricSpace.InfDistUnionRange
import ReasLib.Topology.MetricSpace.PairwiseSeparation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- All distinct endpoints of every sufficiently small invariant slow-curve orbit
are uniformly separated at the squared scale of the first endpoint. -/
theorem slowCurveUniformEndpointPairSeparation (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cPair > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k l : ℕ, k ≠ l →
                  cPair * (orbit.state (k / 2)).ε ^ 2 ≤
                    dist (orbit.endpoint k) (orbit.endpoint l) := by
  have htwoPos : (0 : ℝ) < 2 := by
    norm_num
  have htwoNonneg : (0 : ℝ) ≤ 2 := htwoPos.le
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 htwoPos
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt htwoNonneg
  have hκ : (3 / 4 : ℝ) ∈ Set.Ioo (1 / Real.sqrt 2) 1 := by
    constructor
    · apply (div_lt_iff₀ hsqrtPos).2
      nlinarith
    · norm_num
  obtain ⟨ηDiff, hηDiff, cDiff, hcDiff, hDiff⟩ :=
    slowCurveDifferentScaleEndpointSeparation
      p h h_invariant h_pJet h_hJet (3 / 4) hκ
  obtain ⟨ηAngle, hηAngle, cAngle, hcAngle, hAngle⟩ :=
    slowCurveAngularGapEndpointSeparation
      p h h_invariant h_pJet h_hJet (3 / 4)
  obtain ⟨ηAdj, hηAdj, cAdj, hcAdj, hAdj⟩ :=
    slowCurveAdjacentEndpointSeparation p h h_invariant h_pJet h_hJet
  obtain ⟨ηWind, hηWind, hWind⟩ :=
    slowCurveNearReturnWindingNumber_pos p h h_invariant h_pJet h_hJet (3 / 4) hκ
  obtain ⟨ηNear, hηNear, cNear, hcNear, hNear⟩ :=
    slowCurveNearReturnEndpointSeparation p h h_invariant h_pJet h_hJet (3 / 4) hκ
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηStep, hηStep, hStep⟩ :=
    DFP.TwoLeg.slowCurveNextPosLt p h h_pJet h_hJet
  let εbar := min ηDiff
    (min ηAngle (min ηAdj (min ηWind (min ηNear (min ηGraph ηStep)))))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηDiff.1
      (lt_min hηAngle.1 (lt_min hηAdj.1
        (lt_min hηWind.1 (lt_min hηNear.1 (lt_min hηGraph.1 hηStep)))))
  have hεbarLt : εbar < (1 / 4 : ℝ) := (min_le_left _ _).trans_lt hηDiff.2
  let cPair := min cAdj (min cDiff (min cAngle cNear))
  have hcPair : 0 < cPair := by
    dsimp only [cPair]
    exact lt_min hcAdj (lt_min hcDiff (lt_min hcAngle hcNear))
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, cPair, hcPair, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεbarDiff : εbar ≤ ηDiff := min_le_left _ _
  have hεbarAngle : εbar ≤ ηAngle :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hεbarAdj : εbar ≤ ηAdj :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεbarWind : εbar ≤ ηWind :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hεbarNear : εbar ≤ ηNear :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hεbarGraph : εbar ≤ ηGraph :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
  have hεbarStep : εbar ≤ ηStep :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))))
  have hεDiff : ε₀ ∈ Set.Ioc 0 ηDiff := ⟨hε₀.1, hε₀.2.trans hεbarDiff⟩
  have hεAngle : ε₀ ∈ Set.Ioc 0 ηAngle := ⟨hε₀.1, hε₀.2.trans hεbarAngle⟩
  have hεAdj : ε₀ ∈ Set.Ioc 0 ηAdj := ⟨hε₀.1, hε₀.2.trans hεbarAdj⟩
  have hεWind : ε₀ ∈ Set.Ioc 0 ηWind := ⟨hε₀.1, hε₀.2.trans hεbarWind⟩
  have hεNear : ε₀ ∈ Set.Ioc 0 ηNear := ⟨hε₀.1, hε₀.2.trans hεbarNear⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph := ⟨hε₀.1, hε₀.2.trans hεbarGraph⟩
  have hεStep : ε₀ ∈ Set.Ioc 0 ηStep := ⟨hε₀.1, hε₀.2.trans hεbarStep⟩
  have hcoordinate (n : ℕ) : (orbit.state n).coordinates =
      DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀) := by
    simpa only [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ n
  have hscaleEq (n : ℕ) : (orbit.state n).ε =
      (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := by
    simpa only [State.coordinates_def] using congrArg Prod.fst (hcoordinate n)
  have hforward (n : ℕ) := hGraph ε₀ hεGraph n
  have hscalePos (n : ℕ) : 0 < (orbit.state n).ε := by
    rw [hscaleEq n]
    exact (hforward n).2.1
  have hscaleLeInitial (n : ℕ) : (orbit.state n).ε ≤ ε₀ := by
    rw [hscaleEq n]
    exact (hforward n).2.2
  have hstep (n : ℕ) : (orbit.state (n + 1)).ε < (orbit.state n).ε := by
    have hnPositive : 0 < (DFP.TwoLeg.stateMap^[n]
        (ε₀, p ε₀, h ε₀)).1 := by
      simpa only [← hscaleEq n] using hscalePos n
    have hnUpper : (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 ≤ ηStep :=
      ((hscaleEq n).symm ▸ hscaleLeInitial n).trans hεStep.2
    have hnmem : (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 ∈
        Set.Ioc (0 : ℝ) ηStep := ⟨hnPositive, hnUpper⟩
    have hlt := hStep _ hnmem
    have hnextCoordinate : (orbit.state (n + 1)).coordinates =
        DFP.TwoLeg.stateMap (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)) := by
      calc
        (orbit.state (n + 1)).coordinates =
            DFP.TwoLeg.stateMap^[n + 1] (ε₀, p ε₀, h ε₀) := hcoordinate (n + 1)
        _ = DFP.TwoLeg.stateMap (DFP.TwoLeg.stateMap^[n]
            (ε₀, p ε₀, h ε₀)) := by
          rw [Function.iterate_succ_apply']
    have hnextScale := congrArg Prod.fst hnextCoordinate
    calc
      (orbit.state (n + 1)).ε =
          (DFP.TwoLeg.stateMap (DFP.TwoLeg.stateMap^[n]
            (ε₀, p ε₀, h ε₀))).1 := by
        simpa only [State.coordinates_def] using hnextScale
      _ = DFP.TwoLeg.signedEpsilon
            (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
            (p (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1)
            (h (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1) := by
        rw [(hforward n).1]
        simpa only [Prod.fst] using DFP.TwoLeg.stateMap_fst
          (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
          (p (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1)
          (h (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1)
      _ < (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := hlt.2
      _ = (orbit.state n).ε := (hscaleEq n).symm
  have hscaleAnti (a b : ℕ) (hab : a ≤ b) :
      (orbit.state b).ε ≤ (orbit.state a).ε := by
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (hstep b).le.trans ih
  intro Clim hClim Glim hGlim hGlimTendsto
  have hDiffData := hDiff ε₀ hεDiff Clim hClim Glim hGlim hGlimTendsto
  have hAngleData := hAngle ε₀ hεAngle Clim hClim Glim hGlim hGlimTendsto
  have hAdjData := hAdj ε₀ hεAdj Clim hClim Glim hGlim hGlimTendsto
  have hWindData := hWind ε₀ hεWind Clim hClim
  have hNearData := hNear ε₀ hεNear Clim hClim
  have hstructured (j l : ℕ) (σ τ : Fin 2)
      (hindex : 2 * j + σ.val < 2 * l + τ.val) :
      cPair * (orbit.state j).ε ^ 2 ≤
        dist (orbit.endpoint (2 * j + σ.val))
          (orbit.endpoint (2 * l + τ.val)) := by
    by_cases hjlEq : j = l
    · subst l
      fin_cases σ
      · fin_cases τ
        · simp at hindex
        · have hcPairAdj : cPair ≤ cAdj := min_le_left _ _
          have hscaled := mul_le_mul_of_nonneg_right hcPairAdj
            (sq_nonneg ((orbit.state j).ε))
          have hadjacent := hAdjData j (0 : Fin 2)
          have hadjacent' : cAdj * (orbit.state j).ε ^ 2 ≤
              dist (orbit.endpoint (2 * j)) (orbit.endpoint (2 * j + 1)) := by
            simpa using hadjacent
          exact hscaled.trans hadjacent'
      · fin_cases τ
        · simp at hindex
        · simp at hindex
    · have hjl : j < l := by
        omega
      by_cases hscaleFar :
          (orbit.state l).ε ≤ (3 / 4 : ℝ) * (orbit.state j).ε
      · have hcPairDiff : cPair ≤ cDiff :=
          (min_le_right _ _).trans (min_le_left _ _)
        have hscaled := mul_le_mul_of_nonneg_right hcPairDiff
          (sq_nonneg ((orbit.state j).ε))
        exact hscaled.trans (hDiffData j l σ τ hindex hscaleFar)
      · have hcomparable : (3 / 4 : ℝ) * (orbit.state j).ε <
            (orbit.state l).ε := lt_of_not_ge hscaleFar
        let k := 2 * j + σ.val
        let n := 2 * l + τ.val
        let L := orbit.endpointPolarAngleLift Clim k - orbit.endpointPolarAngleLift Clim n
        let ζ := (orbit.endpointPolarAngle Clim k - orbit.endpointPolarAngle Clim n).toReal
        have hcoe : ((L : ℝ) : Real.Angle) = ((ζ : ℝ) : Real.Angle) := by
          dsimp only [L, ζ]
          change (orbit.endpointPolarAngleLift Clim k : Real.Angle) -
              (orbit.endpointPolarAngleLift Clim n : Real.Angle) =
            (((orbit.endpointPolarAngle Clim k -
              orbit.endpointPolarAngle Clim n).toReal : ℝ) : Real.Angle)
          rw [endpointPolarAngleLift_coe, endpointPolarAngleLift_coe,
            Real.Angle.coe_toReal]
        obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hcoe
        have hdecomposition : L = 2 * Real.pi * (m : ℝ) + ζ := by
          linarith
        by_cases hlarge : (orbit.state j).ε ^ 2 / 4 ≤ |ζ|
        · have hcPairAngle : cPair ≤ cAngle :=
            (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
          have hscaled := mul_le_mul_of_nonneg_right hcPairAngle
            (sq_nonneg ((orbit.state j).ε))
          have hlarge' : (orbit.state j).ε ^ 2 / 4 ≤
              |(orbit.endpointPolarAngle Clim k -
                orbit.endpointPolarAngle Clim n).toReal| := by
            simpa only [ζ] using hlarge
          exact hscaled.trans (hAngleData j l σ τ hindex hcomparable hlarge')
        · have hsmall : |ζ| < (orbit.state j).ε ^ 2 / 4 := lt_of_not_ge hlarge
          have hdecomposition' :
              orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                  orbit.endpointPolarAngleLift Clim (2 * l + τ.val) =
                2 * Real.pi * (m : ℝ) + ζ := by
            simpa only [L, k, n] using hdecomposition
          have hmPos : 1 ≤ m := hWindData j l σ τ hindex hcomparable m ζ
            hdecomposition' hsmall
          have hcPairNear : cPair ≤ cNear :=
            (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
          have hscaled := mul_le_mul_of_nonneg_right hcPairNear
            (sq_nonneg ((orbit.state j).ε))
          exact hscaled.trans
            (hNearData j l σ τ hjl hcomparable m ζ hmPos hdecomposition' hsmall)
  have hordered (k n : ℕ) (hkn : k < n) :
      cPair * (orbit.state (k / 2)).ε ^ 2 ≤
        dist (orbit.endpoint k) (orbit.endpoint n) := by
    rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
    · rcases Nat.even_or_odd' n with ⟨l, rfl | rfl⟩
      · have hindex : 2 * j + (0 : Fin 2).val < 2 * l + (0 : Fin 2).val := by
          simpa using hkn
        simpa using hstructured j l (0 : Fin 2) (0 : Fin 2) hindex
      · have hindex : 2 * j + (0 : Fin 2).val < 2 * l + (1 : Fin 2).val := by
          simpa using hkn
        simpa using hstructured j l (0 : Fin 2) (1 : Fin 2) hindex
    · rcases Nat.even_or_odd' n with ⟨l, rfl | rfl⟩
      · have hhalf : (2 * j + 1) / 2 = j := by
          omega
        rw [hhalf]
        have hindex : 2 * j + (1 : Fin 2).val < 2 * l + (0 : Fin 2).val := by
          simpa using hkn
        simpa using hstructured j l (1 : Fin 2) (0 : Fin 2) hindex
      · have hhalf : (2 * j + 1) / 2 = j := by
          omega
        rw [hhalf]
        have hindex : 2 * j + (1 : Fin 2).val < 2 * l + (1 : Fin 2).val := by
          simpa using hkn
        simpa using hstructured j l (1 : Fin 2) (1 : Fin 2) hindex
  intro k l hkl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · exact hordered k l hlt
  · have hlk := hordered l k hgt
    have hdiv : l / 2 ≤ k / 2 := by
      omega
    have hscaleLe := hscaleAnti (l / 2) (k / 2) hdiv
    have hsquareLe : (orbit.state (k / 2)).ε ^ 2 ≤
        (orbit.state (l / 2)).ε ^ 2 := by
      nlinarith [hscalePos (k / 2), hscalePos (l / 2)]
    calc
      cPair * (orbit.state (k / 2)).ε ^ 2 ≤
          cPair * (orbit.state (l / 2)).ε ^ 2 :=
        mul_le_mul_of_nonneg_left hsquareLe hcPair.le
      _ ≤ dist (orbit.endpoint l) (orbit.endpoint k) := hlk
      _ = dist (orbit.endpoint k) (orbit.endpoint l) := dist_comm _ _

/-- The flattened endpoint sequence of every sufficiently small invariant slow-curve
orbit is injective once its center and amplitude have the stated limits. -/
theorem slowCurveEndpoint_injective (p h : ℝ → ℝ)
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
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                Function.Injective orbit.endpoint := by
  obtain ⟨ηPair, hηPair, cPair, hcPair, hPair⟩ :=
    slowCurveUniformEndpointPairSeparation p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min ηPair ηGraph
  have hεbarPos : 0 < εbar := lt_min hηPair.1 hηGraph.1
  have hεbarLt : εbar < (1 / 4 : ℝ) := (min_le_left _ _).trans_lt hηPair.2
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεPair : ε₀ ∈ Set.Ioc 0 ηPair :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans (min_le_right _ _)⟩
  have hcoordinate (j : ℕ) : (orbit.state j).ε =
      (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hraw := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hraw' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hraw
    simpa only [State.coordinates_def] using congrArg Prod.fst hraw'
  have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := by
    rw [hcoordinate j]
    exact (hGraph ε₀ hεGraph j).2.1
  intro Clim hClim Glim hGlim hGlimTendsto
  have hPairData := hPair ε₀ hεPair Clim hClim Glim hGlim hGlimTendsto
  have hlower (k : ℕ) :
      0 < cPair * (orbit.state (k / 2)).ε ^ 2 :=
    mul_pos hcPair (pow_pos (hscalePos (k / 2)) 2)
  exact Metric.injective_of_pos_le_dist
    orbit.endpoint (fun k ↦ cPair * (orbit.state (k / 2)).ε ^ 2)
    hlower hPairData

/-- Every endpoint of a sufficiently small invariant slow-curve orbit is uniformly
isolated from all other endpoints and from the limiting circle at its squared scale. -/
theorem slowCurveUniformEndpointSeparation (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cStar > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            ∀ Glim > 0,
              Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
                ∀ k : ℕ,
                  cStar * (orbit.state (k / 2)).ε ^ 2 ≤
                    Metric.infDist (orbit.endpoint k)
                      (orbit.closedSetCandidate Clim Glim \ {orbit.endpoint k}) := by
  obtain ⟨ηPair, hηPair, cPair, hcPair, hPair⟩ :=
    slowCurveUniformEndpointPairSeparation p h h_invariant h_pJet h_hJet
  obtain ⟨ηCircle, hηCircle, cCircle, hcCircle, hCircle⟩ :=
    slowCurveEndpointLimitCircleInfDistUniformLower p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min ηPair (min ηCircle ηGraph)
  have hεbarPos : 0 < εbar := lt_min hηPair.1 (lt_min hηCircle.1 hηGraph.1)
  have hεbarLt : εbar < (1 / 4 : ℝ) := (min_le_left _ _).trans_lt hηPair.2
  let cStar := min cPair cCircle
  have hcStar : 0 < cStar := lt_min hcPair hcCircle
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, cStar, hcStar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεPair : ε₀ ∈ Set.Ioc 0 ηPair :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεCircle : ε₀ ∈ Set.Ioc 0 ηCircle :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hcoordinate (j : ℕ) : (orbit.state j).ε =
      (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    have hraw := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hraw' : (orbit.state j).coordinates =
        DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀) := by
      simpa only [orbit] using hraw
    simpa only [State.coordinates_def] using congrArg Prod.fst hraw'
  have hscalePos (j : ℕ) : 0 < (orbit.state j).ε := by
    rw [hcoordinate j]
    exact (hGraph ε₀ hεGraph j).2.1
  intro Clim hClim Glim hGlim hGlimTendsto
  have hPairData := hPair ε₀ hεPair Clim hClim Glim hGlim hGlimTendsto
  have hCircleData := hCircle ε₀ hεCircle Clim hClim Glim hGlim hGlimTendsto
  intro k
  let d := cStar * (orbit.state (k / 2)).ε ^ 2
  have hpairScaled (l : ℕ) (hkl : k ≠ l) :
      d ≤ dist (orbit.endpoint k) (orbit.endpoint l) := by
    have hconstant : cStar ≤ cPair := min_le_left _ _
    have hscaled := mul_le_mul_of_nonneg_right hconstant
      (sq_nonneg ((orbit.state (k / 2)).ε))
    exact hscaled.trans (hPairData k l hkl)
  have hcircleScaled : d ≤
      Metric.infDist (orbit.endpoint k) (limitCircle Clim Glim) := by
    have hconstant : cStar ≤ cCircle := min_le_right _ _
    have hscaled := mul_le_mul_of_nonneg_right hconstant
      (sq_nonneg ((orbit.state (k / 2)).ε))
    exact hscaled.trans (hCircleData k)
  have hnextIndex : k ≠ k + 1 := Nat.ne_of_lt (Nat.lt_succ_self k)
  have hnextBound := hpairScaled (k + 1) hnextIndex
  have hdPos : 0 < d := by
    dsimp only [d]
    exact mul_pos hcStar (pow_pos (hscalePos (k / 2)) 2)
  have hnextNe : orbit.endpoint (k + 1) ≠ orbit.endpoint k := by
    intro heq
    rw [heq, dist_self] at hnextBound
    linarith
  have hnonempty :
      ((limitCircle Clim Glim ∪ Set.range orbit.endpoint) \
        {orbit.endpoint k}).Nonempty := by
    refine ⟨orbit.endpoint (k + 1), Or.inr ⟨k + 1, rfl⟩, ?_⟩
    simpa only [Set.mem_singleton_iff] using hnextNe
  rw [closedSetCandidate_eq]
  apply Metric.le_infDist_union_range_diff_singleton hnonempty
  · intro y hy _
    exact hcircleScaled.trans (Metric.infDist_le_dist_of_mem hy)
  · intro l hl
    exact hpairScaled l hl.symm

end DFP.TwoPhaseOrbit
