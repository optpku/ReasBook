module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointAngleRemainder
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PolarGradientAngleError
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientAngleLift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientAngleGap
import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientLimit
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Filter
open scoped Topology

set_option maxRecDepth 10000

namespace DFP.TwoPhaseOrbit

/-- Explicit-constant endpoint-angle gap bound: the two consecutive endpoint-angle
gaps lie between one half and five halves of the squared cycle scale. -/
theorem slowCurveEndpointPolarAngleGapExplicitBounds (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            StrictAnti (orbit.endpointPolarAngleLift Clim) ∧
              ∀ j : ℕ, ∀ i : Fin 2,
                let k := 2 * j + i.val
                orbit.endpointPolarAngleLift Clim k -
                    orbit.endpointPolarAngleLift Clim (k + 1) ∈
                  Set.Icc ((1 / 2 : ℝ) * (orbit.state j).ε ^ 2)
                    ((5 / 2 : ℝ) * (orbit.state j).ε ^ 2) := by
  let R : Unit → ℝ → ℝ × ℝ := fun _ ε ↦
    ((DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal -
        (-2 * ε ^ 2),
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal -
        (-ε ^ 2))
  let ωθ := Asymptotics.uniformRemainderModulus R Set.univ 2
  obtain ⟨ηRem, hηRem, hModulus, hRem⟩ :=
    slowCurveEndpointAngleRemainderModulus p h h_invariant h_pJet h_hJet
  obtain ⟨ηAQ, hηAQ, Kangle, hKangle, hAQ⟩ :=
    DFP.TwoPhaseOrbit.slowCurvePolarGradientAngleErrorUniform
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGrad, hηGrad, gmin, hgmin, gmax, hgminmax, hGrad⟩ :=
    slowCurveEndpointGradientNormUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηNext, hηNext, hNext⟩ :=
    DFP.TwoLeg.slowCurveNextPosLt p h h_pJet h_hJet
  let ηBase := min ηRem (min ηAQ (min ηGrad (min ηGraph ηNext)))
  have hηBase : ηBase ∈ Set.Ioo (0 : ℝ) (1 / 4) := by
    constructor
    · dsimp only [ηBase]
      exact lt_min hηRem.1 (lt_min hηAQ.1
        (lt_min hηGrad.1 (lt_min hηGraph.1 hηNext)))
    · exact (min_le_left _ _).trans_lt hηRem.2
  obtain ⟨ηExact, hηExact, hExact⟩ :=
    ofSlowCurveExact p h h_invariant h_pJet h_hJet ηBase hηBase
  let ηCorr := 1 / (16 * Kangle)
  have hηCorr : 0 < ηCorr := by
    dsimp only [ηCorr]
    positivity
  let δ := min ηExact ηCorr
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hηExact.1 hηCorr
  have hωSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωθ η < 1 / 8 := by
    exact hModulus.tendsto_zero.eventually (Iio_mem_nhds (by norm_num))
  have hIooSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioo 0 δ :=
    Ioo_mem_nhdsGT hδ
  have hchoice : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      η ∈ Set.Ioo 0 δ ∧ ωθ η < 1 / 8 :=
    hIooSmall.and hωSmall
  obtain ⟨εbar, hεbarδ, hωbar⟩ := Filter.nonempty_of_mem hchoice
  have hεbarExact : εbar ≤ ηExact :=
    hεbarδ.2.le.trans (min_le_left _ _)
  have hεbarBase : εbar ≤ ηBase :=
    hεbarExact.trans hηExact.2
  have hεbarRem : εbar ∈ Set.Ioc 0 ηRem :=
    ⟨hεbarδ.1, hεbarBase.trans (min_le_left _ _)⟩
  have hεbarLt : εbar < (1 / 4 : ℝ) := hεbarRem.2.trans_lt hηRem.2
  have hcorrectionCoefficient : 2 * Kangle * εbar ≤ 1 / 8 := by
    have hεbarCorr : εbar ≤ ηCorr :=
      hεbarδ.2.le.trans (min_le_right _ _)
    dsimp only [ηCorr] at hεbarCorr
    have hdenom : 16 * Kangle ≠ 0 := by positivity
    calc
      2 * Kangle * εbar ≤ 2 * Kangle * (1 / (16 * Kangle)) := by
        gcongr
      _ = 1 / 8 := by
        field_simp [hdenom]
        norm_num
  refine ⟨εbar, ⟨hεbarδ.1, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεExact : ε₀ ∈ Set.Ioc 0 ηExact :=
    ⟨hε₀.1, hε₀.2.trans hεbarExact⟩
  have hεBase : ε₀ ∈ Set.Ioc 0 ηBase :=
    ⟨hε₀.1, hε₀.2.trans hεbarBase⟩
  have hεAQ : ε₀ ∈ Set.Ioc 0 ηAQ :=
    ⟨hε₀.1, hεBase.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεGrad : ε₀ ∈ Set.Ioc 0 ηGrad :=
    ⟨hε₀.1, hεBase.2.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hεBase.2.trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))))⟩
  have hεNext : ε₀ ≤ ηNext :=
    hεBase.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hεRem : ε₀ ∈ Set.Ioc 0 εbar := hε₀
  have hexact (j : ℕ) : State.ExactCycle (orbit.state j) := by
    simpa only [orbit] using hExact ε₀ hεExact j
  have hscale (j : ℕ) : (orbit.state j).ε ∈ Set.Ioc 0 ε₀ := by
    let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
    have hx := hGraph ε₀ hεGraph j
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates = xj := by
      simpa only [orbit, xj] using hc
    have heq : (orbit.state j).ε = xj.1 := by
      simpa only [State.coordinates_def] using congrArg Prod.fst hc'
    rw [heq]
    exact hx.2
  have hstateGraph (j : ℕ) : (orbit.state j).coordinates =
      ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
    let xj := DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)
    have hx := hGraph ε₀ hεGraph j
    have hc := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ j
    have hc' : (orbit.state j).coordinates = xj := by
      simpa only [orbit, xj] using hc
    have heq : (orbit.state j).ε = xj.1 := by
      simpa only [State.coordinates_def] using congrArg Prod.fst hc'
    calc
      (orbit.state j).coordinates = xj := hc'
      _ = (xj.1, p xj.1, h xj.1) := hx.1
      _ = ((orbit.state j).ε, p (orbit.state j).ε, h (orbit.state j).ε) := by
        rw [heq]
  have hscaleSuccLe (j : ℕ) : (orbit.state (j + 1)).ε ≤ (orbit.state j).ε := by
    have hjNext : (orbit.state j).ε ∈ Set.Ioc 0 ηNext :=
      ⟨(hscale j).1, (hscale j).2.trans hεNext⟩
    have hraw := (hNext (orbit.state j).ε hjNext).2.le
    have hcoord : (orbit.state (j + 1)).ε =
        (DFP.TwoLeg.stateMap (orbit.state j).coordinates).1 := by
      calc
        (orbit.state (j + 1)).ε = ((orbit.state (j + 1)).coordinates).1 := by
          exact (congrArg Prod.fst (State.coordinates_def (orbit.state (j + 1)))).symm
        _ = ((orbit.state j).next.coordinates).1 := by
          rw [orbit.state_succ]
        _ = (DFP.TwoLeg.stateMap (orbit.state j).coordinates).1 :=
          congrArg Prod.fst (State.next_coordinates (orbit.state j))
    rw [hcoord, hstateGraph j]
    simpa only [DFP.TwoLeg.stateMap, DFP.TwoLeg.signedEpsilon] using hraw
  have hgradientNe (k : ℕ) : orbit.endpointGradient k ≠ 0 := by
    have hb := hGrad ε₀ hεGrad k
    exact norm_pos_iff.mp (hgmin.trans_le hb.1)
  have hgradientLiftEven (j : ℕ) :
      orbit.endpointGradientAngleLift (2 * j + 1) -
          orbit.endpointGradientAngleLift (2 * j) =
        (DFP.TwoLeg.observableMap (orbit.state j).coordinates).firstEndpointAngleIncrement.toReal := by
    rw [endpointGradientAngleLift_succ_sub]
    exact congrArg Real.Angle.toReal
      (endpointGradientAngle_odd_sub_even orbit j (hexact j).valid
        (hgradientNe (2 * j)) (hgradientNe (2 * j + 1)))
  have hgradientLiftOdd (j : ℕ) :
      orbit.endpointGradientAngleLift (2 * j + 2) -
          orbit.endpointGradientAngleLift (2 * j + 1) =
        (DFP.TwoLeg.observableMap (orbit.state j).coordinates).secondEndpointAngleIncrement.toReal := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega,
      endpointGradientAngleLift_succ_sub]
    exact congrArg Real.Angle.toReal
      (endpointGradientAngle_nextEven_sub_odd orbit j (hexact j).valid
        (hgradientNe (2 * j + 1)) (hgradientNe (2 * j + 2)))
  intro Clim hClim
  have hangleCorrection (j : ℕ) (i : Fin 2) :=
    hAQ ε₀ hεAQ Clim hClim j i
  have hremainders (j : ℕ) := hRem εbar hεbarRem ε₀ hεRem j
  have hgapBounds (j : ℕ) (i : Fin 2) :
      let k := 2 * j + i.val
      orbit.endpointPolarAngleLift Clim k -
          orbit.endpointPolarAngleLift Clim (k + 1) ∈
        Set.Icc ((1 / 2 : ℝ) * (orbit.state j).ε ^ 2)
          ((5 / 2 : ℝ) * (orbit.state j).ε ^ 2) := by
    fin_cases i
    · dsimp only [Fin.val_zero, add_zero]
      let e := (orbit.state j).ε
      let a := (DFP.TwoLeg.observableMap (orbit.state j).coordinates).firstEndpointAngleIncrement.toReal
      let corr :=
        (orbit.endpointPolarAngleLift Clim (2 * j) -
            orbit.endpointGradientAngleLift (2 * j)) -
          (orbit.endpointPolarAngleLift Clim (2 * j + 1) -
            orbit.endpointGradientAngleLift (2 * j + 1))
      have he : 0 < e := (hscale j).1
      have hebar : e ≤ εbar := (hscale j).2.trans hε₀.2
      have hrem : |a - (-2 * e ^ 2)| ≤ (1 / 8 : ℝ) * e ^ 2 := by
        exact (hremainders j).1.trans
          (mul_le_mul_of_nonneg_right hωbar.le (sq_nonneg e))
      have hcorrRaw : |corr| ≤ 2 * Kangle * e ^ 3 := by
        calc
          |corr| ≤
              |orbit.endpointPolarAngleLift Clim (2 * j) -
                  orbit.endpointGradientAngleLift (2 * j)| +
                |orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                  orbit.endpointGradientAngleLift (2 * j + 1)| := abs_sub _ _
          _ ≤ Kangle * e ^ 3 + Kangle * e ^ 3 := by
            exact add_le_add (hangleCorrection j 0) (hangleCorrection j 1)
          _ = 2 * Kangle * e ^ 3 := by ring
      have hcorr : |corr| ≤ (1 / 8 : ℝ) * e ^ 2 := by
        calc
          |corr| ≤ 2 * Kangle * e ^ 3 := hcorrRaw
          _ = (2 * Kangle * e) * e ^ 2 := by ring
          _ ≤ (2 * Kangle * εbar) * e ^ 2 := by
            gcongr
          _ ≤ (1 / 8 : ℝ) * e ^ 2 := by
            exact mul_le_mul_of_nonneg_right hcorrectionCoefficient (sq_nonneg e)
      have hgapIdentity :
          orbit.endpointPolarAngleLift Clim (2 * j) -
              orbit.endpointPolarAngleLift Clim (2 * j + 1) = -a + corr := by
        dsimp only [a]
        rw [← hgradientLiftEven j]
        dsimp only [corr]
        ring
      have hgapError :
          |(orbit.endpointPolarAngleLift Clim (2 * j) -
              orbit.endpointPolarAngleLift Clim (2 * j + 1)) - 2 * e ^ 2| ≤
            (1 / 4 : ℝ) * e ^ 2 := by
        rw [hgapIdentity]
        calc
          |-a + corr - 2 * e ^ 2| = |-(a - (-2 * e ^ 2)) + corr| := by ring_nf
          _ ≤ |-(a - (-2 * e ^ 2))| + |corr| := abs_add_le _ _
          _ = |a - (-2 * e ^ 2)| + |corr| := by rw [abs_neg]
          _ ≤ (1 / 8 : ℝ) * e ^ 2 + (1 / 8 : ℝ) * e ^ 2 :=
            add_le_add hrem hcorr
          _ = (1 / 4 : ℝ) * e ^ 2 := by ring
      have herror := abs_le.mp hgapError
      constructor
      · change (1 / 2 : ℝ) * e ^ 2 ≤
          orbit.endpointPolarAngleLift Clim (2 * j) -
            orbit.endpointPolarAngleLift Clim (2 * j + 1)
        nlinarith [herror.1, sq_nonneg e]
      · change orbit.endpointPolarAngleLift Clim (2 * j) -
            orbit.endpointPolarAngleLift Clim (2 * j + 1) ≤ (5 / 2 : ℝ) * e ^ 2
        nlinarith [herror.2, sq_nonneg e]
    · dsimp only [Fin.val_one]
      let e := (orbit.state j).ε
      let enext := (orbit.state (j + 1)).ε
      let a := (DFP.TwoLeg.observableMap (orbit.state j).coordinates).secondEndpointAngleIncrement.toReal
      let corr :=
        (orbit.endpointPolarAngleLift Clim (2 * j + 1) -
            orbit.endpointGradientAngleLift (2 * j + 1)) -
          (orbit.endpointPolarAngleLift Clim (2 * j + 2) -
            orbit.endpointGradientAngleLift (2 * j + 2))
      have he : 0 < e := (hscale j).1
      have henext : 0 < enext := (hscale (j + 1)).1
      have henextLe : enext ≤ e := by
        simpa only [enext, e] using hscaleSuccLe j
      have hcubeNext : enext ^ 3 ≤ e ^ 3 :=
        pow_le_pow_left₀ henext.le henextLe 3
      have hebar : e ≤ εbar := (hscale j).2.trans hε₀.2
      have hrem : |a - (-e ^ 2)| ≤ (1 / 8 : ℝ) * e ^ 2 := by
        exact (hremainders j).2.trans
          (mul_le_mul_of_nonneg_right hωbar.le (sq_nonneg e))
      have hcorrRaw : |corr| ≤ 2 * Kangle * e ^ 3 := by
        calc
          |corr| ≤
              |orbit.endpointPolarAngleLift Clim (2 * j + 1) -
                  orbit.endpointGradientAngleLift (2 * j + 1)| +
                |orbit.endpointPolarAngleLift Clim (2 * j + 2) -
                  orbit.endpointGradientAngleLift (2 * j + 2)| := abs_sub _ _
          _ ≤ Kangle * e ^ 3 + Kangle * enext ^ 3 := by
            gcongr
            · exact hangleCorrection j 1
            · simpa only [enext, show 2 * (j + 1) + (0 : Fin 2).val = 2 * j + 2 by omega]
                using hangleCorrection (j + 1) 0
          _ ≤ Kangle * e ^ 3 + Kangle * e ^ 3 := by
            gcongr
          _ = 2 * Kangle * e ^ 3 := by ring
      have hcorr : |corr| ≤ (1 / 8 : ℝ) * e ^ 2 := by
        calc
          |corr| ≤ 2 * Kangle * e ^ 3 := hcorrRaw
          _ = (2 * Kangle * e) * e ^ 2 := by ring
          _ ≤ (2 * Kangle * εbar) * e ^ 2 := by
            gcongr
          _ ≤ (1 / 8 : ℝ) * e ^ 2 := by
            exact mul_le_mul_of_nonneg_right hcorrectionCoefficient (sq_nonneg e)
      have hgapIdentity :
          orbit.endpointPolarAngleLift Clim (2 * j + 1) -
              orbit.endpointPolarAngleLift Clim (2 * j + 2) = -a + corr := by
        dsimp only [a]
        rw [← hgradientLiftOdd j]
        dsimp only [corr]
        ring
      have hgapError :
          |(orbit.endpointPolarAngleLift Clim (2 * j + 1) -
              orbit.endpointPolarAngleLift Clim (2 * j + 2)) - e ^ 2| ≤
            (1 / 4 : ℝ) * e ^ 2 := by
        rw [hgapIdentity]
        calc
          |-a + corr - e ^ 2| = |-(a - (-e ^ 2)) + corr| := by ring_nf
          _ ≤ |-(a - (-e ^ 2))| + |corr| := abs_add_le _ _
          _ = |a - (-e ^ 2)| + |corr| := by rw [abs_neg]
          _ ≤ (1 / 8 : ℝ) * e ^ 2 + (1 / 8 : ℝ) * e ^ 2 :=
            add_le_add hrem hcorr
          _ = (1 / 4 : ℝ) * e ^ 2 := by ring
      have herror := abs_le.mp hgapError
      constructor
      · change (1 / 2 : ℝ) * e ^ 2 ≤
          orbit.endpointPolarAngleLift Clim (2 * j + 1) -
            orbit.endpointPolarAngleLift Clim (2 * j + 2)
        nlinarith [herror.1, sq_nonneg e]
      · change orbit.endpointPolarAngleLift Clim (2 * j + 1) -
            orbit.endpointPolarAngleLift Clim (2 * j + 2) ≤ (5 / 2 : ℝ) * e ^ 2
        nlinarith [herror.2, sq_nonneg e]
  refine ⟨strictAnti_nat_of_succ_lt ?_, hgapBounds⟩
  intro k
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hb := (hgapBounds j 0).1
    have he := (hscale j).1
    norm_num at hb ⊢
    nlinarith [sq_pos_of_pos he]
  · have hb := (hgapBounds j 1).1
    have he := (hscale j).1
    norm_num at hb ⊢
    nlinarith [sq_pos_of_pos he]

/-- For a sufficiently small invariant slow-curve orbit, the lifted physical endpoint
angles are strictly decreasing and each consecutive gap is uniformly comparable to
the square of the cycle scale. -/
theorem slowCurveEndpointPolarAngleGapUniformBounds (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cθ > 0, ∃ Cθ > cθ,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
            StrictAnti (orbit.endpointPolarAngleLift Clim) ∧
              ∀ j : ℕ, ∀ i : Fin 2,
                let k := 2 * j + i.val
                orbit.endpointPolarAngleLift Clim k -
                    orbit.endpointPolarAngleLift Clim (k + 1) ∈
                  Set.Icc (cθ * (orbit.state j).ε ^ 2)
                    (Cθ * (orbit.state j).ε ^ 2) := by
  obtain ⟨εbar, hεbar, hcore⟩ :=
    slowCurveEndpointPolarAngleGapExplicitBounds
      p h h_invariant h_pJet h_hJet
  exact ⟨εbar, hεbar, (1 / 2 : ℝ), by norm_num,
    (5 / 2 : ℝ), by norm_num, hcore⟩

/-- Every sufficiently small invariant slow-curve orbit has a consecutive lifted
endpoint-angle gap at least half the square of its cycle scale. -/
theorem slowCurveEndpointPolarAngleGapLowerBound (p h : ℝ → ℝ)
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
            ∀ (j : ℕ) (i : Fin 2),
              orbit.endpointPolarAngleLift Clim (2 * j + i.val) -
                  orbit.endpointPolarAngleLift Clim (2 * j + i.val + 1) ≥
                (1 / 2 : ℝ) * (orbit.state j).ε ^ 2 := by
  obtain ⟨εbar, hεbar, hcore⟩ :=
    slowCurveEndpointPolarAngleGapExplicitBounds
      p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim j i
  exact ((hcore ε₀ hε₀ Clim hClim).2 j i).1

end DFP.TwoPhaseOrbit
