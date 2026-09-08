module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoPhaseOrbit

/-- A comparable-scale interval of a positive slow-curve orbit has a uniform
positive fourth-order loss in physical amplitude at each intervening cycle. -/
theorem slowCurveComparableScaleAmplitudeLoss (p h : ℝ → ℝ)
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
    (κ : ℝ) (hκ : κ ∈ Set.Ioo (1 / Real.sqrt 2) 1) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cG > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ j ℓ t : ℕ, j ≤ t → t < ℓ →
          κ * (orbit.state j).ε < (orbit.state ℓ).ε →
            cG * (orbit.state j).ε ^ 4 ≤
              (orbit.state t).amplitude - (orbit.state (t + 1)).amplitude := by
  obtain ⟨ηDrift, hηDrift, hDriftMod, hDrift⟩ :=
    slowCurveAmplitudeDriftModulus p h h_invariant h_pJet h_hJet
  obtain ⟨ηBounds, hηBounds, Gmin, hGmin, Gmax, hGcmp, hBounds⟩ :=
    slowCurveAmplitudeUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηStep, hηStep, hStep⟩ :=
    DFP.TwoLeg.slowCurveNextPosLt p h h_pJet h_hJet
  let ωA : ℝ → ℝ := Asymptotics.uniformRemainderModulus
    (fun _ : Unit ↦ fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) Set.univ 4
  have hDriftSpec :=
    (Asymptotics.IsUniformRemainderModulusOn.spec _ _ _ _ _).mp hDriftMod
  have hωsmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωA η < (13 / 4 : ℝ) := by
    exact (tendsto_order.1 hDriftSpec.2.2.1).2 _ (by norm_num)
  have hηsmall : ∃ η ∈ Set.Ioc (0 : ℝ) ηDrift, ωA η < (13 / 4 : ℝ) := by
    have hmem : Set.Ioc (0 : ℝ) ηDrift ∈ 𝓝[>] (0 : ℝ) :=
      Ioc_mem_nhdsGT hηDrift.1
    have hinter : ∀ᶠ η in 𝓝[>] (0 : ℝ),
        ωA η < (13 / 4 : ℝ) ∧ η ∈ Set.Ioc (0 : ℝ) ηDrift := by
      filter_upwards [hωsmall, hmem] with η hω hη
      exact ⟨hω, hη⟩
    obtain ⟨η, hη⟩ := Filter.Eventually.exists hinter
    exact ⟨η, hη.2, hη.1⟩
  obtain ⟨η, hη, hωη⟩ := hηsmall
  let εbar := min (min (min η ηBounds) ηGraph) ηStep
  have hεbar_le_eta : εbar ≤ η := by
    dsimp [εbar]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεbar_le_bounds : εbar ≤ ηBounds := by
    dsimp [εbar]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεbar_le_graph : εbar ≤ ηGraph := by
    dsimp [εbar]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hεbar_le_step : εbar ≤ ηStep := by
    dsimp [εbar]
    exact min_le_right _ _
  have hεbar_pos : 0 < εbar := by
    dsimp [εbar]
    exact lt_min (lt_min (lt_min hη.1 hηBounds.1) hηGraph.1) hηStep
  have hεbar_lt : εbar < 1 / 4 := by
    exact lt_of_le_of_lt hεbar_le_eta (lt_of_le_of_lt hη.2 hηDrift.2)
  have hκ_pos : 0 < κ := by
    have : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity
    exact this.trans hκ.1
  have hκ4 : 0 < κ ^ 4 := pow_pos hκ_pos 4
  refine ⟨εbar, ⟨hεbar_pos, hεbar_lt⟩, Gmin * (13 / 4 : ℝ) * κ ^ 4, ?_, ?_⟩
  · positivity
  · intro ε₀ hε₀
    dsimp
    have hε₀Drift : ε₀ ∈ Set.Ioc 0 η :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_eta⟩
    have hε₀Bounds : ε₀ ∈ Set.Ioc 0 ηBounds :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_bounds⟩
    have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_graph⟩
    have hε₀Step : ε₀ ∈ Set.Ioc 0 ηStep :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_step⟩
    let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
    obtain ⟨Glim, hGlim, hGlim_tendsto, hAmpBounds⟩ := hBounds ε₀ hε₀Bounds
    have hcoord (n : ℕ) :
        (orbit.state n).coordinates =
          DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀) := by
      simpa [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ n
    have hεeq (n : ℕ) :
        (orbit.state n).ε =
          (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := by
      exact congrArg Prod.fst (by simpa [State.coordinates_def] using hcoord n)
    have hforward (n : ℕ) := hGraph ε₀ hε₀Graph n
    have hεpos (n : ℕ) : 0 < (orbit.state n).ε := by
      rw [hεeq n]
      exact (hforward n).2.1
    have hεle₀ (n : ℕ) : (orbit.state n).ε ≤ ε₀ := by
      rw [hεeq n]
      exact (hforward n).2.2
    have hstateMapFirst (ε p' h' : ℝ) :
        (DFP.TwoLeg.stateMap (ε, p', h')).1 =
          DFP.TwoLeg.signedEpsilon ε p' h' := by
      simp [DFP.TwoLeg.stateMap, DFP.TwoLeg.signedEpsilon,
        DFP.TwoLeg.radiusFactor]
    have hstep (n : ℕ) : (orbit.state (n + 1)).ε < (orbit.state n).ε := by
      have hnmem : (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 ∈
          Set.Ioc (0 : ℝ) ηStep :=
        ⟨by simpa [hεeq n] using hεpos n,
          ((hεeq n).symm ▸ hεle₀ n).trans hε₀Step.2⟩
      have hlt := hStep _ hnmem
      have hnextcoord : (orbit.state (n + 1)).coordinates =
          DFP.TwoLeg.stateMap (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)) := by
        calc
          (orbit.state (n + 1)).coordinates =
              DFP.TwoLeg.stateMap^[n + 1] (ε₀, p ε₀, h ε₀) := hcoord (n + 1)
          _ = DFP.TwoLeg.stateMap (DFP.TwoLeg.stateMap^[n]
              (ε₀, p ε₀, h ε₀)) := by rw [Function.iterate_succ_apply']
      have hnextε := congrArg Prod.fst hnextcoord
      calc
        (orbit.state (n + 1)).ε =
            (DFP.TwoLeg.stateMap (DFP.TwoLeg.stateMap^[n]
              (ε₀, p ε₀, h ε₀))).1 := by
                simpa [State.coordinates_def] using hnextε
        _ = DFP.TwoLeg.signedEpsilon
              (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
              (p (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1)
              (h (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1) := by
                rw [(hforward n).1]
                simpa only [Prod.fst] using
                  hstateMapFirst
                    (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
                    (p (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1)
                    (h (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1)
        _ < (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := hlt.2
        _ = (orbit.state n).ε := (hεeq n).symm
    have hmono (a b : ℕ) (hab : a ≤ b) :
        (orbit.state b).ε ≤ (orbit.state a).ε := by
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ b hab ih => exact (hstep b).le.trans ih
    intro j ℓ t hjt htl hcomp
    have hratioBound := hDrift η hη ε₀ hε₀Drift t
    have hratioRem :
        |(orbit.state (t + 1)).amplitude / (orbit.state t).amplitude -
            (1 - (13 / 2) * (orbit.state t).ε ^ 4)| ≤
          ωA η * (orbit.state t).ε ^ 4 := by
      simpa [ωA, orbit] using hratioBound
    have hεtpow : 0 < (orbit.state t).ε ^ 4 := pow_pos (hεpos t) 4
    have hωmul : ωA η * (orbit.state t).ε ^ 4 <
        (13 / 4 : ℝ) * (orbit.state t).ε ^ 4 :=
      mul_lt_mul_of_pos_right hωη hεtpow
    have hratioDrop :
        (13 / 4 : ℝ) * (orbit.state t).ε ^ 4 ≤
          1 - (orbit.state (t + 1)).amplitude / (orbit.state t).amplitude := by
      have hpos := le_trans (le_abs_self _) hratioRem
      linarith
    have hAmpLower : Gmin ≤ (orbit.state t).amplitude := by
      simpa [orbit] using (hAmpBounds t).1
    have hAmpPos : 0 < (orbit.state t).amplitude :=
      lt_of_lt_of_le hGmin hAmpLower
    have hdropEq :
        (orbit.state t).amplitude - (orbit.state (t + 1)).amplitude =
          (orbit.state t).amplitude *
            (1 - (orbit.state (t + 1)).amplitude / (orbit.state t).amplitude) := by
      field_simp [ne_of_gt hAmpPos]
    have hdropLower :
        Gmin * ((13 / 4 : ℝ) * (orbit.state t).ε ^ 4) ≤
          (orbit.state t).amplitude - (orbit.state (t + 1)).amplitude := by
      rw [hdropEq]
      calc
        Gmin * ((13 / 4 : ℝ) * (orbit.state t).ε ^ 4) ≤
            (orbit.state t).amplitude * ((13 / 4 : ℝ) * (orbit.state t).ε ^ 4) := by
              exact mul_le_mul_of_nonneg_right hAmpLower
                (by positivity)
        _ ≤ (orbit.state t).amplitude *
            (1 - (orbit.state (t + 1)).amplitude / (orbit.state t).amplitude) := by
              exact mul_le_mul_of_nonneg_left hratioDrop (le_of_lt hAmpPos)
    have hεell_le_t : (orbit.state ℓ).ε ≤ (orbit.state t).ε :=
      hmono t ℓ (Nat.le_of_lt htl)
    have hκeps : κ * (orbit.state j).ε < (orbit.state t).ε :=
      lt_of_lt_of_le hcomp hεell_le_t
    have hpowComp : κ ^ 4 * (orbit.state j).ε ^ 4 ≤
        (orbit.state t).ε ^ 4 := by
      have hpow := pow_lt_pow_left₀ hκeps
        (mul_pos hκ_pos (hεpos j)).le
        (by norm_num : (4 : ℕ) ≠ 0)
      have hpow' : (κ * (orbit.state j).ε) ^ 4 <
          (orbit.state t).ε ^ 4 := hpow
      nlinarith [hpow']
    calc
      (Gmin * (13 / 4 : ℝ) * κ ^ 4) * (orbit.state j).ε ^ 4 =
          Gmin * ((13 / 4 : ℝ) * (κ ^ 4 * (orbit.state j).ε ^ 4)) := by ring
      _ ≤ Gmin * ((13 / 4 : ℝ) * (orbit.state t).ε ^ 4) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpowComp (by norm_num)) hGmin.le
      _ ≤ (orbit.state t).amplitude - (orbit.state (t + 1)).amplitude := hdropLower

end DFP.TwoPhaseOrbit
