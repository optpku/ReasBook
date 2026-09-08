module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PhaseRadiusApproximation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.NearReturnAmplitudeGap
public import ReasLib.Topology.MetricSpace.RadialApproximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Endpoint separation from radial approximation and an amplitude gap

The generic core in this file is independent of the slow-curve construction.  The
orbit-level theorem combines it with the uniform phase-radius approximation and the
near-return amplitude gap.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- Comparable-scale positive-winding near returns on a sufficiently small invariant
slow curve have endpoint separation proportional to the earlier squared scale. -/
theorem slowCurveNearReturnEndpointSeparation (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ c > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        ∀ Clim : EuclideanSpace ℝ (Fin 2),
          Tendsto (fun i : ℕ ↦ (orbit.state i).center) atTop (𝓝 Clim) →
            ∀ j ℓ : ℕ, ∀ σ τ : Fin 2,
              j < ℓ →
                κ * (orbit.state j).ε < (orbit.state ℓ).ε →
                  ∀ (m : ℤ) (ζ : ℝ),
                    1 ≤ m →
                      orbit.endpointPolarAngleLift Clim (2 * j + σ.val) -
                          orbit.endpointPolarAngleLift Clim (2 * ℓ + τ.val) =
                        2 * Real.pi * (m : ℝ) + ζ →
                          |ζ| < (orbit.state j).ε ^ 2 / 4 →
                            c * (orbit.state j).ε ^ 2 ≤
                              dist (orbit.endpoint (2 * j + σ.val))
                                (orbit.endpoint (2 * ℓ + τ.val)) := by
  obtain ⟨ηGap, hηGap, c0, hc0, hGap⟩ :=
    slowCurveNearReturnAmplitudeGap p h h_invariant h_pJet h_hJet κ hκ
  obtain ⟨ηR, hηR, ωR, hωRSpec, hR⟩ :=
    slowCurvePhaseRadiusErrorUniform p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  have hωSmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), ωR η < c0 / 4 := by
    exact (tendsto_order.1 hωRSpec.2.2).2 (c0 / 4) (by positivity)
  have hηRMem : Set.Ioc (0 : ℝ) ηR ∈ 𝓝[>] (0 : ℝ) :=
    Ioc_mem_nhdsGT hηR.1
  obtain ⟨ηω, hωηω, hηω⟩ := Filter.Eventually.exists (hωSmall.and hηRMem)
  let εbar := min ηGap (min ηω ηGraph)
  have hεbarPos : 0 < εbar :=
    lt_min hηGap.1 (lt_min hηω.1 hηGraph.1)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_left _ _).trans_lt hηGap.2
  let c : ℝ := c0 / 2
  have hc : 0 < c := half_pos hc0
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, c, hc, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
  have hεGap : ε₀ ∈ Set.Ioc 0 ηGap :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hεω : ε₀ ∈ Set.Ioc 0 ηω :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hεGraph : ε₀ ∈ Set.Ioc 0 ηGraph :=
    ⟨hε₀.1, hε₀.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have hηωR : ηω ∈ Set.Ioc 0 ηR := hηω
  have hcoord (n : ℕ) :
      (orbit.state n).coordinates =
        DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀) := by
    simpa only [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ n
  have hεeq (n : ℕ) :
      (orbit.state n).ε =
        (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := by
    have hfst := congrArg Prod.fst (hcoord n)
    simpa only [State.coordinates_def] using hfst
  have hforward (n : ℕ) := hGraph ε₀ hεGraph n
  have hεpos (n : ℕ) : 0 < (orbit.state n).ε := by
    rw [hεeq n]
    exact (hforward n).2.1
  have hεle₀ (n : ℕ) : (orbit.state n).ε ≤ ε₀ := by
    rw [hεeq n]
    exact (hforward n).2.2
  have hstateGraph (n : ℕ) : (orbit.state n).coordinates =
      ((orbit.state n).ε, p (orbit.state n).ε, h (orbit.state n).ε) := by
    let xn := DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)
    have hcoord' : (orbit.state n).coordinates = xn := by
      simpa only [xn] using hcoord n
    have hgraph' : xn = (xn.1, p xn.1, h xn.1) := by
      simpa only [xn] using (hforward n).1
    calc
      (orbit.state n).coordinates = xn := hcoord'
      _ = (xn.1, p xn.1, h xn.1) := hgraph'
      _ = ((orbit.state n).ε, p (orbit.state n).ε, h (orbit.state n).ε) := by
        rw [hεeq n]
  have hscaleSuccLe (n : ℕ) : (orbit.state (n + 1)).ε ≤ (orbit.state n).ε := by
    have hnGraph : (orbit.state n).ε ∈ Set.Ioc 0 ηGraph :=
      ⟨hεpos n, (hεle₀ n).trans hεGraph.2⟩
    have htail := (hGraph (orbit.state n).ε hnGraph 1).2
    have htailOne :
        (DFP.TwoLeg.stateMap
          ((orbit.state n).ε, p (orbit.state n).ε, h (orbit.state n).ε)).1 ≤
            (orbit.state n).ε := by
      simpa using htail.2
    have hnextcoord : (orbit.state (n + 1)).coordinates =
        DFP.TwoLeg.stateMap (orbit.state n).coordinates := by
      rw [orbit.state_succ, State.next_coordinates]
    rw [hstateGraph n] at hnextcoord
    have hfst := congrArg Prod.fst hnextcoord
    calc
      (orbit.state (n + 1)).ε =
          (DFP.TwoLeg.stateMap
            ((orbit.state n).ε, p (orbit.state n).ε, h (orbit.state n).ε)).1 := by
              simpa only [State.coordinates_def] using hfst
      _ ≤ (orbit.state n).ε := htailOne
  have hmono (a b : ℕ) (hab : a ≤ b) :
      (orbit.state b).ε ≤ (orbit.state a).ε := by
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact (hscaleSuccLe b).trans ih
  intro Clim hClim j ℓ σ τ hjℓ hcomp m ζ hm hangle hζ
  have hamp := hGap ε₀ hεGap Clim hClim j ℓ σ τ hjℓ hcomp m ζ hm hangle hζ
  have hjR := hR ηω hηωR ε₀ hεω Clim hClim j σ
  have hℓR := hR ηω hηωR ε₀ hεω Clim hClim ℓ τ
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hεℓj : (orbit.state ℓ).ε ≤ (orbit.state j).ε :=
    hmono j ℓ (Nat.le_of_lt hjℓ)
  have hsqLe : (orbit.state ℓ).ε ^ 2 ≤ (orbit.state j).ε ^ 2 :=
    pow_le_pow_left₀ (hεpos ℓ).le hεℓj 2
  have hωNonneg : 0 ≤ ωR ηω := hωRSpec.1 ηω hηωR
  have hlaterError :
      ωR ηω * (orbit.state ℓ).ε ^ 2 ≤
        ωR ηω * (orbit.state j).ε ^ 2 :=
    mul_le_mul_of_nonneg_left hsqLe hωNonneg
  have hampBase : c0 * (orbit.state j).ε ^ 2 ≤
      (orbit.state j).amplitude - (orbit.state ℓ).amplitude := by
    calc
      c0 * (orbit.state j).ε ^ 2 ≤
          c0 * (m : ℝ) * (orbit.state j).ε ^ 2 := by
            have hcm : c0 * 1 ≤ c0 * (m : ℝ) :=
              mul_le_mul_of_nonneg_left hmReal hc0.le
            have hmul := mul_le_mul_of_nonneg_right hcm
              (sq_nonneg ((orbit.state j).ε))
            simpa only [mul_one] using hmul
      _ ≤ _ := hamp
  have hradial := Metric.radiusGap_le_dist_add_errors
    (x := orbit.endpoint (2 * j + σ.val))
    (y := orbit.endpoint (2 * ℓ + τ.val)) (center := Clim)
    (radiusX := (orbit.state j).amplitude)
    (radiusY := (orbit.state ℓ).amplitude)
    (errorX := ωR ηω * (orbit.state j).ε ^ 2)
    (errorY := ωR ηω * (orbit.state j).ε ^ 2)
    (gap := c0 * (orbit.state j).ε ^ 2)
    hjR (hℓR.trans hlaterError) hampBase
  have herrorBudget :
      2 * ωR ηω * (orbit.state j).ε ^ 2 ≤
        c0 / 2 * (orbit.state j).ε ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hωηω.le
      (sq_nonneg ((orbit.state j).ε))
    nlinarith
  dsimp only [c]
  linarith

end DFP.TwoPhaseOrbit
