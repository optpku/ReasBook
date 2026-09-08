module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.NearReturnCycleCount
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.ComparableScaleAmplitudeLoss

public section

open Filter
open scoped BigOperators Topology

namespace DFP.TwoPhaseOrbit

/-- A count bound and a uniform pointwise loss bound combine, by telescoping, into
a lower bound for the total loss over a finite interval. -/
private theorem amplitudeGap_of_countBound_and_pointwiseLoss
    (a : ℕ → ℝ) {j ℓ : ℕ} (hjℓ : j ≤ ℓ)
    {x C c r : ℝ} (hC : 0 < C) (hc : 0 ≤ c)
    (hcount : x ≤ ((ℓ - j : ℕ) : ℝ) * C * r ^ 2)
    (hloss : ∀ t ∈ Finset.Ico j ℓ, c * r ^ 4 ≤ a t - a (t + 1)) :
    (c / C) * x * r ^ 2 ≤ a j - a ℓ := by
  have hfactor : 0 ≤ c * r ^ 2 / C :=
    div_nonneg (mul_nonneg hc (sq_nonneg r)) hC.le
  have hmul := mul_le_mul_of_nonneg_left hcount hfactor
  have hscaled :
      (c / C) * x * r ^ 2 ≤ ((ℓ - j : ℕ) : ℝ) * (c * r ^ 4) := by
    calc
      (c / C) * x * r ^ 2 = (c * r ^ 2 / C) * x := by ring
      _ ≤ (c * r ^ 2 / C) * (((ℓ - j : ℕ) : ℝ) * C * r ^ 2) := hmul
      _ = ((ℓ - j : ℕ) : ℝ) * (c * r ^ 4) := by
        field_simp [ne_of_gt hC]
  have hsum :
      ((ℓ - j : ℕ) : ℝ) * (c * r ^ 4) ≤ a j - a ℓ := by
    calc
      ((ℓ - j : ℕ) : ℝ) * (c * r ^ 4) =
          ∑ t ∈ Finset.Ico j ℓ, c * r ^ 4 := by
            simp [Nat.card_Ico, Nat.cast_sub hjℓ]
      _ ≤ ∑ t ∈ Finset.Ico j ℓ, (a t - a (t + 1)) := by
        exact Finset.sum_le_sum fun t ht ↦ hloss t ht
      _ = a j - a ℓ := by
        rw [Finset.sum_Ico_eq_sub _ hjℓ, Finset.sum_range_sub',
          Finset.sum_range_sub']
        ring
  exact hscaled.trans hsum

/-- Comparable-scale cycle endpoints whose lifted angles differ by a positive
number of windings have an amplitude gap bounded below by that winding count
times the squared incoming scale. -/
theorem slowCurveNearReturnAmplitudeGap (p h : ℝ → ℝ)
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
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ c0 > 0,
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
                            c0 * (m : ℝ) * (orbit.state j).ε ^ 2 ≤
                              (orbit.state j).amplitude -
                                (orbit.state ℓ).amplitude := by
  obtain ⟨εbarθ, hεbarθ, Cθ, hCθ, hCycle⟩ :=
    slowCurveNearReturnCycleCountBound p h h_invariant h_pJet h_hJet κ hκ
  obtain ⟨εbarG, hεbarG, cG, hcG, hLoss⟩ :=
    DFP.TwoPhaseOrbit.slowCurveComparableScaleAmplitudeLoss
      p h h_invariant h_pJet h_hJet κ hκ
  obtain ⟨εbarGraph, hεbarGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let εbar := min (min εbarθ εbarG) εbarGraph
  have hεbar_pos : 0 < εbar := by
    exact lt_min (lt_min hεbarθ.1 hεbarG.1) hεbarGraph.1
  have hεbar_lt : εbar < 1 / 4 := by
    exact lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (min_le_left _ _) hεbarθ.2)
  have hεbar_le_θ : εbar ≤ εbarθ := by
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hεbar_le_G : εbar ≤ εbarG := by
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hεbar_le_graph : εbar ≤ εbarGraph := min_le_right _ _
  refine ⟨εbar, ⟨hεbar_pos, hεbar_lt⟩, cG * Real.pi / Cθ, ?_, ?_⟩
  · positivity
  · intro ε₀ hε₀
    dsimp
    have hε₀θ : ε₀ ∈ Set.Ioc (0 : ℝ) εbarθ :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_θ⟩
    have hε₀G : ε₀ ∈ Set.Ioc (0 : ℝ) εbarG :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_G⟩
    have hε₀Graph : ε₀ ∈ Set.Ioc (0 : ℝ) εbarGraph :=
      ⟨hε₀.1, hε₀.2.trans hεbar_le_graph⟩
    let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
    have hcoord (n : ℕ) :
        (orbit.state n).coordinates =
          DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀) := by
      simpa [orbit] using DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ n
    have hεeq (n : ℕ) :
        (orbit.state n).ε =
          (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1 := by
      exact congrArg Prod.fst
        (by simpa [DFP.TwoPhaseOrbit.State.coordinates_def] using hcoord n)
    have hforward (n : ℕ) := hGraph ε₀ hε₀Graph n
    have hεpos (n : ℕ) : 0 < (orbit.state n).ε := by
      rw [hεeq n]
      exact (hforward n).2.1
    have hεle₀ (n : ℕ) : (orbit.state n).ε ≤ ε₀ := by
      rw [hεeq n]
      exact (hforward n).2.2
    intro Clim hClim j ℓ σ τ hjℓ hcomp m ζ hm hangle hζ
    let N := ℓ - j
    have hjℓle : j ≤ ℓ := Nat.le_of_lt hjℓ
    have hNpos : 0 < N := Nat.sub_pos_of_lt hjℓ
    have hjN : j + N = ℓ := by
      simpa [N] using Nat.add_sub_of_le hjℓle
    have hCycleBound :
        2 * Real.pi * (m : ℝ) - (orbit.state j).ε ^ 2 / 4 ≤
          (N : ℝ) * Cθ * (orbit.state j).ε ^ 2 := by
      exact hCycle ε₀ hε₀θ Clim hClim j N σ τ hNpos
        (by simpa only [hjN] using hcomp) m ζ
        (by simpa only [hjN] using hangle) hζ
    have hεj_lt_one : (orbit.state j).ε < 1 := by
      calc
        (orbit.state j).ε ≤ ε₀ := hεle₀ j
        _ ≤ εbar := hε₀.2
        _ < 1 / 4 := hεbar_lt
        _ < 1 := by norm_num
    have hquarter_le_pi_m :
        (orbit.state j).ε ^ 2 / 4 ≤ Real.pi * (m : ℝ) := by
      have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hεjSq : (orbit.state j).ε ^ 2 < 1 := by nlinarith [hεpos j]
      have hpi_m : (2 : ℝ) ≤ Real.pi * (m : ℝ) := by
        have hmul := mul_le_mul Real.two_le_pi hmReal
          (by norm_num : (0 : ℝ) ≤ 1) Real.pi_pos.le
        nlinarith
      nlinarith
    have hcount :
        Real.pi * (m : ℝ) ≤ (N : ℝ) * Cθ * (orbit.state j).ε ^ 2 := by
      have hle : Real.pi * (m : ℝ) ≤
          2 * Real.pi * (m : ℝ) - (orbit.state j).ε ^ 2 / 4 := by
        linarith
      exact hle.trans hCycleBound
    have hperStep (t : ℕ) (ht : t ∈ Finset.Ico j ℓ) :
        cG * (orbit.state j).ε ^ 4 ≤
          (orbit.state t).amplitude - (orbit.state (t + 1)).amplitude := by
      exact hLoss ε₀ hε₀G j ℓ t (Finset.mem_Ico.mp ht).1
        (Finset.mem_Ico.mp ht).2 hcomp
    have hgap := amplitudeGap_of_countBound_and_pointwiseLoss
      (a := fun n ↦ (orbit.state n).amplitude) hjℓle hCθ hcG.le
      (by simpa only [N] using hcount) hperStep
    calc
      (cG * Real.pi / Cθ) * (m : ℝ) * (orbit.state j).ε ^ 2 =
          (cG / Cθ) * (Real.pi * (m : ℝ)) * (orbit.state j).ε ^ 2 := by ring
      _ ≤ (orbit.state j).amplitude - (orbit.state ℓ).amplitude := hgap

end DFP.TwoPhaseOrbit
