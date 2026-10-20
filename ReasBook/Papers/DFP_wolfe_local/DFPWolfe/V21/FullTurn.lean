/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import DFPWolfe.V21.SequenceProperties
public import ReasLib.Optimization.DFP.Polar.PointGeometry

/-!
# Complete turns of the actual polar Wolfe counterexample

The complete-turn parameter neighborhood is intersected with the objective and
sequence neighborhoods before selecting the cycle parameter. Consequently the
source distance expansion and the other sequence comparisons hold for one
canonical Wolfe witness, with constants fixed before every later start.
-/

public section

open DFP.Polar

namespace DFPWolfe.V21

namespace FullTurn

/-- Helper for lem:polar-geometry: the source distance expansion between
successive complete turns, at the original cubic endpoint indices. -/
def distanceEstimate (ν : ℝ) (j₀ : ℕ)
    (point : ℕ → EuclideanSpace ℝ (Fin 2)) (K : ℝ) : Prop :=
  ∀ N : ℕ, 0 < N → j₀ ≤ N ^ 3 →
    |‖point (2 * (N ^ 3 - j₀)) - point (2 * ((N + 1) ^ 3 - j₀))‖ -
        3 * (RadiusExpansions.radiusCoefficient ν 0 +
          RadiusExpansions.radiusCoefficient ν 1) / ((N : ℝ) * (N + 1))| ≤
      K * (N : ℝ) ^ (-3 : ℤ)

/-- Helper for lem:polar-geometry: exact source identities transfer the
complete-turn estimate to the canonical objective's own point sequence. -/
theorem distanceEstimateOfSourceIdentity {ν κ c₁ c₂ K : ℝ} {j₀ : ℕ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : PlanarCounterexample.SourceIdentity (Parameters.of j₀ ν) κ w)
    (hturn : distanceEstimate ν j₀ (Parameters.of j₀ ν).point K) :
    distanceEstimate ν j₀ w.iteration.point K := by
  rw [h.point]
  exact hturn

end FullTurn

/-- Helper for lem:polar-geometry and sec:known-results: one canonical strong
Wolfe counterexample has the full source sequence comparisons AND the exact
complete-turn distance expansion. The cycle parameter, support scale and all
comparison constants are fixed before every accuracy and later starting index. -/
theorem planarCounterexampleFamilyWithFullTurn (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∃ Cgrad > 0, ∃ lower > 0, ∃ upper > 0,
      ∃ productLower > 0, ∃ productUpper > 0, ∃ Kturn > 0,
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
          PlanarCounterexample.SourceIdentity (Parameters.of j₀ νStar) κ w ∧
          PlanarCounterexample.CounterexampleProperties ε w ∧
          SequenceProperties.SourceEstimates (Parameters.of j₀ νStar) νStar
            Cgrad lower upper productLower productUpper ∧
          FullTurn.distanceEstimate νStar j₀ w.iteration.point Kturn := by
  obtain ⟨ηs, hηs, hsourceData⟩ := PlanarCounterexample.sourceDataNeighborhood
  obtain ⟨ηq, hηq, hsequenceData⟩ := SequenceProperties.sourceSequenceNeighborhood
  obtain ⟨ηt, hηt, hturnData⟩ := PointGeometry.polarPointFullTurn
  obtain ⟨νStar, hνStar, _, Jw, _, hmodels⟩ :=
    WolfeRatios.existsUniformModelWolfe c₁ c₂ (min ηs (min ηq ηt))
      hc₁ hc₁lim hc₂lim hc₂ (lt_min hηs (lt_min hηq hηt))
  have hnearSource : νStar ∈ Set.Ioo baseAngle (baseAngle + ηs) :=
    Set.Ioo_subset_Ioo_right
      (add_le_add le_rfl (min_le_left ηs (min ηq ηt))) hνStar
  have hnearSequence : νStar ∈ Set.Ioo baseAngle (baseAngle + ηq) :=
    Set.Ioo_subset_Ioo_right
      (add_le_add le_rfl ((min_le_right ηs (min ηq ηt)).trans (min_le_left ηq ηt))) hνStar
  have hnearTurn : νStar ∈ Set.Ioo baseAngle (baseAngle + ηt) :=
    Set.Ioo_subset_Ioo_right
      (add_le_add le_rfl ((min_le_right ηs (min ηq ηt)).trans (min_le_right ηq ηt))) hνStar
  obtain ⟨κ, hκ, C, _, H, hH, haccuracy⟩ := hsourceData νStar hnearSource
  obtain ⟨Cgrad, hCgrad, lower, hlower, upper, hupper, productLower, hProductLower,
    productUpper, hProductUpper, Jq, _, hsequences⟩ := hsequenceData νStar hnearSequence
  obtain ⟨Kturn, hKturn, Jt, _, hturns⟩ := hturnData νStar hnearTurn
  refine ⟨νStar, hνStar.1, κ, hκ, Cgrad, hCgrad, lower, hlower, upper, hupper,
    productLower, hProductLower, productUpper, hProductUpper, Kturn, hKturn, ?_⟩
  intro ε hε _
  let δ := min ε (1 / 2)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
  have hδ : 0 < δ := lt_min hε hhalf
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hδone : δ < 1 := hδhalf.trans_lt hhalfOne
  obtain ⟨Js, hJs, hsource⟩ := haccuracy δ hδ hδone
  refine ⟨max Js (max Jw (max Jq Jt)), hJs.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  have hjSource : Js ≤ j₀ := (le_max_left _ _).trans hj₀
  have hjWolfe : Jw ≤ j₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans hj₀
  have hjSequence : Jq ≤ j₀ :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hj₀
  have hjTurn : Jt ≤ j₀ :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hj₀
  have hactual := hsource j₀ hjSource
  have hwolfe := SequenceProperties.strongWolfeOfSourceModel hactual.objective
    hc₁ (hc₁lim.trans_le hc₂lim) hc₂ (hmodels j₀ hjWolfe)
  obtain ⟨w, hidentity, hproperties⟩ :=
    PlanarCounterexample.certificateOfSourceData hactual hδhalf hδε hH.le hwolfe
  have hturn : FullTurn.distanceEstimate νStar j₀ (Parameters.of j₀ νStar).point Kturn :=
    hturns j₀ hjTurn
  exact ⟨w, hidentity, hproperties, hsequences j₀ hjSequence,
    FullTurn.distanceEstimateOfSourceIdentity hidentity hturn⟩

end DFPWolfe.V21
