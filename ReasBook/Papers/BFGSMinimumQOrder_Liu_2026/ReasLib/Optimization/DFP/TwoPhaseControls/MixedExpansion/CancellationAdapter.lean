module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- A joint eventual equality with the independent-radius
    normal form transports three already-certified truncated coefficient germs to the
    removable mixed map. -/
theorem mixedIndependentRadiusCancellation_of_normalFormGerms
    {K : Set (ℝ × ℝ × ℝ)}
    (hmap : ∀ θ, θ ∈ K →
      Function.uncurry (fun η r ↦ map η.1 (input η r)) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry independentRadiusNormalForm))
    (hRadius : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (independentRadiusNormalForm θ r).1) K 3
      (fun n θ ↦ (![0, 1,
        θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n))
    (hShape : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (independentRadiusNormalForm θ r).2.1) K 2
      (fun n θ ↦ (![2,
        θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n))
    (hScale : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (independentRadiusNormalForm θ r).2.2) K 2
      (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n)) :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).1) K 3
        (fun n θ ↦ (![0, 1,
          θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).2.1) K 2
        (fun n θ ↦ (![2,
          θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (map θ.1 (input θ r)).2.2) K 2
        (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n) := by
  have hmapRadius : ∀ θ, θ ∈ K →
      Function.uncurry (fun η r ↦ (map η.1 (input η r)).1) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry (fun η r ↦ (independentRadiusNormalForm η r).1)) := by
    intro θ hθ
    filter_upwards [hmap θ hθ] with z hz
    exact congrArg Prod.fst hz
  have hmapShape : ∀ θ, θ ∈ K →
      Function.uncurry (fun η r ↦ (map η.1 (input η r)).2.1) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry (fun η r ↦ (independentRadiusNormalForm η r).2.1)) := by
    intro θ hθ
    filter_upwards [hmap θ hθ] with z hz
    exact congrArg (fun q : ℝ × ℝ × ℝ ↦ q.2.1) hz
  have hmapScale : ∀ θ, θ ∈ K →
      Function.uncurry (fun η r ↦ (map η.1 (input η r)).2.2) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry (fun η r ↦ (independentRadiusNormalForm η r).2.2)) := by
    intro θ hθ
    filter_upwards [hmap θ hθ] with z hz
    exact congrArg (fun q : ℝ × ℝ × ℝ ↦ q.2.2) hz
  refine ⟨?_, ?_, ?_⟩
  · apply independentRadiusTruncatedGerm_of_eventuallyEq
      (hregular := hmapRadius) (hscalar := ?_) hRadius
    intro θ hθ
    have hconst : Tendsto (fun _ : ℝ ↦ θ) (𝓝 0) (𝓝 θ) := tendsto_const_nhds
    have hpair0 := hconst.prodMk tendsto_id
    have hfun : (fun x : ℝ ↦ (θ, id x)) = (fun r : ℝ ↦ (θ, r)) := by
      funext r
      rfl
    rw [hfun] at hpair0
    have hpair : Tendsto (fun r : ℝ ↦ (θ, r)) (𝓝 0) (𝓝 (θ, 0)) :=
      by simpa only [nhds_prod_eq] using hpair0
    have hpath := (hmapRadius θ hθ).comp_tendsto hpair
    filter_upwards [hpath] with r hr
    change (map θ.1 (input θ r)).1 =
      (independentRadiusNormalForm θ r).1 at hr
    exact hr
  · apply independentRadiusTruncatedGerm_of_eventuallyEq
      (hregular := hmapShape) (hscalar := ?_) hShape
    intro θ hθ
    have hconst : Tendsto (fun _ : ℝ ↦ θ) (𝓝 0) (𝓝 θ) := tendsto_const_nhds
    have hpair0 := hconst.prodMk tendsto_id
    have hfun : (fun x : ℝ ↦ (θ, id x)) = (fun r : ℝ ↦ (θ, r)) := by
      funext r
      rfl
    rw [hfun] at hpair0
    have hpair : Tendsto (fun r : ℝ ↦ (θ, r)) (𝓝 0) (𝓝 (θ, 0)) :=
      by simpa only [nhds_prod_eq] using hpair0
    have hpath := (hmapShape θ hθ).comp_tendsto hpair
    filter_upwards [hpath] with r hr
    change (map θ.1 (input θ r)).2.1 =
      (independentRadiusNormalForm θ r).2.1 at hr
    exact hr
  · apply independentRadiusTruncatedGerm_of_eventuallyEq
      (hregular := hmapScale) (hscalar := ?_) hScale
    intro θ hθ
    have hconst : Tendsto (fun _ : ℝ ↦ θ) (𝓝 0) (𝓝 θ) := tendsto_const_nhds
    have hpair0 := hconst.prodMk tendsto_id
    have hfun : (fun x : ℝ ↦ (θ, id x)) = (fun r : ℝ ↦ (θ, r)) := by
      funext r
      rfl
    rw [hfun] at hpair0
    have hpair : Tendsto (fun r : ℝ ↦ (θ, r)) (𝓝 0) (𝓝 (θ, 0)) :=
      by simpa only [nhds_prod_eq] using hpair0
    have hpath := (hmapScale θ hθ).comp_tendsto hpair
    filter_upwards [hpath] with r hr
    change (map θ.1 (input θ r)).2.2 =
      (independentRadiusNormalForm θ r).2.2 at hr
    exact hr

/-- Helper for Infrastructure I.16a: compact normal-form germs and their local cancellation
produce positive uniform remainder constants for all three actual mixed-map coordinates. -/
theorem mixedIndependentRadiusCancellation_uniformRemainders_of_normalFormGerms
    {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K)
    (hmap : ∀ θ, θ ∈ K →
      Function.uncurry (fun η r ↦ map η.1 (input η r)) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry independentRadiusNormalForm))
    (hRadius : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (independentRadiusNormalForm θ r).1) K 3
      (fun n θ ↦ (![0, 1,
        θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n))
    (hShape : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (independentRadiusNormalForm θ r).2.1) K 2
      (fun n θ ↦ (![2,
        θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n))
    (hScale : IndependentRadiusTruncatedGerm
      (fun θ r ↦ (independentRadiusNormalForm θ r).2.2) K 2
      (fun n θ ↦ (![1, 8 * θ.1] : Fin 2 → ℝ) n)) :
    (∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ (map θ.1 (input θ r)).1 -
        ∑ n : Fin 3,
          (![0, 1, θ.1 * (6 * θ.2.2 + 5 * θ.2.1 - 300) / 18] : Fin 3 → ℝ) n *
            r ^ (n : ℕ)) K C 3) ∧
    (∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ (map θ.1 (input θ r)).2.1 -
        ∑ n : Fin 2,
          (![2, θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9] : Fin 2 → ℝ) n *
            r ^ (n : ℕ)) K C 2) ∧
    (∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ (map θ.1 (input θ r)).2.2 -
        ∑ n : Fin 2, (![1, 8 * θ.1] : Fin 2 → ℝ) n * r ^ (n : ℕ)) K C 2) := by
  have hthree : (0 : ℕ) < 3 := by
    norm_num
  have htwo : (0 : ℕ) < 2 := by
    norm_num
  obtain ⟨hRadiusMap, hShapeMap, hScaleMap⟩ :=
    mixedIndependentRadiusCancellation_of_normalFormGerms
      hmap hRadius hShape hScale
  obtain ⟨Cr, hCr, hRadiusRemainder⟩ :=
    uniformRemainderOn_of_independentRadiusTruncatedGerm hthree hK hRadiusMap
  obtain ⟨Cs, hCs, hShapeRemainder⟩ :=
    uniformRemainderOn_of_independentRadiusTruncatedGerm htwo hK hShapeMap
  obtain ⟨Cscale, hCscale, hScaleRemainder⟩ :=
    uniformRemainderOn_of_independentRadiusTruncatedGerm htwo hK hScaleMap
  refine ⟨⟨Cr, hCr, hRadiusRemainder⟩, ?_⟩
  exact ⟨⟨Cs, hCs, hShapeRemainder⟩, ⟨Cscale, hCscale, hScaleRemainder⟩⟩

end DFP.TwoLeg.Mixed
