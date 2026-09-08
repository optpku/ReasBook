module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This file is the parent-independent assembly layer for the second-gradient low
coordinate.  It accepts the raw-to-normal-form equality as a certificate and
therefore does not unfold the physical observable map.
-/

/-- Helper for Appendix Lemma A.6: an uncurried eventual equality specializes to
    an eventual equality on every fixed-parameter radius path. -/
theorem scalarFamily_eventuallyEq_of_uncurry_radius
    {K : Set (ℝ × ℝ × ℝ)}
    {f g : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hmap : ∀ θ, θ ∈ K →
      Function.uncurry f =ᶠ[𝓝 (θ, 0)] Function.uncurry g) :
    ∀ θ, θ ∈ K → f θ =ᶠ[𝓝 0] g θ := by
  intro θ hθ
  have hconst : Tendsto (fun _ : ℝ ↦ θ) (𝓝 0) (𝓝 θ) := tendsto_const_nhds
  have hpair0 := hconst.prodMk tendsto_id
  have hfun : (fun x : ℝ ↦ (θ, id x)) = (fun r : ℝ ↦ (θ, r)) := by
    funext r
    rfl
  rw [hfun] at hpair0
  have hpair : Tendsto (fun r : ℝ ↦ (θ, r)) (𝓝 0) (𝓝 (θ, 0)) := by
    simpa only [nhds_prod_eq] using hpair0
  have hpath := (hmap θ hθ).comp_tendsto hpair
  filter_upwards [hpath] with r hr
  change f θ r = g θ r at hr
  exact hr

/-- Helper for Appendix Lemma A.6: the normalized second-gradient low coordinate
    carries its exact three-term coefficient germ on an arbitrary parameter set. -/
theorem independentRadiusSecondGradientLow_truncatedGerm_generic
    {K : Set (ℝ × ℝ × ℝ)} :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (independentRadiusSecondGradient (θ, r)).1) K 3
      (fun n θ ↦
        (![1, 0,
          (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) := by
  have hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3
        (Function.uncurry
          (fun η r ↦ (independentRadiusSecondGradient (η, r)).1)) (θ, 0) := by
    intro θ hθ
    have hanalytic := independentRadiusSecondGradient_analyticAt θ
    have hlow := analyticAt_fst.comp hanalytic
    have huncurry :
        Function.uncurry
            (fun η r ↦ (independentRadiusSecondGradient (η, r)).1) =
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
            (independentRadiusSecondGradient z).1) := by
      funext z
      rfl
    rw [huncurry]
    exact hlow.contDiffAt
  have hgerm : ∀ θ, θ ∈ K →
      HasQuadraticGerm
        (fun r ↦ (independentRadiusSecondGradient (θ, r)).1)
        1 0 ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18) := by
    intro θ hθ
    exact independentRadiusSecondGradientLow_quadraticGerm θ
  exact independentRadiusTruncatedGerm_of_quadraticGerms hregular hgerm

/-- Appendix Lemma A.6: any scalar family with a certified uncurried equality to
    the normalized second-gradient low coordinate inherits its exact amplitude
    coefficient germ. -/
theorem truncatedGerm_of_uncurryEq_secondGradientLow
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {K : Set (ℝ × ℝ × ℝ)}
    (hmap : ∀ θ, θ ∈ K →
      Function.uncurry f =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry
          (fun η r ↦ (independentRadiusSecondGradient (η, r)).1))) :
    IndependentRadiusTruncatedGerm f K 3
      (fun n θ ↦
        (![1, 0,
          (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) := by
  have hlow := independentRadiusSecondGradientLow_truncatedGerm_generic (K := K)
  have hscalar := scalarFamily_eventuallyEq_of_uncurry_radius hmap
  exact independentRadiusTruncatedGerm_of_eventuallyEq hmap hscalar hlow

end DFP.TwoLeg.Mixed
