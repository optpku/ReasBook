module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
The physical-drift wrapper needs to transport scalar observable germs from a removable
normal form.  The bridge below isolates the only topological plumbing involved: an
uncurry equality at `(θ, 0)` specializes to an equality of radius paths at `θ`.
-/

/-- Helper for Appendix Lemma A.6: an eventual equality of uncurried scalar families
    specializes to an eventual equality along the fixed-parameter radius path. -/
theorem scalarFamily_eventuallyEq_of_uncurry
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

/-- Helper for Appendix Lemma A.6: an uncurried normal-form equality transports any
    scalar truncated radius germ to the concrete mixed observable family. -/
theorem observableScalarGerm_of_uncurry_eventuallyEq
    {K : Set (ℝ × ℝ × ℝ)}
    {f g : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {m : ℕ} {coeff : Fin m → (ℝ × ℝ × ℝ) → ℝ}
    (hmap : ∀ θ, θ ∈ K →
      Function.uncurry f =ᶠ[𝓝 (θ, 0)] Function.uncurry g)
    (hGerm : IndependentRadiusTruncatedGerm g K m coeff) :
    IndependentRadiusTruncatedGerm f K m coeff := by
  exact independentRadiusTruncatedGerm_of_eventuallyEq hmap
    (scalarFamily_eventuallyEq_of_uncurry hmap) hGerm

/-- Helper for Appendix Lemma A.6: the amplitude projection inherits a normal-form
    truncated germ from an uncurried neighborhood equality. -/
theorem amplitudeGerm_of_uncurry_eventuallyEq
    {K : Set (ℝ × ℝ × ℝ)}
    {g : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {coeff : Fin 3 → (ℝ × ℝ × ℝ) → ℝ}
    (hmap : ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).amplitudeRatio) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry g))
    (hGerm : IndependentRadiusTruncatedGerm g K 3 coeff) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio) K 3 coeff := by
  exact observableScalarGerm_of_uncurry_eventuallyEq hmap hGerm

/-- Helper for Appendix Lemma A.6: the frame-angle projection inherits a normal-form
    truncated germ from an uncurried neighborhood equality. -/
theorem frameAngleGerm_of_uncurry_eventuallyEq
    {K : Set (ℝ × ℝ × ℝ)}
    {g : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {coeff : Fin 2 → (ℝ × ℝ × ℝ) → ℝ}
    (hmap : ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).frameAngleIncrement) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry g))
    (hGerm : IndependentRadiusTruncatedGerm g K 2 coeff) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement) K 2 coeff := by
  exact observableScalarGerm_of_uncurry_eventuallyEq hmap hGerm

/-- Helper for Appendix Lemma A.6: paired amplitude and frame-angle projection
    certificates transport their two normal-form truncated germs simultaneously. -/
theorem pairedObservableGerms_of_uncurry_eventuallyEq
    {K : Set (ℝ × ℝ × ℝ)}
    {amplitudeNormalForm angleNormalForm : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    {amplitudeCoeff : Fin 3 → (ℝ × ℝ × ℝ) → ℝ}
    {angleCoeff : Fin 2 → (ℝ × ℝ × ℝ) → ℝ}
    (hamplitude : ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).amplitudeRatio) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry amplitudeNormalForm))
    (hangle : ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).frameAngleIncrement) =ᶠ[𝓝 (θ, 0)]
        (Function.uncurry angleNormalForm))
    (hamplitudeGerm : IndependentRadiusTruncatedGerm amplitudeNormalForm K 3 amplitudeCoeff)
    (hangleGerm : IndependentRadiusTruncatedGerm angleNormalForm K 2 angleCoeff) :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio) K 3 amplitudeCoeff ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement) K 2 angleCoeff := by
  constructor
  · exact amplitudeGerm_of_uncurry_eventuallyEq hamplitude hamplitudeGerm
  · exact frameAngleGerm_of_uncurry_eventuallyEq hangle hangleGerm

end DFP.TwoLeg.Mixed
