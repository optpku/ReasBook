module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusDerivatives
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusDerivatives

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- A derivative of a product-valued path transports to
    its first coordinate through the canonical one-dimensional derivative map. -/
lemma hasDerivAt_fst_of_prod
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {f : ℝ → α × β} {f' : α × β} {x : ℝ}
    (h : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (f t).1) f'.1 x := by
  simpa [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply] using h.hasFDerivAt.fst.hasDerivAt

/-- A derivative of a product-valued path transports to
    its second coordinate through the canonical one-dimensional derivative map. -/
lemma hasDerivAt_snd_of_prod
    {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {f : ℝ → α × β} {f' : α × β} {x : ℝ}
    (h : HasDerivAt f f' x) :
    HasDerivAt (fun t ↦ (f t).2) f'.2 x := by
  simpa [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply] using h.hasFDerivAt.snd.hasDerivAt

/-- An explicit factorization with the corrected second-leg
    spectral jet transports to `independentRadiusSecondSpectral`. -/
theorem independentRadiusSecondSpectral_hasDerivAt_of_factorization
    (θ : ℝ × ℝ × ℝ) (F : ℝ → ℝ × ℝ)
    (hF : HasDerivAt F
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12), 8 * θ.1) 0)
    (hEq : ∀ r : ℝ, F r = independentRadiusSecondSpectral (θ, r)) :
    HasDerivAt (fun r ↦ independentRadiusSecondSpectral (θ, r))
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 12), 8 * θ.1) 0 := by
  apply hF.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun r ↦ (hEq r).symm)

/-- An explicit factorization with the corrected `+12`
    second-leg gradient jet transports to `independentRadiusSecondGradient`. -/
theorem independentRadiusSecondGradient_hasDerivAt_of_factorization
    (θ : ℝ × ℝ × ℝ) (F : ℝ → ℝ × ℝ)
    (hF : HasDerivAt F
      (0, 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0)
    (hEq : ∀ r : ℝ, F r = independentRadiusSecondGradient (θ, r)) :
    HasDerivAt (fun r ↦ independentRadiusSecondGradient (θ, r))
      (0, 4 * θ.1 * (3 * θ.2.2 + θ.2.1 + 12) / 9) 0 := by
  apply hF.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun r ↦ (hEq r).symm)

end DFP.TwoLeg.Mixed
