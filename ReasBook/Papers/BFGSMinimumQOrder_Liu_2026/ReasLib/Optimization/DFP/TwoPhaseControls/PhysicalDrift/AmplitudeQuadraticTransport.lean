module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: a quadratic germ transports across an eventual
equality when the destination representative is continuous at the base point. -/
theorem HasQuadraticGerm.congr_of_eventuallyEq
    {f g : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂)
    (hfg : f =ᶠ[𝓝 0] g)
    (hg : ContinuousAt g 0) :
    HasQuadraticGerm g a₀ a₁ a₂ := by
  constructor
  · exact hg
  · apply EqModPow.of_isBigO
    refine hf.eqMod.to_isBigO.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [hfg] with r hr
    rw [hr]

/-- Helper for Appendix Lemma A.6: subtracting the quadratic model turns a
quadratic germ into an explicit third-order remainder germ. -/
theorem HasQuadraticGerm.to_quadraticRemainder
    {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f a₀ a₁ a₂) :
    EqModPow 3
      (fun r ↦ f r - quadraticModel a₀ a₁ a₂ r)
      (fun _ ↦ 0) := by
  have hsub := hf.eqMod.sub (EqModPow.refl 3 (quadraticModel a₀ a₁ a₂))
  apply EqModPow.congr hsub
  · intro r
    rfl
  · intro r
    simp only [quadraticModel]
    ring

/-- Helper for Appendix Lemma A.6: the physical amplitude inherits the quadratic
germ computed from four spectral/gradient component germs. -/
theorem physicalAmplitudeQuadraticGerm_of_componentTransport
    {amplitude sLow sHigh gLow gHigh : ℝ → ℝ}
    {s₁ s₂ t₁ t₂ g₁ g₂ u₁ u₂ : ℝ}
    (hsLow : HasQuadraticGerm sLow 2 s₁ s₂)
    (hsHigh : HasQuadraticGerm sHigh 1 t₁ t₂)
    (hgLow : HasQuadraticGerm gLow 1 g₁ g₂)
    (hgHigh : HasQuadraticGerm gHigh 2 u₁ u₂)
    (hphysical : amplitude =ᶠ[𝓝 0]
      (fun r ↦ sLow r * gLow r / (sHigh r * gHigh r)))
    (hamplitude : ContinuousAt amplitude 0) :
    HasQuadraticGerm amplitude
      1 ((2 * g₁ + s₁ - (u₁ + 2 * t₁)) / 2)
      ((2 * (2 * g₂ + s₁ * g₁ + s₂) - (2 * g₁ + s₁) * (u₁ + 2 * t₁) +
        (u₁ + 2 * t₁) ^ 2 - 2 * (u₂ + t₁ * u₁ + 2 * t₂)) / 4) := by
  have hfactor := recoveryRadiusQuadraticGerm_of_componentGerms
    hsLow hsHigh hgLow hgHigh
  exact hfactor.congr_of_eventuallyEq hphysical.symm hamplitude

/-- Helper for Appendix Lemma A.6: the component transport directly supplies the
explicit third-order amplitude remainder consumed by physical-drift estimates. -/
theorem physicalAmplitudeRemainder_of_componentTransport
    {amplitude sLow sHigh gLow gHigh : ℝ → ℝ}
    {s₁ s₂ t₁ t₂ g₁ g₂ u₁ u₂ : ℝ}
    (hsLow : HasQuadraticGerm sLow 2 s₁ s₂)
    (hsHigh : HasQuadraticGerm sHigh 1 t₁ t₂)
    (hgLow : HasQuadraticGerm gLow 1 g₁ g₂)
    (hgHigh : HasQuadraticGerm gHigh 2 u₁ u₂)
    (hphysical : amplitude =ᶠ[𝓝 0]
      (fun r ↦ sLow r * gLow r / (sHigh r * gHigh r)))
    (hamplitude : ContinuousAt amplitude 0) :
    EqModPow 3
      (fun r ↦ amplitude r -
        quadraticModel 1 ((2 * g₁ + s₁ - (u₁ + 2 * t₁)) / 2)
          ((2 * (2 * g₂ + s₁ * g₁ + s₂) - (2 * g₁ + s₁) * (u₁ + 2 * t₁) +
            (u₁ + 2 * t₁) ^ 2 - 2 * (u₂ + t₁ * u₁ + 2 * t₂)) / 4) r)
      (fun _ ↦ 0) := by
  have hgerm := physicalAmplitudeQuadraticGerm_of_componentTransport
    hsLow hsHigh hgLow hgHigh hphysical hamplitude
  exact hgerm.to_quadraticRemainder

end DFP.TwoLeg.Mixed
