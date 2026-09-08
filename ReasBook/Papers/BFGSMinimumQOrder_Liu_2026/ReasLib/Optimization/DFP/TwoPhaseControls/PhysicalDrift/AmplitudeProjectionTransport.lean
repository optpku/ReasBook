module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion isolates the final physical-amplitude projection boundary.  The
physical observable is first identified with the independent raw evaluator by the
existing pointwise projection theorem.  A later frame-coordinate certificate can
then identify that raw evaluator with the normalized second-gradient coordinate.
-/

/-- Helper for Appendix Lemma A.6: along the canonical mixed input, the physical
    amplitude equals the independent raw evaluator's final low coordinate. -/
theorem physicalAmplitude_eq_mixedIndependentRawAmplitude_input
    (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    (observableMap θ.1 (input θ r)).amplitudeRatio =
      mixedIndependentRawAmplitude θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) := by
  simpa only [input] using
    mixedObservable_amplitude_eq_independentRaw θ.1 r
      (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)

/-- Helper for Appendix Lemma A.6: an eventual raw-to-normalized low-coordinate
    equality transports the physical amplitude to that normalized coordinate. -/
theorem physicalAmplitude_eventuallyEq_secondGradientLow_of_rawCertificate
    {K : Set (ℝ × ℝ × ℝ)}
    (hraw : ∀ θ, θ ∈ K →
      (fun r ↦ mixedIndependentRawAmplitude θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) =ᶠ[𝓝 0]
        (fun r ↦ (independentRadiusSecondGradient (θ, r)).1)) :
    ∀ θ, θ ∈ K →
      (fun r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio) =ᶠ[𝓝 0]
        (fun r ↦ (independentRadiusSecondGradient (θ, r)).1) := by
  intro θ hθ
  have hpointwise : ∀ r : ℝ,
      (observableMap θ.1 (input θ r)).amplitudeRatio =
        mixedIndependentRawAmplitude θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) := by
    intro r
    exact physicalAmplitude_eq_mixedIndependentRawAmplitude_input θ r
  have hphysical :
      (fun r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio) =ᶠ[𝓝 0]
        (fun r ↦ mixedIndependentRawAmplitude θ.1 r
          (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)) :=
    Filter.Eventually.of_forall hpointwise
  exact hphysical.trans (hraw θ hθ)

/-- Helper for Appendix Lemma A.6: a product-filter raw-coordinate certificate
    gives the uncurried physical-amplitude equality used by germ transport. -/
theorem physicalAmplitude_uncurry_eventuallyEq_secondGradientLow_of_rawCertificate
    {K : Set (ℝ × ℝ × ℝ)}
    (hraw : ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ mixedIndependentRawAmplitude η.1 r
            (2 + η.2.1 * η.1 * r) (1 + η.2.2 * η.1 * r)) =ᶠ[𝓝 (θ, 0)]
        Function.uncurry
          (fun η r ↦ (independentRadiusSecondGradient (η, r)).1)) :
    ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).amplitudeRatio) =ᶠ[𝓝 (θ, 0)]
        Function.uncurry
          (fun η r ↦ (independentRadiusSecondGradient (η, r)).1) := by
  intro θ hθ
  have hpointwise : ∀ z : (ℝ × ℝ × ℝ) × ℝ,
      (observableMap z.1.1 (input z.1 z.2)).amplitudeRatio =
        mixedIndependentRawAmplitude z.1.1 z.2
          (2 + z.1.2.1 * z.1.1 * z.2) (1 + z.1.2.2 * z.1.1 * z.2) := by
    intro z
    exact physicalAmplitude_eq_mixedIndependentRawAmplitude_input z.1 z.2
  have hphysical :
      Function.uncurry
          (fun η r ↦ (observableMap η.1 (input η r)).amplitudeRatio) =ᶠ[𝓝 (θ, 0)]
        Function.uncurry
          (fun η r ↦ mixedIndependentRawAmplitude η.1 r
            (2 + η.2.1 * η.1 * r) (1 + η.2.2 * η.1 * r)) :=
    Filter.Eventually.of_forall hpointwise
  exact hphysical.trans (hraw θ hθ)

end DFP.TwoLeg.Mixed
