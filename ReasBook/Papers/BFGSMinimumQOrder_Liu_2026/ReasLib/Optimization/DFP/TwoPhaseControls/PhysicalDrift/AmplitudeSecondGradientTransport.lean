module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeProjectionTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeProjectionTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondQuadraticGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This file assembles the completed second-gradient quadratic germ with the
physical projection transport.  The raw frame-coordinate certificate remains
an explicit input, so the assembly does not assert an unproved observable
identity.
-/

/-- Helper for Appendix Lemma A.6: the normalized second-gradient low coordinate
    has a compact-uniform quadratic germ on any parameter set. -/
theorem independentRadiusSecondGradientLow_truncatedGerm
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

/-- Appendix Lemma A.6: a raw-to-normalized second-gradient certificate yields
    the physical amplitude coefficient germ, with the exact displayed quadratic
    coefficient and no additional frame assumptions hidden in the conclusion. -/
theorem physicalAmplitudeTruncatedGerm_of_secondGradientLow_rawCertificate
    {K : Set (ℝ × ℝ × ℝ)}
    (hraw : ∀ θ, θ ∈ K →
      Function.uncurry
          (fun η r ↦ mixedIndependentRawAmplitude η.1 r
            (2 + η.2.1 * η.1 * r) (1 + η.2.2 * η.1 * r)) =ᶠ[𝓝 (θ, 0)]
        Function.uncurry
          (fun η r ↦ (independentRadiusSecondGradient (η, r)).1)) :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio) K 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) := by
  have hphysical :=
    physicalAmplitude_uncurry_eventuallyEq_secondGradientLow_of_rawCertificate hraw
  have hlow := independentRadiusSecondGradientLow_truncatedGerm (K := K)
  simpa only using
    (amplitudeGerm_of_uncurry_eventuallyEq hphysical hlow)

end DFP.TwoLeg.Mixed
