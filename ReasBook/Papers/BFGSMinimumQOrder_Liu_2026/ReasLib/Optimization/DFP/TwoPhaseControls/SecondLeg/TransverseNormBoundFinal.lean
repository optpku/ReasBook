module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleStationarity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleJetCertificate
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleStationarityNeighborhood
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleStationarity
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.SecondScaleJetCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleStationarityNeighborhood

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-!
# Unconditional uniform cubic bound for the transverse derivative of the low second-leg
# gradient factor

This leaf module discharges Claim 2 of Lemma 4.15 unconditionally, using the verified
`SecondScaleStationarity` results (the crux `𝒢₂ = 1 + O(ε³)` and its promotion to the scalar
second-scale stationarity of the transverse derivative family).  It lives outside `SecondLeg.lean`
(which is imported *by* the certificate chain) to avoid an import cycle.

The final integrator replaces the stub `SecondLeg.lean:975` with
`lowGradientFactorTransverseFDeriv_norm_bound_final` (re-exported under the canonical name once the
stub is removed).
-/

/-- Helper for Lemma 4.15: the verified unconditional scalar second-scale stationarity packages into
the source-side certificate. -/
theorem lowGradientTransverseSecondScaleCertificate_final :
    LowGradientTransverseSecondScaleCertificate where
  scalar_second := lowGradientTransverseFDerivFamily_scalar_secondScale_eventually

/-- Helper for Lemma 4.15: the eventual bundled second scale jet of the transverse derivative family
vanishes near the positive transverse base point (unconditional). -/
theorem lowGradientTransverseFDerivFamily_secondScaleJet_eventually_zero_final :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0 :=
  lowGradientTransverseSecondScaleCertificate_final.eventually_secondScaleJet

/-- Lemma 4.15 (Near-return winding number is nonzero), Claim 2: the transverse
Fréchet derivative of the low second-leg gradient factor is uniformly `O(ε³)` near the canceled base
point.  Canonical declaration site (the former `SecondLeg.lean` stub was removed to break the import
cycle: `SecondLeg.lean` is imported by this certificate chain). -/
theorem lowGradientFactorTransverseFDeriv_norm_bound :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦ (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖
        ≤ C * ‖x.1 ^ (3 : ℕ)‖ :=
  lowGradientFactorTransverseFDeriv_norm_bound_of_secondScaleJet
    lowGradientTransverseFDerivFamily_secondScaleJet_eventually_zero_final

end DFP.SecondLeg
