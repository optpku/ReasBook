module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleStationarityNeighborhood
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseScaleTaylorCertificate
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ScaleStationarityNeighborhood
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseScaleTaylorCertificate

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

/-- Helper for Infrastructure I.16a companion: an eventual vanishing of the normalized second
scale coefficient of the transverse derivative family gives the bundled second
scale jet required by the finite Taylor estimate. -/
theorem lowGradientTransverseFDerivFamily_secondScaleJet_of_scalarCoefficient
    (hsecondCoefficient : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      (FiniteTaylorJet.ofFunction ℝ 2
        (lowGradientTransverseFDerivFamily z) 0).scalarCoeff (2 : Fin 3) = 0) :
    ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      iteratedFDeriv ℝ 2 (lowGradientTransverseFDerivFamily z) 0 = 0 := by
  filter_upwards [hsecondCoefficient] with z hz
  exact FiniteTaylorJet.iteratedFDeriv_eq_zero_of_scalarCoeff_eq_zero hz

/-- Infrastructure I.16a companion: the single source-side normalized second
scale coefficient identity, together with the stationarity bridge, supplies the
uniform cubic transverse derivative bound. -/
theorem lowGradientFactorTransverseFDeriv_norm_bound_of_secondScaleCoefficient
    (hsecondCoefficient : ∀ᶠ z : ℝ × ℝ in 𝓝 ((2, 1) : ℝ × ℝ),
      (FiniteTaylorJet.ofFunction ℝ 2
        (lowGradientTransverseFDerivFamily z) 0).scalarCoeff (2 : Fin 3) = 0) :
    ∃ C > 0, ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      ‖fderiv ℝ (fun z : ℝ × ℝ ↦
        (gradientFactors x.1 z.1 z.2).1) (x.2.1, x.2.2)‖ ≤
        C * ‖x.1 ^ (3 : ℕ)‖ := by
  exact lowGradientFactorTransverseFDeriv_norm_bound_of_secondScaleJet
    (lowGradientTransverseFDerivFamily_secondScaleJet_of_scalarCoefficient
      hsecondCoefficient)

end DFP.SecondLeg
