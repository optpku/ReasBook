module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

open DFP.TwoLeg.Mixed

/-- Infrastructure I.16a: the canceled FirstLeg spectral factors agree with the independent-radius
factors after the mixed-path parameter substitution `p ↦ 2 + p ε ^ 3` and
`h ↦ 1 + h ε ^ 3`. -/
theorem firstLeg_spectralFactors_eq_independentRadiusFirstSpectral_on_mixedPath
    (ε p h : ℝ) :
    DFP.FirstLeg.spectralFactors ε (2 + p * ε ^ 3) (1 + h * ε ^ 3) =
      independentRadiusFirstSpectral ((ε, p, h), ε ^ 2) := by
  unfold DFP.FirstLeg.spectralFactors independentRadiusFirstSpectral
  dsimp [independentRadiusFirstResiduals, independentRadiusFirstMetricTriple,
    independentFirstResiduals]
  convert rfl using 1
  all_goals ring

/-- Infrastructure I.16a: the canceled FirstLeg gradient factors agree with the independent-radius
factors after the same mixed-path parameter substitution. -/
theorem firstLeg_gradientFactors_eq_independentRadiusFirstGradient_on_mixedPath
    (ε p h : ℝ) :
    DFP.FirstLeg.gradientFactors ε (2 + p * ε ^ 3) (1 + h * ε ^ 3) =
      independentRadiusFirstGradient ((ε, p, h), ε ^ 2) := by
  unfold DFP.FirstLeg.gradientFactors independentRadiusFirstGradient
  dsimp [independentRadiusFirstResiduals, independentFirstResiduals,
    independentRadiusFirstGradientResiduals, independentFirstGradientResiduals,
    independentRadiusFirstMetricTriple]
  convert rfl using 1
  all_goals ring

/-- Infrastructure I.16a: the spectral-factor identity is packaged as an equality of the two
mixed-path functions, so it can be transported through germ and derivative interfaces. -/
theorem firstLeg_spectralFactors_mixedPath_eq
    (p h : ℝ) :
    (fun ε : ℝ ↦ DFP.FirstLeg.spectralFactors ε (2 + p * ε ^ 3) (1 + h * ε ^ 3)) =
      (fun ε : ℝ ↦ independentRadiusFirstSpectral ((ε, p, h), ε ^ 2)) := by
  funext ε
  exact firstLeg_spectralFactors_eq_independentRadiusFirstSpectral_on_mixedPath ε p h

/-- Infrastructure I.16a: the gradient-factor identity is packaged as an equality of the two
mixed-path functions, so it can be consumed without reopening their residual formulas. -/
theorem firstLeg_gradientFactors_mixedPath_eq
    (p h : ℝ) :
    (fun ε : ℝ ↦ DFP.FirstLeg.gradientFactors ε (2 + p * ε ^ 3) (1 + h * ε ^ 3)) =
      (fun ε : ℝ ↦ independentRadiusFirstGradient ((ε, p, h), ε ^ 2)) := by
  funext ε
  exact firstLeg_gradientFactors_eq_independentRadiusFirstGradient_on_mixedPath ε p h

end DFP.SecondLeg
