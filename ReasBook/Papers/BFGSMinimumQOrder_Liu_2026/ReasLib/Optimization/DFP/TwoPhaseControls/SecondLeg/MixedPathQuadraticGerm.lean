module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ResidualDataChartGerm
public import
  ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientScaleSubstitution
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.FirstLegFactorTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeQuadraticTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.ResidualDataChartGerm
import all
  ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientScaleSubstitution
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.FirstLegFactorTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeQuadraticTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.SecondLeg

open DFP.TwoLeg.Mixed

/-- Infrastructure I.16a: along the canonical mixed parameter path, the removable low
gradient factor is the independent-radius second-gradient low coordinate. -/
theorem lowGradientFactor_eq_independentRadiusSecondGradient_on_mixedPath
    (ε p h : ℝ) :
    lowGradientFactor (ε, 2 + p * ε ^ 3, 1 + h * ε ^ 3) =
      (independentRadiusSecondGradient ((ε, p, h), ε ^ 2)).1 := by
  rw [lowGradientFactor_eq_independentSecondGradientFactors]
  rw [firstLeg_spectralFactors_eq_independentRadiusFirstSpectral_on_mixedPath,
    firstLeg_gradientFactors_eq_independentRadiusFirstGradient_on_mixedPath]
  rfl

/-- Infrastructure I.16a: the mixed-path low-gradient factor has the flat quadratic germ
provided by the independent-radius second-gradient calculation. -/
theorem lowGradientFactor_mixedPath_quadraticGerm (p h : ℝ) :
    HasQuadraticGerm
      (fun ε : ℝ ↦ lowGradientFactor (ε, 2 + p * ε ^ 3, 1 + h * ε ^ 3))
      1 0 0 := by
  have hIndependent := independentRadiusSecondGradientLow_scale_quadraticGerm p h
  have hpath : ContinuousAt
      (fun ε : ℝ ↦ (ε, 2 + p * ε ^ 3, 1 + h * ε ^ 3))
      (0 : ℝ) := by
    fun_prop
  have hcontinuous : ContinuousAt
      (fun ε : ℝ ↦ lowGradientFactor (ε, 2 + p * ε ^ 3, 1 + h * ε ^ 3))
      (0 : ℝ) := by
    have hbase : ContinuousAt lowGradientFactor
        ((0, 2, 1) : ℝ × ℝ × ℝ) :=
      lowGradientFactor_analyticAt.continuousAt
    have hpath_base :
        (0, 2 + p * (0 : ℝ) ^ 3, 1 + h * (0 : ℝ) ^ 3) =
          ((0, 2, 1) : ℝ × ℝ × ℝ) := by
      norm_num
    have hcomp := hbase.comp_of_eq hpath hpath_base
    simpa only [Function.comp_def] using hcomp
  have hfg :
      (fun ε : ℝ ↦ (independentRadiusSecondGradient ((ε, p, h), ε ^ 2)).1) =ᶠ[𝓝 0]
        (fun ε : ℝ ↦ lowGradientFactor (ε, 2 + p * ε ^ 3, 1 + h * ε ^ 3)) := by
    filter_upwards [] with ε
    exact (lowGradientFactor_eq_independentRadiusSecondGradient_on_mixedPath ε p h).symm
  exact hIndependent.congr_of_eventuallyEq hfg hcontinuous

/-- Infrastructure I.16a: the mixed-path flat quadratic germ gives a vanishing second
scale derivative after the path is given its analytic regularity. -/
theorem lowGradientFactor_mixedPath_iteratedDeriv_two_eq_zero (p h : ℝ) :
    iteratedDeriv 2
      (fun ε : ℝ ↦ lowGradientFactor (ε, 2 + p * ε ^ 3, 1 + h * ε ^ 3)) 0 = 0 := by
  have hgerm := lowGradientFactor_mixedPath_quadraticGerm p h
  have hpath : ContDiffAt ℝ 3
      (fun ε : ℝ ↦ (ε, 2 + p * ε ^ 3, 1 + h * ε ^ 3)) 0 := by
    fun_prop
  have hbase : ContDiffAt ℝ 3 lowGradientFactor
      ((0, 2, 1) : ℝ × ℝ × ℝ) :=
    lowGradientFactor_analyticAt.contDiffAt
  have hpath_base :
      (0, 2 + p * (0 : ℝ) ^ 3, 1 + h * (0 : ℝ) ^ 3) =
        ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    norm_num
  have hbase' : ContDiffAt ℝ 3 lowGradientFactor
      (0, 2 + p * (0 : ℝ) ^ 3, 1 + h * (0 : ℝ) ^ 3) := by
    rw [hpath_base]
    exact hbase
  have hcomp := hbase'.comp 0 hpath
  have hregular : ContDiffAt ℝ 3
      (fun ε : ℝ ↦ lowGradientFactor (ε, 2 + p * ε ^ 3, 1 + h * ε ^ 3)) 0 := by
    simpa only [Function.comp_def] using hcomp
  have hderiv := HasQuadraticGerm.iteratedDeriv_two_eq_of_contDiffAt hgerm hregular
  simpa using hderiv

end DFP.SecondLeg
