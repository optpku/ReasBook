module

public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.CoordinateReduction
public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Analyticity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Analyticity
import all ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.CoordinateReduction
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Analyticity
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Analyticity

/-!
# Base-neighborhood reduction of the second endpoint angle

This file discharges the local chart, orientation, and positivity conditions needed
by `secondEndpointAngleIncrement_toReal_eq_arctan_sub_of_localData` near `(0, 2, 1)`.
-/

public section

noncomputable section

open Filter
open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg

/-- Near the canceled base state, the second endpoint angle is exactly the difference
of the final and intermediate first-frame slope arctangents. -/
theorem secondEndpointAngleIncrement_toReal_eq_arctan_sub_eventually :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (observableMap x).secondEndpointAngleIncrement.toReal =
        Real.arctan
            (DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2 1 /
              DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2 0) -
          Real.arctan
            (x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2 /
              (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1) := by
  have hleft := (DFP.FirstLeg.outputMetricEntry_analyticAt 0 0).continuousAt
  have hright := (DFP.FirstLeg.outputMetricEntry_analyticAt 1 1).continuousAt
  have hdiff : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
        DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0) (0, 2, 1) :=
    hright.sub hleft
  have hchart : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0 <
        DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 := by
    have hbase :
        DFP.FirstLeg.outputMetric 0 2 1 1 1 -
          DFP.FirstLeg.outputMetric 0 2 1 0 0 = 1 := by
      norm_num [DFP.FirstLeg.outputMetric]
    have hpos : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
        0 < DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
          DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0 := by
      apply hdiff.eventually
      change Set.Ioi 0 ∈ 𝓝
        (DFP.FirstLeg.outputMetric 0 2 1 1 1 -
          DFP.FirstLeg.outputMetric 0 2 1 0 0)
      rw [hbase]
      exact Ioi_mem_nhds zero_lt_one
    simpa only [sub_pos] using hpos
  have hgradientAnalytic : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
    apply ((analyticAt_fst.comp analyticAt_snd).comp
      DFP.FirstLeg.factorsAnalytic).congr
    filter_upwards [] with x
    rfl
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hQ : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1 := by
    have hc := (analyticAt_fst.comp hgradientAnalytic).continuousAt
    apply hc.eventually
    change Set.Ioi 0 ∈ 𝓝 (DFP.FirstLeg.gradientFactors 0 2 1).1
    rw [hgradientBase]
    exact Ioi_mem_nhds (by norm_num)
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hRbase : DFP.SecondLeg.outputGradient 0 2 1 0 = 1 := by
    norm_num [DFP.SecondLeg.outputGradient, hspectralBase, hgradientBase]
  have hR : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < DFP.SecondLeg.outputGradient x.1 x.2.1 x.2.2 0 := by
    have hc := (DFP.SecondLeg.outputGradientEntry_analyticAt 0).continuousAt
    apply hc.eventually
    change Set.Ioi 0 ∈ 𝓝 (DFP.SecondLeg.outputGradient 0 2 1 0)
    rw [hRbase]
    exact Ioi_mem_nhds (by norm_num)
  filter_upwards [hchart, hQ, hR, DFP.FirstLeg.gradientFactorization]
    with x hxchart hxQ hxR hxgrad
  have hxgrad' : (DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
      DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 =
        ![(DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1,
          x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2] := by
    simpa using hxgrad 1
  simpa using secondEndpointAngleIncrement_toReal_eq_arctan_sub_of_localData
    x.1 x.2.1 x.2.2 hxchart hxQ hxR hxgrad'

end DFP.TwoLeg
