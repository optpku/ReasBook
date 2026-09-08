module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Analyticity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicConcrete
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.TransverseCubicConcrete
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.SecondLeg

/-!
# Analytic interfaces for the transverse low-gradient quotient

The rational definition of the low gradient factor is kept behind the frame-coordinate
interface.  This file exposes only the analytic numerator/denominator data and the local
nonvanishing certificate needed by the cubic derivative adapters.
-/

/-- Helper for Lemma 4.15: the three independent output-metric entries used by the low chart. -/
private def transverseMetricEntries (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (outputMetric x.1 x.2.1 x.2.2 0 0,
    outputMetric x.1 x.2.1 x.2.2 0 1,
    outputMetric x.1 x.2.1 x.2.2 1 1)

/-- Helper for Lemma 4.15: the metric-entry triple is analytic at `(0, 2, 1)`. -/
private lemma transverseMetricEntries_analyticAt :
    AnalyticAt ℝ transverseMetricEntries (0, 2, 1) := by
  exact (outputMetricEntry_analyticAt 0 0).prod
    ((outputMetricEntry_analyticAt 0 1).prod
      (outputMetricEntry_analyticAt 1 1))

/-- Helper for Lemma 4.15: the metric-entry triple has the diagonal base value `(0, 0, 1)`. -/
private lemma transverseMetricEntries_base :
    transverseMetricEntries (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
  have hspectral : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradient : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  norm_num [transverseMetricEntries, outputMetric, hspectral, hgradient]

/-- Helper for Lemma 4.15: an analytic metric triple at the diagonal base has analytic low
eigenvalue. -/
private lemma analyticAt_low_of_transverseMetricEntries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {m : E → ℝ × ℝ × ℝ}
    (hm : AnalyticAt ℝ m x) (hm0 : m x = (0, 0, 1)) :
    AnalyticAt ℝ (fun y ↦ RealSymmetric2.low (m y).1
      (m y).2.1 (m y).2.2) x := by
  have houter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  have houter' : AnalyticAt ℝ
      (fun p ↦ RealSymmetric2.low p.1 p.2.1 p.2.2) (m x) := by
    rw [hm0]
    exact houter
  simpa only [Function.comp_def] using houter'.comp (f := m) hm

/-- Helper for Lemma 4.15: the low-eigenvector normalization denominator is analytic after an
analytic metric triple is based at `(0, 0, 1)`. -/
private lemma analyticAt_lowDenom_of_transverseMetricEntries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} {m : E → ℝ × ℝ × ℝ}
    (hm : AnalyticAt ℝ m x) (hm0 : m x = (0, 0, 1)) :
    AnalyticAt ℝ (fun y ↦ RealSymmetric2.lowDenom (m y).1
      (m y).2.1 (m y).2.2) x := by
  have hlow := analyticAt_low_of_transverseMetricEntries hm hm0
  have hd : AnalyticAt ℝ (fun y ↦ (m y).2.2) x :=
    analyticAt_snd.comp (analyticAt_snd.comp hm)
  have hfirst : AnalyticAt ℝ (fun y ↦ (m y).2.2 -
      RealSymmetric2.low (m y).1 (m y).2.1 (m y).2.2) x := hd.sub hlow
  have hb : AnalyticAt ℝ (fun y ↦ (m y).2.1) x :=
    analyticAt_fst.comp (analyticAt_snd.comp hm)
  let rad : E → ℝ := fun y ↦
    ((m y).2.2 - RealSymmetric2.low (m y).1 (m y).2.1 (m y).2.2) ^ 2 +
      (m y).2.1 ^ 2
  have hrad : AnalyticAt ℝ rad x := by
    exact (hfirst.pow 2).add (hb.pow 2)
  have hrad0 : 0 < rad x := by
    dsimp [rad]
    rw [hm0]
    norm_num [RealSymmetric2.low, RealSymmetric2.gap]
  have hsqrtAt : AnalyticAt ℝ Real.sqrt (rad x) := by
    have hformula : AnalyticAt ℝ
        (fun t : ℝ ↦ NormedSpace.exp (Real.log t * (1 / 2 : ℝ))) (rad x) :=
      (NormedSpace.exp_analytic _).comp ((analyticAt_log hrad0).mul analyticAt_const)
    apply hformula.congr
    filter_upwards [eventually_gt_nhds hrad0] with t ht
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht, Real.exp_eq_exp_ℝ]
  have hsqrt := hsqrtAt.comp (f := rad) hrad
  have hden : AnalyticAt ℝ (fun y ↦ RealSymmetric2.lowDenom
      (m y).1 (m y).2.1 (m y).2.2) x := by
    apply hsqrt.congr
    filter_upwards [] with y
    simp only [rad, RealSymmetric2.lowDenom]
    rfl
  exact hden

/-- Lemma 4.15 companion: the transverse quotient denominator is analytic at the canceled base. -/
theorem lowGradientTransverseDenominator_analyticAt :
    AnalyticAt ℝ lowGradientTransverseDenominator (0, 2, 1) := by
  have hmetric := transverseMetricEntries_analyticAt
  have hbase := transverseMetricEntries_base
  have hden := analyticAt_lowDenom_of_transverseMetricEntries hmetric hbase
  apply hden.congr
  filter_upwards [] with x
  rfl

/-- Lemma 4.15 companion: the transverse quotient numerator is analytic at the canceled base. -/
theorem lowGradientTransverseNumerator_analyticAt :
    AnalyticAt ℝ lowGradientTransverseNumerator (0, 2, 1) := by
  have hmetric := transverseMetricEntries_analyticAt
  have hbase := transverseMetricEntries_base
  have hlow := analyticAt_low_of_transverseMetricEntries hmetric hbase
  have h00 := outputMetricEntry_analyticAt 0 0
  have h01 := outputMetricEntry_analyticAt 0 1
  have h11 := outputMetricEntry_analyticAt 1 1
  have hg0 := outputGradientEntry_analyticAt 0
  have hg1 := outputGradientEntry_analyticAt 1
  have hleft := (h11.sub hlow).mul hg0
  have hright := h01.mul hg1
  have hnumerator := hleft.sub hright
  apply hnumerator.congr
  filter_upwards [] with x
  rfl

/-- Lemma 4.15 companion: the transverse quotient denominator has value one at `(0, 2, 1)`. -/
theorem lowGradientTransverseDenominator_base :
    lowGradientTransverseDenominator (0, 2, 1) = 1 := by
  have hbase := transverseMetricEntries_base
  have hproject := congrArg
    (fun m : ℝ × ℝ × ℝ ↦ RealSymmetric2.lowDenom m.1 m.2.1 m.2.2) hbase
  have hdiag : RealSymmetric2.lowDenom 0 0 1 = 1 := by
    norm_num [RealSymmetric2.lowDenom, RealSymmetric2.low, RealSymmetric2.gap]
  have hproject' : RealSymmetric2.lowDenom
      (transverseMetricEntries (0, 2, 1)).1
      (transverseMetricEntries (0, 2, 1)).2.1
      (transverseMetricEntries (0, 2, 1)).2.2 = 1 := hproject.trans hdiag
  simpa only [transverseMetricEntries, lowGradientTransverseDenominator] using hproject'

/-- Lemma 4.15 companion: the transverse quotient denominator is nonzero on a neighborhood of
the canceled base. -/
theorem eventually_lowGradientTransverseDenominator_ne_zero :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      lowGradientTransverseDenominator x ≠ 0 := by
  have hone : (1 : ℝ) ≠ 0 := one_ne_zero
  apply lowGradientTransverseDenominator_analyticAt.continuousAt.eventually_ne
  simpa only [lowGradientTransverseDenominator_base] using hone

end DFP.SecondLeg
